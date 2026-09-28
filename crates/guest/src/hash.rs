//! Unkeyed BLAKE2s-256 (RFC 7693), using the compression ECALL on RV64.

pub const IV: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];
pub const BLOCK_LEN: usize = 64;
pub const OUT_LEN: usize = 32;
pub const PARAM_IV: [u32; 8] = {
    let mut h = IV;
    h[0] ^= 0x0101_0020;
    h
};

/// Absorb one block into `chaining` with the exact 64-bit byte counter and
/// both 32-bit flags. Sequential hashing uses f0 = u32::MAX for its final
/// block and f1 = 0. This low-level API also preserves arbitrary flag words.
/// The chaining buffer is used as both ECALL input and output: the machine
/// must snapshot all inputs before performing the output writes.
pub fn blake2s_compress(chaining: &mut [u32; 8], message: &[u8; 64], counter: u64, f0: u32, f1: u32) {
    #[cfg(target_arch = "riscv64")]
    {
        #[repr(C)]
        struct Metadata {
            counter: u64,
            f0: u32,
            f1: u32,
        }
        let metadata = Metadata { counter, f0, f1 };
        let chaining_ptr = chaining.as_mut_ptr() as usize;
        // SAFETY: little-endian RV64 has the ABI's exact layouts, and each
        // buffer remains live with the required size. The shared chaining
        // input/output address intentionally exercises allowed overlap.
        let status = unsafe {
            crate::ecall(
                crate::ECALL_BLAKE2S,
                message.as_ptr() as usize,
                chaining_ptr,
                core::ptr::from_ref(&metadata) as usize,
                chaining_ptr,
            )
        };
        assert_eq!(status, 0, "BLAKE2s compression failed");
    }
    #[cfg(not(target_arch = "riscv64"))]
    software_compress(chaining, message, counter, f0, f1);
}

#[cfg(not(target_arch = "riscv64"))]
fn software_compress(h: &mut [u32; 8], block: &[u8; 64], counter: u64, f0: u32, f1: u32) {
    const SIGMA: [[usize; 16]; 10] = [
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
        [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
        [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
        [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
        [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
        [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
        [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
        [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
        [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
        [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
    ];
    const LANES: [[usize; 4]; 8] = [
        [0, 4, 8, 12],
        [1, 5, 9, 13],
        [2, 6, 10, 14],
        [3, 7, 11, 15],
        [0, 5, 10, 15],
        [1, 6, 11, 12],
        [2, 7, 8, 13],
        [3, 4, 9, 14],
    ];
    let message: [u32; 16] = core::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= counter as u32;
    v[13] ^= (counter >> 32) as u32;
    v[14] ^= f0;
    v[15] ^= f1;
    for schedule in SIGMA {
        for (g, [a, b, c, d]) in LANES.into_iter().enumerate() {
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(message[schedule[g * 2]]);
            v[d] = (v[d] ^ v[a]).rotate_right(16);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(12);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(message[schedule[g * 2 + 1]]);
            v[d] = (v[d] ^ v[a]).rotate_right(8);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(7);
        }
    }
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

/// Streaming unkeyed BLAKE2s-256. A full final block is held until more input
/// arrives, so exact multiples of 64 never gain a spurious empty final block.
#[derive(Clone)]
pub struct Hasher {
    chaining: [u32; 8],
    buffer: [u8; BLOCK_LEN],
    buffered: usize,
    counter: u64,
}

impl Hasher {
    pub const fn new() -> Self {
        Self {
            chaining: PARAM_IV,
            buffer: [0; BLOCK_LEN],
            buffered: 0,
            counter: 0,
        }
    }

    pub fn update(&mut self, mut input: &[u8]) -> &mut Self {
        while !input.is_empty() {
            if self.buffered == BLOCK_LEN {
                self.counter = self
                    .counter
                    .checked_add(BLOCK_LEN as u64)
                    .expect("BLAKE2s byte counter overflow");
                blake2s_compress(&mut self.chaining, &self.buffer, self.counter, 0, 0);
                self.buffered = 0;
            }
            if self.buffered == 0 && input.len() > BLOCK_LEN {
                self.counter = self
                    .counter
                    .checked_add(BLOCK_LEN as u64)
                    .expect("BLAKE2s byte counter overflow");
                let (block, rest) = input.split_at(BLOCK_LEN);
                blake2s_compress(&mut self.chaining, block.try_into().unwrap(), self.counter, 0, 0);
                input = rest;
                continue;
            }
            let count = (BLOCK_LEN - self.buffered).min(input.len());
            self.buffer[self.buffered..self.buffered + count].copy_from_slice(&input[..count]);
            self.buffered += count;
            input = &input[count..];
        }
        self
    }

    /// Return the digest without consuming or altering the streaming state.
    pub fn finalize(&self) -> [u8; OUT_LEN] {
        let mut chaining = self.chaining;
        let mut block = self.buffer;
        block[self.buffered..].fill(0);
        let counter = self
            .counter
            .checked_add(self.buffered as u64)
            .expect("BLAKE2s byte counter overflow");
        blake2s_compress(&mut chaining, &block, counter, u32::MAX, 0);
        let mut digest = [0; OUT_LEN];
        for (bytes, word) in digest.chunks_exact_mut(4).zip(chaining) {
            bytes.copy_from_slice(&word.to_le_bytes());
        }
        digest
    }
}

impl Default for Hasher {
    fn default() -> Self {
        Self::new()
    }
}

pub fn hash(input: &[u8]) -> [u8; OUT_LEN] {
    Hasher::new().update(input).finalize()
}

#[cfg(test)]
mod tests {
    use super::{Hasher, hash};

    fn digest(hex: &str) -> [u8; 32] {
        core::array::from_fn(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap())
    }

    #[test]
    fn rfc7693_empty_and_abc() {
        assert_eq!(
            hash(b""),
            digest("69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9")
        );
        assert_eq!(
            hash(b"abc"),
            digest("508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982")
        );
    }

    #[test]
    fn final_block_is_preserved_across_stream_updates() {
        // BLAKE2 reference KATs: message byte i is i, unkeyed digest size 32.
        let input: [u8; 65] = core::array::from_fn(|i| i as u8);
        let mut state = Hasher::new();
        state.update(&input[..64]);
        state.update(&[]);
        assert_eq!(
            state.finalize(),
            digest("56f34e8b96557e90c1f24b52d0c89d51086acf1b00f634cf1dde9233b8eaaa3e")
        );
        state.update(&input[64..]);
        assert_eq!(
            state.finalize(),
            digest("1b53ee94aaf34e4b159d48de352c7f0661d0a40edff95a0b1639b4090e974472")
        );
        for split in [1, 31, 63] {
            let mut other = Hasher::new();
            other.update(&input[..split]);
            other.update(&input[split..]);
            assert_eq!(other.finalize(), state.finalize());
        }
    }

    #[test]
    fn direct_blocks_preserve_partial_updates_and_finalization() {
        let input: [u8; 257] = core::array::from_fn(|i| i as u8);
        let mut state = Hasher::new();
        state.update(&input[..63]);
        state.update(&input[63..256]);
        assert_eq!(
            state.finalize(),
            digest("5fdeb59f681d975f52c8e69c5502e02a12a3afcc5836ba58f42784c439228781")
        );
        state.update(&input[256..]);
        let expected = digest("7795ecf74355f1bdc9ee5818c357081b6a51b8dd801be35b1a872391014edeae");
        assert_eq!(state.finalize(), expected);
        assert_eq!(hash(&input), expected);
    }
}
