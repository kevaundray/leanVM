use crate::Error;
use alloc::vec::Vec;

pub const RAM_END: u64 = 1u64 << 32;

#[derive(Clone, Debug)]
pub struct Segment {
    address: u64,
    memory_size: u64,
    flags: u32,
    bytes: Vec<u8>,
}

impl Segment {
    pub fn address(&self) -> u64 {
        self.address
    }
    pub fn memory_size(&self) -> u64 {
        self.memory_size
    }
    pub fn flags(&self) -> u32 {
        self.flags
    }
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub fn readable(&self) -> bool {
        self.flags & 4 != 0
    }
    pub fn writable(&self) -> bool {
        self.flags & 2 != 0
    }
    pub fn executable(&self) -> bool {
        self.flags & 1 != 0
    }
}

#[derive(Clone, Debug)]
pub struct ProgramInfo {
    entry: u64,
    segments: Vec<Segment>,
    digest: [u8; 32],
}

impl ProgramInfo {
    pub fn entry(&self) -> u64 {
        self.entry
    }
    pub fn segments(&self) -> &[Segment] {
        &self.segments
    }
    pub fn program_digest(&self) -> [u8; 32] {
        self.digest
    }

    /// Canonical ROM: initial bytes at even keys, executable words at odd keys.
    pub fn rom_entries(&self) -> Vec<(u64, u64)> {
        let segments: Vec<_> = self
            .segments
            .iter()
            .filter(|segment| segment.memory_size != 0)
            .collect();
        let mut words = Vec::new();
        let mut previous_pc = None;
        for segment in &segments {
            if !segment.executable() || segment.bytes.is_empty() {
                continue;
            }
            let file_end = segment.address + segment.bytes.len() as u64;
            for pc in ((segment.address & !3)..file_end).step_by(4) {
                if previous_pc == Some(pc) {
                    continue;
                }
                previous_pc = Some(pc);
                let mut word = 0u64;
                let mut executable = true;
                for offset in 0..4 {
                    let address = pc + offset;
                    let index = segments.partition_point(|segment| segment.address <= address);
                    let Some(source) = index.checked_sub(1).map(|index| segments[index]) else {
                        executable = false;
                        break;
                    };
                    let relative = address - source.address;
                    if !source.executable() || relative >= source.memory_size {
                        executable = false;
                        break;
                    }
                    word |= u64::from(source.bytes.get(relative as usize).copied().unwrap_or(0)) << (8 * offset);
                }
                if executable {
                    words.push(((pc << 1) | 1, word));
                }
            }
        }
        let byte_count: usize = segments.iter().map(|segment| segment.bytes.len()).sum();
        let mut entries = Vec::with_capacity(byte_count + words.len());
        let mut words = words.into_iter().peekable();
        for segment in &segments {
            for (offset, &byte) in segment.bytes.iter().enumerate() {
                let key = (segment.address + offset as u64) << 1;
                while words.peek().is_some_and(|&(word_key, _)| word_key < key) {
                    entries.push(words.next().unwrap());
                }
                entries.push((key, byte as u64));
            }
        }
        entries.extend(words);
        entries
    }

    pub fn from_elf(elf: &[u8]) -> Result<Self, Error> {
        if elf.len() < 64 || &elf[..4] != b"\x7fELF" || elf[4..7] != [2, 1, 1] {
            return Err(Error::InvalidProgram);
        }
        let u16_at = |i| u16::from_le_bytes(elf[i..i + 2].try_into().unwrap());
        let u32_at = |i| u32::from_le_bytes(elf[i..i + 4].try_into().unwrap());
        let u64_at = |i| u64::from_le_bytes(elf[i..i + 8].try_into().unwrap());
        let entry = u64_at(24);
        if u16_at(16) != 2
            || u16_at(18) != 243
            || u32_at(20) != 1
            || u32_at(48) != 0
            || u16_at(52) != 64
            || u16_at(54) != 56
            || entry & 3 != 0
        {
            return Err(Error::InvalidProgram);
        }
        let phoff = u64_at(32);
        let phnum = u16_at(56) as u64;
        let end = phoff.checked_add(phnum * 56).ok_or(Error::InvalidProgram)?;
        if phnum == 0 || phnum == 0xffff || phoff < 64 || end > elf.len() as u64 {
            return Err(Error::InvalidProgram);
        }
        let mut segments = Vec::new();
        for index in 0..phnum {
            let p = (phoff + index * 56) as usize;
            let kind = u32_at(p);
            if kind == 2 || kind == 3 {
                return Err(Error::InvalidProgram);
            }
            if kind != 1 {
                continue;
            }
            let flags = u32_at(p + 4);
            let offset = u64_at(p + 8);
            let address = u64_at(p + 16);
            let file_size = u64_at(p + 32);
            let memory_size = u64_at(p + 40);
            let alignment = u64_at(p + 48);
            let file_end = offset.checked_add(file_size).ok_or(Error::InvalidProgram)?;
            let memory_end = address.checked_add(memory_size).ok_or(Error::InvalidProgram)?;
            if flags & !7 != 0
                || flags & 3 == 3
                || file_size > memory_size
                || file_end > elf.len() as u64
                || address >= RAM_END
                || memory_end > RAM_END
                || (alignment > 1 && (!alignment.is_power_of_two() || address % alignment != offset % alignment))
            {
                return Err(Error::InvalidProgram);
            }
            segments.push(Segment {
                address,
                memory_size,
                flags,
                bytes: elf[offset as usize..file_end as usize].to_vec(),
            });
        }
        segments.sort_by_key(|segment| segment.address);
        let mut previous_end = 0;
        for segment in &segments {
            if segment.memory_size == 0 {
                continue;
            }
            if segment.address < previous_end {
                return Err(Error::InvalidProgram);
            }
            previous_end = segment.address + segment.memory_size;
        }
        if !(0..4).all(|offset| {
            segments.iter().any(|segment| {
                let address = entry.wrapping_add(offset);
                segment.executable() && address >= segment.address && address - segment.address < segment.memory_size
            })
        }) {
            return Err(Error::InvalidProgram);
        }
        Ok(Self {
            entry,
            segments,
            digest: leanvm_guest::hash(elf),
        })
    }

    pub fn iv(&self) -> [u8; 32] {
        let mut hash = leanvm_guest::Hasher::new();
        hash.update(b"leanvm/rv64im/proof/v1");
        hash.update(&self.digest);
        hash.update(&[
            0x53, 0x7a, 0xd2, 0x07, 0x90, 0x30, 0x8f, 0x8e, 0xb8, 0xc0, 0xe8, 0xbd, 0x3e, 0x6c, 0x58, 0xee, 0x64, 0x57,
            0x33, 0x71, 0xe3, 0xd5, 0x3c, 0x30, 0x61, 0x3d, 0xd0, 0x4d, 0x87, 0xc0, 0xb7, 0xea,
        ]);
        hash.finalize()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn program(segments: &[(u64, u64, u32, &[u8])]) -> ProgramInfo {
        let mut elf = vec![0u8; 64 + segments.len() * 56];
        elf[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
        for (at, value) in [(16, 2u16), (18, 243), (52, 64), (54, 56), (56, segments.len() as u16)] {
            elf[at..at + 2].copy_from_slice(&value.to_le_bytes());
        }
        elf[20..24].copy_from_slice(&1u32.to_le_bytes());
        elf[24..32].copy_from_slice(&0x1000u64.to_le_bytes());
        elf[32..40].copy_from_slice(&64u64.to_le_bytes());
        for (index, &(address, memory_size, flags, bytes)) in segments.iter().enumerate() {
            let p = 64 + index * 56;
            let offset = elf.len() as u64;
            elf[p..p + 4].copy_from_slice(&1u32.to_le_bytes());
            elf[p + 4..p + 8].copy_from_slice(&flags.to_le_bytes());
            for (at, value) in [
                (8, offset),
                (16, address),
                (32, bytes.len() as u64),
                (40, memory_size),
                (48, 1),
            ] {
                elf[p + at..p + at + 8].copy_from_slice(&value.to_le_bytes());
            }
            elf.extend_from_slice(bytes);
        }
        ProgramInfo::from_elf(&elf).unwrap()
    }

    #[test]
    fn executable_words_cross_segments_and_partial_bss_without_expanding_bss() {
        let program = program(&[
            (0x1000, 4, 5, &[0x13]),
            (0x2000, 3, 5, &[0x13]),
            (0x2001, 0, 4, &[]),
            (0x2003, 5, 5, &[0, 0x73]),
            (0x2008, 4, 4, &[0x13]),
            (0x200c, RAM_END - 0x200c, 5, &[]),
        ]);
        let entries = program.rom_entries();
        let words: Vec<_> = entries.iter().copied().filter(|&(key, _)| key & 1 != 0).collect();
        assert_eq!(words, vec![(0x2001, 0x13), (0x4001, 0x13), (0x4009, 0x73)]);
        assert!(entries.windows(2).all(|pair| pair[0].0 < pair[1].0));
        assert_eq!(entries.len(), 8);
    }

    #[test]
    fn a_nonexecutable_or_unmapped_byte_excludes_the_entire_word() {
        for (address, flags) in [(0x2003, 4), (0x2004, 5)] {
            let program = program(&[
                (0x1000, 4, 5, &[0x13]),
                (0x2000, 3, 5, &[0x13]),
                (address, 4, flags, &[0]),
            ]);
            let entries = program.rom_entries();
            assert!(!entries.iter().any(|&(key, _)| key == 0x4001));
            assert!(entries.contains(&(0x4000, 0x13)));
        }
    }
}
