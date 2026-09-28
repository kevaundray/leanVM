use crate::{AccessKind, Error, ErrorKind, MemorySnapshot, RAM_END};
use std::sync::Arc;

/// Immutable PT_LOAD description. File bytes are followed by zero-filled BSS.
#[derive(Clone, Debug)]
pub struct Segment {
    address: u64,
    memory_size: u64,
    flags: u32,
    alignment: u64,
    file_offset: u64,
    file_size: u64,
    image: Arc<[u8]>,
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
    pub fn alignment(&self) -> u64 {
        self.alignment
    }
    pub fn file_offset(&self) -> u64 {
        self.file_offset
    }
    pub fn bytes(&self) -> &[u8] {
        &self.image[self.file_offset as usize..(self.file_offset + self.file_size) as usize]
    }
    pub fn executable(&self) -> bool {
        self.flags & 1 != 0
    }
    pub fn writable(&self) -> bool {
        self.flags & 2 != 0
    }
    pub fn readable(&self) -> bool {
        self.flags & 4 != 0
    }
    pub(crate) fn contains(&self, address: u64) -> bool {
        address >= self.address && address - self.address < self.memory_size
    }
}

#[derive(Clone, Debug)]
pub struct Program {
    entry: u64,
    segments: Vec<Segment>,
    initial: MemorySnapshot,
    image: Arc<[u8]>,
}

impl Program {
    pub fn entry(&self) -> u64 {
        self.entry
    }
    /// Sorted by virtual address; no overlapping nonempty ranges.
    pub fn segments(&self) -> &[Segment] {
        &self.segments
    }
    pub fn initial_memory(&self) -> &MemorySnapshot {
        &self.initial
    }
    /// Exact original ELF, including non-loaded bytes, for statement binding.
    pub fn elf_bytes(&self) -> &[u8] {
        &self.image
    }

    pub fn from_elf(elf: &[u8]) -> Result<Self, Error> {
        let mut pc = 0;
        let fail = |pc, why| Error {
            pc,
            kind: ErrorKind::InvalidElf(why),
        };
        if elf.len() < 64 {
            return Err(fail(pc, "truncated ELF header"));
        }
        if &elf[..4] != b"\x7fELF" || elf[4] != 2 || elf[5] != 1 || elf[6] != 1 {
            return Err(fail(pc, "expected ELF64 little-endian version 1"));
        }
        let u16_at = |i| u16::from_le_bytes(elf[i..i + 2].try_into().unwrap());
        let u32_at = |i| u32::from_le_bytes(elf[i..i + 4].try_into().unwrap());
        let u64_at = |i| u64::from_le_bytes(elf[i..i + 8].try_into().unwrap());
        pc = u64_at(24);
        if u16_at(16) != 2 || u16_at(18) != 243 || u32_at(20) != 1 {
            return Err(fail(pc, "expected RISC-V ET_EXEC version 1"));
        }
        if u32_at(48) != 0 {
            return Err(fail(pc, "unsupported RISC-V ELF flags (requires soft-float RV64IM)"));
        }
        if u16_at(52) != 64 || u16_at(54) != 56 {
            return Err(fail(pc, "invalid ELF or program-header size"));
        }
        let phoff = u64_at(32);
        let phnum = u16_at(56) as u64;
        if phnum == 0 || phnum == 0xffff {
            return Err(fail(pc, "missing or extended program-header count"));
        }
        let end = phoff
            .checked_add(phnum * 56)
            .ok_or_else(|| fail(pc, "program-header overflow"))?;
        if phoff < 64 || end > elf.len() as u64 {
            return Err(fail(pc, "program headers outside ELF"));
        }
        let image: Arc<[u8]> = Arc::from(elf);
        let mut segments = Vec::new();
        for index in 0..phnum {
            let p = (phoff + index * 56) as usize;
            let typ = u32_at(p);
            if typ == 2 || typ == 3 {
                return Err(fail(pc, "dynamic ELF execution is unsupported"));
            }
            if typ != 1 {
                continue;
            }
            let flags = u32_at(p + 4);
            let offset = u64_at(p + 8);
            let address = u64_at(p + 16);
            let file_size = u64_at(p + 32);
            let memory_size = u64_at(p + 40);
            let alignment = u64_at(p + 48);
            if flags & !7 != 0 || flags & 3 == 3 {
                return Err(fail(pc, "invalid permissions or writable executable segment"));
            }
            if file_size > memory_size {
                return Err(fail(pc, "segment file size exceeds memory size"));
            }
            let file_end = offset
                .checked_add(file_size)
                .ok_or_else(|| fail(pc, "segment file range overflow"))?;
            let mem_end = address
                .checked_add(memory_size)
                .ok_or_else(|| fail(pc, "segment memory range overflow"))?;
            if file_end > elf.len() as u64 || address >= RAM_END || mem_end > RAM_END {
                return Err(fail(pc, "segment outside file or guest memory"));
            }
            if alignment > 1 && (!alignment.is_power_of_two() || address % alignment != offset % alignment) {
                return Err(fail(pc, "invalid segment alignment"));
            }
            segments.push(Segment {
                address,
                memory_size,
                flags,
                alignment,
                file_offset: offset,
                file_size,
                image: Arc::clone(&image),
            });
        }
        segments.sort_by_key(|segment| segment.address);
        let mut previous_end = 0;
        for segment in &segments {
            if segment.memory_size == 0 {
                continue;
            }
            if segment.address < previous_end {
                return Err(fail(pc, "overlapping PT_LOAD ranges"));
            }
            previous_end = segment.address + segment.memory_size;
        }
        if pc & 3 != 0 {
            return Err(fail(pc, "entry is not four-byte aligned"));
        }
        if !(0..4).all(|i| {
            segments
                .iter()
                .any(|s| s.executable() && s.contains(pc.wrapping_add(i)))
        }) {
            return Err(fail(pc, "entry is not executable mapped memory"));
        }
        let mut initial = MemorySnapshot::default();
        for segment in &segments {
            for (index, &byte) in segment.bytes().iter().enumerate() {
                if byte != 0 {
                    initial.set(segment.address + index as u64, byte);
                }
            }
        }
        Ok(Self {
            entry: pc,
            segments,
            initial,
            image,
        })
    }

    pub(crate) fn check_access(&self, pc: u64, address: u64, length: u64, kind: AccessKind) -> Result<(), Error> {
        let end = address.checked_add(length).filter(|&end| end <= RAM_END);
        if address > RAM_END || end.is_none() {
            return Err(Error {
                pc,
                kind: ErrorKind::MemoryOutOfBounds { address, length },
            });
        }
        let end = end.unwrap();
        if kind == AccessKind::Fetch {
            for at in address..end {
                if !self.segments.iter().any(|s| s.executable() && s.contains(at)) {
                    return Err(Error {
                        pc,
                        kind: ErrorKind::PermissionDenied { address: at, kind },
                    });
                }
            }
        } else {
            for segment in &self.segments {
                if segment.memory_size != 0 && address < segment.address + segment.memory_size && end > segment.address
                {
                    let allowed = match kind {
                        AccessKind::Read => segment.readable(),
                        AccessKind::Write => segment.writable() && !segment.executable(),
                        AccessKind::Fetch => unreachable!(),
                    };
                    if !allowed && length != 0 {
                        return Err(Error {
                            pc,
                            kind: ErrorKind::PermissionDenied {
                                address: address.max(segment.address),
                                kind,
                            },
                        });
                    }
                }
            }
        }
        Ok(())
    }
}
