use crate::{AccessKind, Error, MemoryEvent, Program, RAM_END};
use std::{collections::BTreeMap, sync::Arc};

pub const PAGE_SIZE: usize = 4096;

/// Copy-on-write sparse pages, keyed by page number (address / PAGE_SIZE).
/// Missing pages read as zero. Page contents cannot be mutated by callers.
#[derive(Clone, Debug, Default)]
pub struct MemorySnapshot {
    pages: BTreeMap<u64, Arc<[u8; PAGE_SIZE]>>,
}

impl MemorySnapshot {
    pub fn pages(&self) -> impl Iterator<Item = (u64, &[u8; PAGE_SIZE])> {
        self.pages.iter().map(|(&number, bytes)| (number, bytes.as_ref()))
    }
    pub fn read_byte(&self, address: u64) -> Option<u8> {
        if address >= RAM_END {
            return None;
        }
        Some(self.byte(address))
    }
    pub(crate) fn byte(&self, address: u64) -> u8 {
        self.pages
            .get(&(address / PAGE_SIZE as u64))
            .map_or(0, |page| page[address as usize % PAGE_SIZE])
    }
    pub(crate) fn set(&mut self, address: u64, value: u8) {
        let page = self
            .pages
            .entry(address / PAGE_SIZE as u64)
            .or_insert_with(|| Arc::new([0; PAGE_SIZE]));
        Arc::make_mut(page)[address as usize % PAGE_SIZE] = value;
    }
}

pub(crate) struct Memory<'a> {
    pub program: &'a Program,
    pub snapshot: MemorySnapshot,
}

impl<'a> Memory<'a> {
    pub fn new(program: &'a Program) -> Self {
        Self {
            program,
            snapshot: program.initial_memory().clone(),
        }
    }
    pub fn fetch(&self, pc: u64) -> Result<u32, Error> {
        self.program.check_access(pc, pc, 4, AccessKind::Fetch)?;
        Ok(u32::from_le_bytes(std::array::from_fn(|i| {
            self.snapshot.byte(pc + i as u64)
        })))
    }
    pub fn read<const N: usize>(&self, pc: u64, address: u64, events: &mut Vec<MemoryEvent>) -> Result<[u8; N], Error> {
        self.program.check_access(pc, address, N as u64, AccessKind::Read)?;
        Ok(std::array::from_fn(|i| {
            let address = address + i as u64;
            let value = self.snapshot.byte(address);
            events.push(MemoryEvent {
                address,
                before: value,
                after: value,
                kind: AccessKind::Read,
            });
            value
        }))
    }
    pub fn load(&mut self, pc: u64, address: u64, length: usize, events: &mut Vec<MemoryEvent>) -> Result<u64, Error> {
        self.program
            .check_access(pc, address, length as u64, AccessKind::Read)?;
        let mut bytes = [0; 8];
        for (i, byte) in bytes[..length].iter_mut().enumerate() {
            let address = address + i as u64;
            *byte = self.snapshot.byte(address);
            events.push(MemoryEvent {
                address,
                before: *byte,
                after: *byte,
                kind: AccessKind::Read,
            });
        }
        Ok(u64::from_le_bytes(bytes))
    }
    pub fn write(&mut self, pc: u64, address: u64, bytes: &[u8], events: &mut Vec<MemoryEvent>) -> Result<(), Error> {
        self.program
            .check_access(pc, address, bytes.len() as u64, AccessKind::Write)?;
        for (index, &after) in bytes.iter().enumerate() {
            let address = address + index as u64;
            let before = self.snapshot.byte(address);
            self.snapshot.set(address, after);
            events.push(MemoryEvent {
                address,
                before,
                after,
                kind: AccessKind::Write,
            });
        }
        Ok(())
    }
}
