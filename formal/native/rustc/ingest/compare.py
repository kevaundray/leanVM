#!/usr/bin/env python3
"""Compares the functions of an object file assembled from an ingested program with rustc's object file.

Usage: compare.py RUSTC.o INGESTED.o

Both files are ELF relocatable files for AArch64 or x86-64. Every function of INGESTED.o (a symbol at the
start of a `.text.<name>` section), other than the traps (the panic entries of `core`, which the ingested
program replaces with a trap: `PANIC_SUFFIXES`), must be a function of RUSTC.o of the same size whose
bytes and relocations are the same. A relocation is compared as its offset, its type, its target and its
addend: a target is a function (or other named symbol) by name, or a data item by contents, recursively
(its bytes and its own relocations). A section symbol stands for the named symbol at the start of its
section when there is one (each function has a section of its own); otherwise for its section's
contents (each data item of either file has a section of its own), or, in a section of mergeable
strings, for the string at the addend up to its terminating NUL. Local labels never reach the object
files, so their names (which ingestion renames) are not compared. Every function a relocation of
INGESTED.o targets must be defined in it, and every data section of INGESTED.o must be reached.

AArch64 instruction words are compared exactly but for one bit: a byte load or store with a register
offset (`LDRB`, `STRB`, `LDRSB`) encodes `[Xn, Xm]` with S = 0 and `[Xn, Xm, LSL #0]` with S = 1, both
shifting the offset by 0 (Arm ARM, "LDRB (register)"). Kraken's syntax has one form for both (shift
amount 0), which its printer writes as `LSL #0`; S is compared as 0 in such words. x86-64 bytes are
compared exactly.
"""

import struct
import sys

SHT_SYMTAB, SHT_RELA, SHT_NOBITS = 2, 4, 8
SHF_MERGE, SHF_STRINGS = 0x10, 0x20
STT_SECTION = 3
EM_X86_64, EM_AARCH64 = 0x3E, 0xB7
PANIC_SUFFIXES = ("9panicking9panic_fmt", "5slice5index16slice_index_fail")


def normalise(machine, code):
    """The bytes of `code`, compared: on AArch64, S cleared in byte loads and stores with a register
    offset."""
    if machine != EM_AARCH64:
        return code
    out = bytearray(code)
    for k in range(0, len(code) - len(code) % 4, 4):
        w = int.from_bytes(code[k:k + 4], "little")
        if w & 0xFF200C00 == 0x38200800:
            out[k:k + 4] = (w & ~(1 << 12)).to_bytes(4, "little")
    return bytes(out)


class Elf:
    def __init__(self, path):
        self.path = path
        data = open(path, "rb").read()
        if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
            raise SystemExit(f"{path}: not a little-endian ELF64 file")
        self.machine, = struct.unpack_from("<H", data, 0x12)
        shoff, = struct.unpack_from("<Q", data, 0x28)
        shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 0x3A)
        secs = []
        for i in range(shnum):
            name, typ, flags, _, off, size, link, info, _, entsize = struct.unpack_from(
                "<IIQQQQIIQQ", data, shoff + i * shentsize)
            secs.append(dict(name=name, type=typ, flags=flags, off=off, size=size, link=link, info=info,
                             entsize=entsize))
        strtab = secs[shstrndx]
        for s in secs:
            s["name"] = self._str(data, strtab["off"], s["name"])
            s["data"] = data[s["off"]:s["off"] + s["size"]] if s["type"] != SHT_NOBITS else b"\0" * s["size"]
        self.secs = secs
        self.syms = []
        for s in secs:
            if s["type"] == SHT_SYMTAB:
                names = secs[s["link"]]
                for k in range(s["size"] // 24):
                    name, info, _, shndx, value, size = struct.unpack_from("<IBBHQQ", data, s["off"] + 24 * k)
                    self.syms.append(dict(name=self._str(data, names["off"], name), type=info & 0xF,
                                          bind=info >> 4, shndx=shndx, value=value, size=size))
        # Relocations of each section: offset -> (type, symbol index, addend).
        self.relocs = {}
        for s in secs:
            if s["type"] == SHT_RELA:
                rs = self.relocs.setdefault(s["info"], {})
                for k in range(s["size"] // 24):
                    off, info, addend = struct.unpack_from("<QQq", data, s["off"] + 24 * k)
                    rs[off] = (info & 0xFFFFFFFF, info >> 32, addend)

    @staticmethod
    def _str(data, base, off):
        end = data.index(b"\0", base + off)
        return data[base + off:end].decode()

    def named_at(self, shndx, value):
        """The named symbols at `value` in section `shndx`: neither section symbols, local labels nor
        mapping symbols (`$x`, `$d`)."""
        return sorted(s["name"] for s in self.syms
                      if s["shndx"] == shndx and s["value"] == value and s["type"] != STT_SECTION
                      and s["name"] and not s["name"].startswith((".L", "$")))

    def functions(self):
        """Each symbol at the start of a `.text.*` section: name -> section index."""
        out = {}
        for i, s in enumerate(self.secs):
            if s["name"].startswith(".text."):
                for n in self.named_at(i, 0):
                    out[n] = i
        return out

    def target(self, symidx, addend, depth=0, reached=None):
        """The canonical form of a relocation's target and addend."""
        sym = self.syms[symidx]
        if sym["type"] != STT_SECTION and sym["name"] and not sym["name"].startswith((".L", "$")):
            if sym["shndx"] == 0:
                return ("undefined", sym["name"], addend)
            return ("symbol", sym["name"], addend)
        shndx, off = sym["shndx"], sym["value"] + addend
        sec = self.secs[shndx]
        if sec["flags"] & SHF_MERGE and sec["flags"] & SHF_STRINGS:
            return (self.datum(shndx, off, sec["data"].index(b"\0", off) + 1, depth, reached), 0)
        named = self.named_at(shndx, 0)
        if named:
            return ("symbol", named[0], off)
        return (self.datum(shndx, 0, sec["size"], depth, reached), off)

    def datum(self, shndx, start, end, depth, reached):
        """The bytes `start` to `end` of a section, and their relocations."""
        if depth > 8:
            raise SystemExit(f"{self.path}: data refers to data too deeply")
        if reached is not None:
            reached.add(shndx)
        rels = tuple(sorted((o - start, t, self.target(si, a, depth + 1, reached))
                            for o, (t, si, a) in self.relocs.get(shndx, {}).items() if start <= o < end))
        return ("data", self.secs[shndx]["data"][start:end].hex(), rels)

    def function(self, shndx, reached=None):
        sec = self.secs[shndx]
        rels = {o: (t, self.target(si, a, 0, reached)) for o, (t, si, a) in self.relocs.get(shndx, {}).items()}
        return sec["data"], rels


def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    ref, mine = Elf(sys.argv[1]), Elf(sys.argv[2])
    if ref.machine != mine.machine or ref.machine not in (EM_X86_64, EM_AARCH64):
        raise SystemExit(f"{sys.argv[1]}, {sys.argv[2]}: machines {ref.machine}, {mine.machine}")
    ref_fns, mine_fns = ref.functions(), mine.functions()
    errors = []
    reached = set()
    compared = 0
    for name, shndx in sorted(mine_fns.items()):
        if name.endswith(PANIC_SUFFIXES):
            continue
        if name not in ref_fns:
            errors.append(f"{name}: not a function of {ref.path}")
            continue
        rsym = [s for s in ref.syms if s["name"] == name and s["shndx"] == ref_fns[name] and s["value"] == 0]
        rbytes, rrels = ref.function(ref_fns[name])
        mbytes, mrels = mine.function(shndx, reached)
        rsize = rsym[0]["size"] if rsym and rsym[0]["size"] else len(rbytes)
        if len(mbytes) != rsize:
            errors.append(f"{name}: {len(mbytes)} bytes ingested, {rsize} rustc")
        else:
            rn, mn = normalise(ref.machine, rbytes[:rsize]), normalise(mine.machine, mbytes)
            if rn != mn:
                k = next(k for k in range(rsize) if rn[k] != mn[k])
                errors.append(f"{name}+{k:#x}: bytes {mn[k:k + 8].hex()} ingested, {rn[k:k + 8].hex()} rustc")
        rrels = {o: r for o, r in rrels.items() if o < rsize}
        for o in sorted(set(rrels) | set(mrels)):
            if rrels.get(o) != mrels.get(o):
                errors.append(f"{name}+{o:#x}: relocation {mrels.get(o)} ingested, {rrels.get(o)} rustc")
        for o, (_, t) in mrels.items():
            if t[0] == "undefined":
                errors.append(f"{name}+{o:#x}: {t[1]} is not in the ingested program")
        compared += 1
    for i, s in enumerate(mine.secs):
        if s["name"].startswith(".rodata") and s["size"] and i not in reached:
            errors.append(f"{s['name']}: data the functions do not reach")
    for e in errors:
        print(f"MISMATCH {e}")
    if errors or compared == 0:
        raise SystemExit(f"{sys.argv[2]}: {len(errors)} mismatches against {sys.argv[1]}")
    print(f"{sys.argv[2]}: {compared} functions identical to {sys.argv[1]}, "
          f"{len(reached)} data sections reached")


if __name__ == "__main__":
    main()
