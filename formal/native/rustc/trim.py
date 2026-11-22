#!/usr/bin/env python3
"""Keep rustc's reachable code and data verbatim, stopping at ingestion's panic traps.

Usage: python3 trim.py INPUT.s OUTPUT.s ENTRY
The output is a subsequence of the input lines, in their original order. It is
proof input, not a standalone replacement for the full assembly linked by run/.
"""

import argparse
from pathlib import Path
import re


# Keep in sync with RustcIngest.Core.panicSuffixes.
PANIC_SUFFIXES = (
    "9panicking9panic_fmt",
    "5slice5index16slice_index_fail",
    "6option13unwrap_failed",
)
IDENT = r"[A-Za-z_.$][A-Za-z_.$0-9]*"
LABEL = re.compile(rf"^\s*({IDENT}):\s*(?://.*|#.*)?$")
TYPE = re.compile(rf"^\s*\.type\s+({IDENT}),\s*[@%](function|object)\b")
SIZE = re.compile(rf"^\s*\.size\s+({IDENT}),")
TOKEN = re.compile(r"(?<![A-Za-z_.0-9])[A-Za-z_.][A-Za-z_.$0-9]*")
STRINGS = re.compile(r'"(?:\\.|[^"\\])*"')
HEADER = {
    ".section", ".text", ".data", ".bss", ".p2align", ".balign", ".align",
    ".globl", ".local", ".hidden", ".protected", ".weak", ".type",
}
SECTIONS = {".section", ".text", ".data", ".bss"}


def trim(text: str, entry: str) -> str:
    lines = text.splitlines(keepends=True)
    x64 = any(line.strip() == ".att_syntax" for line in lines)
    labels = {}
    types = {}
    sizes = {}
    sections = []
    section = None
    for i, line in enumerate(lines):
        fields = line.split()
        if fields and fields[0] in SECTIONS:
            section = i
        sections.append(section)
        if match := LABEL.match(line):
            labels[match[1]] = i
        if match := TYPE.match(line):
            types[match[1]] = (i, match[2])
        if match := SIZE.match(line):
            sizes[match[1]] = i

    # A block includes its section, visibility and alignment preamble. Functions
    # own their local labels; data references may also name an interior label.
    blocks = {}
    owners = {}
    occupied = set()

    def add_block(name, start, end):
        while start > 0:
            fields = lines[start - 1].split()
            if fields and fields[0] not in HEADER:
                break
            start -= 1
        blocks[name] = (start, end)
        for i in range(start, end):
            occupied.add(i)
            if match := LABEL.match(lines[i]):
                owners[match[1]] = name

    for name, (type_line, kind) in types.items():
        if name not in labels or name not in sizes:
            raise ValueError(f"{name}: missing label or .size")
        end = sizes[name] + 1
        if kind == "function" and end < len(lines) and lines[end].strip() == ".cfi_endproc":
            end += 1
        add_block(name, min(type_line, labels[name]), end)

    # LLVM may emit untyped constant pools and jump tables. They end at the
    # next label or section, unlike the explicitly sized objects above.
    for name, pos in labels.items():
        if pos in occupied:
            continue
        end = pos + 1
        while end < len(lines) and end not in occupied:
            fields = lines[end].split()
            if LABEL.match(lines[end]) or (fields and fields[0] in SECTIONS):
                break
            end += 1
        add_block(name, pos, end)

    if entry not in blocks or types.get(entry, (None, None))[1] != "function":
        raise ValueError(f"no entry function {entry}")
    kept = set()
    pending = [entry]
    selected = set()
    while pending:
        name = pending.pop()
        if name in selected or name.endswith(PANIC_SUFFIXES):
            continue
        selected.add(name)
        start, end = blocks[name]
        kept.update(range(start, end))
        section = sections[labels[name]]
        if section is not None:
            kept.add(section)
        for line in lines[start:end]:
            # Literal strings and comments are not references. Tokenization
            # leaves symbol@GOTPCREL, :got:symbol and symbol+offset intact as
            # symbol tokens, and also follows references in data directives.
            code = STRINGS.sub("", line).split("//", 1)[0]
            if x64:
                code = code.split("#", 1)[0]
            fields = code.split()
            if not fields or fields[0] in HEADER or fields[0] == ".size":
                continue
            for token in TOKEN.findall(code):
                if token in owners:
                    pending.append(owners[token])

    file_ids = set()
    for i in kept:
        fields = lines[i].split()
        if fields and fields[0] == ".loc":
            file_ids.add(fields[1])
    for i, line in enumerate(lines):
        fields = line.split()
        if not fields:
            continue
        directive = fields[0]
        if directive in {".att_syntax", ".intel_syntax", ".cfi_sections", ".ident"}:
            kept.add(i)
        elif directive == ".file" and (fields[1].startswith('"') or fields[1] in file_ids):
            kept.add(i)
        elif directive == ".section" and '".note.GNU-stack"' in line:
            kept.add(i)
    return "".join(line for i, line in enumerate(lines) if i in kept)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("entry")
    args = parser.parse_args()
    # bytes avoids universal-newline conversion: retained lines stay verbatim.
    result = trim(args.source.read_bytes().decode("utf-8"), args.entry)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(result.encode("utf-8"))


if __name__ == "__main__":
    main()
