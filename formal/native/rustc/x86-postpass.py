#!/usr/bin/env python3
"""Rewrites rustc's x86-64 assembly (`rustc/build.sh`, `out/{xmss,sphincs}-x86_64.s`) so that every instruction of its
core is one Kraken's x86-64 parser reads. The output is what gets assembled, run (`run/check.sh`) and proved.

Usage: x86-postpass.py IN.s [OUT.s]      (OUT.s defaults to standard output)

The core: the functions reachable from the entry `*_verify` (direct calls and jumps, and references to a function's
address: `f@GOTPCREL`, `f(%rip)`), without entering the panic entries `core::panicking::panic_fmt` and
`core::slice::index::slice_index_fail`. Only core lines are rewritten; every other line is copied unchanged. A
rewritten instruction carries the comment `# postpass RULE: ORIGINAL`.

Rules (each keeps every register, every flag a later instruction reads, and every live memory byte as the original
instruction leaves them; the argument is stated with each rule below):
  got-call  `callq *f@GOTPCREL(%rip)` -> `callq f`, `jmpq *f@GOTPCREL(%rip)` -> `jmp f`
  got-load  `movq f@GOTPCREL(%rip), %r` -> `leaq f(%rip), %r`
  reg-call  `callq *%r` -> `callq f` where a dataflow analysis shows that %r holds the address of `f`
  bt        `bt{l,q} %k, %x` -> push, two right shifts, pop
  bts       `bts{l,q} %k, %x` -> push, a shifted one or-ed in, pop
  lea       `leaq d(,%i,s), %r`, `leal d(,%i,s), %e` (no base register) -> one to three of it with a base register

The script is deterministic and idempotent (its output contains none of the patterns it rewrites), and fails, writing
nothing, when a core instruction matches no rule's preconditions but would still be one Kraken rejects
(`@GOTPCREL`, `*`, `bt`, a memory operand without a base register).
"""

import re
import sys

PANICS = re.compile(r"9panicking9panic_fmt$|5slice5index16slice_index_fail$")

REG64 = ["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp"] + [f"r{i}" for i in range(8, 16)]
# Every register name to the 64-bit register it is part of.
PARENT = {}
for _r in ["a", "b", "c", "d"]:
    for _n in [f"r{_r}x", f"e{_r}x", f"{_r}x", f"{_r}l", f"{_r}h"]:
        PARENT[_n] = f"r{_r}x"
for _r in ["si", "di", "bp", "sp"]:
    for _n in [f"r{_r}", f"e{_r}", _r, f"{_r}l"]:
        PARENT[_n] = f"r{_r}"
for _i in range(8, 16):
    for _s in ["", "d", "w", "b"]:
        PARENT[f"r{_i}{_s}"] = f"r{_i}"
NAME32 = {r: (f"e{r[1:]}" if r[1:] in ("ax", "bx", "cx", "dx", "si", "di", "bp", "sp") else f"{r}d") for r in REG64}
CALLER_SAVED = ["rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11"]

CC_CF_ONLY = {"b", "c", "nae", "ae", "nb", "nc"}
CC = r"(?:o|no|b|c|nae|ae|nb|nc|e|z|ne|nz|be|na|a|nbe|s|ns|p|pe|np|po|l|nge|ge|nl|le|ng|g|nle)"
SUF = r"[bwlq]?"
# Mnemonics whose register destination is their last operand (and that write no other register).
DST_LAST = re.compile(
    rf"^(?:(?:add|sub|and|or|xor|adc|sbb|mov|movabs|lea|not|neg|inc|dec|shl|sal|shr|sar|rol|ror|rcl|rcr|shld|shrd"
    rf"|bswap|pop){SUF}|movz[bw][wlq]|movs[bwl][wlq]|movslq|cmov{CC}{SUF}|set{CC})$"
)
NO_REG_WRITE = re.compile(rf"^(?:(?:cmp|test|bt|push){SUF}|j{CC}|jmpq?|nop[wlq]?|retq?)$")
# Instructions after which ZF, SF, OF, PF and AF are all set from their result.
FLAGS_WRITER = re.compile(rf"^(?:add|sub|and|or|xor|adc|sbb|cmp|test|neg|inc|dec){SUF}$")


def split_ops(s):
    """The operands of an instruction, split at the commas outside parentheses."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def parse(line):
    """`(mnemonic, operands)` of an instruction line, else None (labels, directives, comments, blank lines)."""
    s = line.split("#", 1)[0].strip()
    if not s or s.startswith(".") or s.endswith(":"):
        return None
    parts = s.split(None, 1)
    return parts[0], split_ops(parts[1]) if len(parts) > 1 else []


def label_of(line):
    m = re.match(r"^([A-Za-z_.$][\w.$]*):", line)
    return m.group(1) if m else None


def reg(op):
    """The 64-bit register an operand `%name` is part of, else None."""
    m = re.fullmatch(r"%(\w+)", op)
    return PARENT.get(m.group(1)) if m else None


def ins(mn, *ops, rule, orig):
    return f"\t{mn}\t{', '.join(ops)}" if ops else f"\t{mn}", rule, orig


class Postpass:
    def __init__(self, lines):
        self.lines = lines
        self.funcs = {}  # name -> (first line, last line), both inclusive
        cur = None
        for i, l in enumerate(lines):
            name = label_of(l)
            if name and i + 1 < len(lines) and re.match(r"^\.Lfunc_begin\d+:", lines[i + 1]):
                cur = name
                self.funcs[cur] = [i, None]
            elif cur and re.match(r"^\.Lfunc_end\d+:", l):
                self.funcs[cur][1] = i
                cur = None
        self.core = self.reachable()

    def body(self, f):
        a, b = self.funcs[f]
        return range(a, b + 1)

    def reachable(self):
        entries = [f for f in self.funcs if f.endswith("_verify")]
        if len(entries) != 1:
            sys.exit(f"x86-postpass: expected one entry *_verify, found {entries}")
        seen, stack = [], entries
        while stack:
            f = stack.pop()
            if f in seen or PANICS.search(f):
                continue
            seen.append(f)
            for i in self.body(f):
                s = self.lines[i].split("#", 1)[0]
                for sym in re.findall(r"(?:callq|jmpq?)\s+\*?([A-Za-z_.$][\w.$]*)\s*$", s) + re.findall(
                    r"([A-Za-z_.$][\w.$]*)(?:@GOTPCREL)?\(%rip\)", s
                ):
                    if sym in self.funcs:
                        stack.append(sym)
        return sorted(seen, key=lambda f: self.funcs[f][0])

    # got-call, got-load. The GOT slot of `f` holds the address of `f`: loading it and calling or jumping through it
    # does what a call or jump to `f`, or computing `f`'s address, does, besides reading the slot (relro memory outside
    # the program, which nothing writes). These are the linker's own GOTPCRELX relaxations, which `ld.lld` applies
    # when `f` is defined in the link and not preemptible, as here: `run/check.sh` links the object statically, with
    # every symbol but the entry made local.
    def got(self, i, mn, ops):
        if len(ops) == 1 and mn in ("callq", "jmpq"):
            m = re.fullmatch(r"\*([A-Za-z_.$][\w.$]*)@GOTPCREL\(%rip\)", ops[0])
            if m and m.group(1) in self.funcs:
                return [ins("callq" if mn == "callq" else "jmp", m.group(1), rule="got-call", orig=self.lines[i])]
        if len(ops) == 2 and mn == "movq" and reg(ops[1]):
            m = re.fullmatch(r"([A-Za-z_.$][\w.$]*)@GOTPCREL\(%rip\)", ops[0])
            if m and m.group(1) in self.funcs:
                return [ins("leaq", f"{m.group(1)}(%rip)", ops[1], rule="got-load", orig=self.lines[i])]
        return None

    # reg-call. A forward must-analysis over the function's control flow graph finds, before each instruction, the
    # registers that hold a function's address. A register gets `f` from `leaq f(%rip), %r` (got-load's output) or from
    # a `movq` of a register holding `f`; any other write to it (by its last operand, a call's clobber of the
    # caller-saved registers, or an instruction the analysis does not know, which forgets every register) forgets it;
    # a call keeps the callee-saved registers (rbx, rbp, r12-r15), as every callee does by the SysV ABI (and as the
    # proof's contract of each callee states). At a join the value is kept only if every predecessor has it. Where `%r`
    # holds `f`, `callq *%r` and `callq f` push the same return address and go to the same place, and leave `%r` alone.
    # A function with an indirect jump (whose targets the graph would miss) is left as it is.
    def reg_calls(self, f, out):
        idx = list(self.body(f))
        code = {i: parse(out[i][0][0]) if len(out[i]) == 1 else None for i in idx}
        if any(c and c[0].startswith("jmp") and c[1] and c[1][0].startswith("*") for c in code.values()):
            return
        labels = {label_of(self.lines[i]): i for i in idx if label_of(self.lines[i])}

        def transfer(state, c):
            mn, ops = c
            st = dict(state)
            if mn in ("callq", "call"):
                for r in CALLER_SAVED:
                    st.pop(r, None)
                return st
            if mn == "leaq" and len(ops) == 2 and reg(ops[1]):
                m = re.fullmatch(r"([A-Za-z_.$][\w.$]*)\(%rip\)", ops[0])
                if m and m.group(1) in self.funcs:
                    st[reg(ops[1])] = m.group(1)
                    return st
            if mn == "movq" and len(ops) == 2 and reg(ops[0]) and reg(ops[1]):
                v = st.get(reg(ops[0]))
                st.pop(reg(ops[1]), None)
                if v:
                    st[reg(ops[1])] = v
                return st
            if NO_REG_WRITE.match(mn):
                return st
            if DST_LAST.match(mn) or (re.fullmatch(r"imul[wlq]?", mn) and len(ops) >= 2):
                if ops and reg(ops[-1]):
                    st.pop(reg(ops[-1]), None)
                return st
            return {}

        # Successors of each instruction line, and the state before each line (None: not reached yet).
        def succs(k):
            i = idx[k]
            c = code[i]
            nxt = [idx[k + 1]] if k + 1 < len(idx) else []
            if c is None:
                return nxt
            mn, ops = c
            if re.fullmatch(rf"j{CC}", mn):
                return nxt + ([labels[ops[0]]] if ops[0] in labels else [])
            if mn in ("jmp", "jmpq"):
                return [labels[ops[0]]] if ops and ops[0] in labels else []
            if mn in ("retq", "ret", "ud2"):
                return []
            return nxt

        pos = {i: k for k, i in enumerate(idx)}
        before = {i: None for i in idx}
        before[idx[0]] = {}
        work = [idx[0]]
        while work:
            i = work.pop()
            st = before[i]
            after = transfer(st, code[i]) if code[i] else st
            for j in succs(pos[i]):
                if before[j] is None:
                    new = dict(after)
                else:
                    new = {r: v for r, v in before[j].items() if after.get(r) == v}
                if new != before[j]:
                    before[j] = new
                    work.append(j)
        for i in idx:
            c = code[i]
            if c and c[0] == "callq" and len(c[1]) == 1 and c[1][0].startswith("*%") and before[i] is not None:
                target = before[i].get(reg(c[1][0][1:]))
                if target:
                    out[i] = [ins("callq", target, rule="reg-call", orig=self.lines[i])]

    # bt. `bt{l,q} %k, %x` sets CF to bit (k mod 32, or mod 64) of %x and writes nothing else that is defined (ZF is
    # kept, OF, SF, AF and PF are undefined). The replacement saves %x, shifts it right by %cl (the hardware masks the
    # count alike, mod 32 or mod 64; a zero count changes nothing) and then by one, which puts that bit in CF, and
    # restores %x; when the bit index is not in %rcx, %rcx is saved and restored around it too (and when %x is %rcx, a
    # copy of it is shifted in a scratch register, saved and restored as well). So every register (and rsp) and CF end
    # as bt leaves them. Two preconditions make the rest invisible:
    #  - the flags: on every path from bt, nothing reads ZF, SF, OF, PF or AF before an instruction that sets them all
    #    (add, sub, and, or, xor, adc, sbb, cmp, test, neg, inc, dec); the paths followed are the function's own:
    #    through a conditional jump on CF alone (`jb`, `jae`, ...) both ways, through `jmp` to its label, and a call
    #    or return ends none (so none may come first);
    #  - the stack: the pushes write the 8 or 16 bytes below rsp, which hold nothing live because the function makes
    #    calls (LLVM keeps data below rsp, in the red zone, only in functions that make none) or has no operand below
    #    rsp (`-k(%rsp)`), so keeps nothing there.
    def bt(self, i, mn, ops, no_red_zone):
        m = re.fullmatch(r"bt([lq])", mn)
        if not m or len(ops) != 2 or not reg(ops[0]) or not reg(ops[1]):
            return None
        w = m.group(1)
        k, x = reg(ops[0]), reg(ops[1])
        if not no_red_zone or not self.flags_dead_after(i):
            return None
        xw = ops[1]
        o = self.lines[i]
        if k == "rcx":
            return [ins("pushq", f"%{x}", rule="bt", orig=o), ins(f"shr{w}", "%cl", xw, rule="bt", orig=o),
                    ins(f"shr{w}", "$1", xw, rule="bt", orig=o), ins("popq", f"%{x}", rule="bt", orig=o)]
        if x == "rcx":
            # The bit's word is in %rcx, which the count needs: shift a copy in a scratch register %s instead.
            sc = "rsi" if k == "rax" else "rax"
            sw = f"%{sc}" if w == "q" else f"%{NAME32[sc]}"
            return [ins("pushq", f"%{sc}", rule="bt", orig=o), ins("pushq", "%rcx", rule="bt", orig=o),
                    ins("movq", "%rcx", f"%{sc}", rule="bt", orig=o), ins("movl", f"%{NAME32[k]}", "%ecx", rule="bt", orig=o),
                    ins(f"shr{w}", "%cl", sw, rule="bt", orig=o), ins(f"shr{w}", "$1", sw, rule="bt", orig=o),
                    ins("popq", "%rcx", rule="bt", orig=o), ins("popq", f"%{sc}", rule="bt", orig=o)]
        return [ins("pushq", "%rcx", rule="bt", orig=o), ins("pushq", f"%{x}", rule="bt", orig=o),
                ins("movl", f"%{NAME32[k]}", "%ecx", rule="bt", orig=o), ins(f"shr{w}", "%cl", xw, rule="bt", orig=o),
                ins(f"shr{w}", "$1", xw, rule="bt", orig=o), ins("popq", f"%{x}", rule="bt", orig=o),
                ins("popq", "%rcx", rule="bt", orig=o)]

    # bts. `bts{l,q} %k, %x` sets bit (k mod 32, or mod 64) of %x, CF to its old value, and writes nothing else that
    # is defined. The replacement saves %rcx and a scratch register %s (neither %x nor %k), puts the bit index in %cl,
    # shifts a one in %s left by it (the hardware masks the count alike) and or-s it into %x, and restores %s and
    # %rcx; so every register ends as bts leaves it. Its preconditions are bt's, the flags' with CF too: on every path
    # from bts nothing reads any flag before an instruction that sets them all.
    def bts(self, i, mn, ops, no_red_zone):
        m = re.fullmatch(r"bts([lq])", mn)
        if not m or len(ops) != 2 or not reg(ops[0]) or not reg(ops[1]):
            return None
        w = m.group(1)
        k, x = reg(ops[0]), reg(ops[1])
        if x == "rcx" or not no_red_zone or not self.flags_dead_after(i, cf_read=False):
            return None
        sc = next(r for r in ("rax", "rdx", "rsi", "rdi") if r not in (k, x))
        sw = f"%{sc}" if w == "q" else f"%{NAME32[sc]}"
        o = self.lines[i]
        out = [ins("pushq", "%rcx", rule="bts", orig=o), ins("pushq", f"%{sc}", rule="bts", orig=o)]
        if k != "rcx":
            out.append(ins("movl", f"%{NAME32[k]}", "%ecx", rule="bts", orig=o))
        return out + [ins("movl", "$1", f"%{NAME32[sc]}", rule="bts", orig=o), ins(f"shl{w}", "%cl", sw, rule="bts", orig=o),
                      ins(f"or{w}", sw, ops[1], rule="bts", orig=o), ins("popq", f"%{sc}", rule="bts", orig=o),
                      ins("popq", "%rcx", rule="bts", orig=o)]

    def flags_dead_after(self, i, cf_read=True):
        f = next(g for g, (a, b) in self.funcs.items() if a <= i <= b)
        a, b = self.funcs[f]
        labels = {label_of(self.lines[j]): j for j in range(a, b + 1) if label_of(self.lines[j])}
        seen = set()

        def dead_from(j):
            # Whether every path from line j sets the flags before reading ZF, SF, OF, PF or AF.
            while j <= b:
                if j in seen:
                    return True
                seen.add(j)
                c = parse(self.lines[j])
                if c is None:
                    if re.match(r"^\.Lfunc_end\d+:", self.lines[j]):
                        return False
                    j += 1
                    continue
                mn, ops = c
                m = re.fullmatch(rf"(?:set|cmov|j)({CC})[wlq]?", mn)
                if m:
                    if m.group(1) not in CC_CF_ONLY or not cf_read:
                        return False
                    if mn.startswith("j"):
                        if len(ops) != 1 or ops[0] not in labels or not dead_from(labels[ops[0]]):
                            return False
                    j += 1
                    continue
                if mn in ("jmp", "jmpq") and len(ops) == 1 and ops[0] in labels:
                    j = labels[ops[0]]
                    continue
                if re.match(r"^(?:jmp|call|ret)", mn) or re.fullmatch(rf"(?:rcl|rcr){SUF}", mn) or (
                        not cf_read and re.fullmatch(rf"(?:adc|sbb){SUF}", mn)):
                    return False
                if FLAGS_WRITER.match(mn):
                    return True
                if DST_LAST.match(mn) or re.fullmatch(r"(?:push|pop)[wq]?|bswap[lq]|bt[lq]", mn):
                    j += 1
                    continue
                return False
            return False

        return dead_from(i + 1)

    # lea. `leaq d(,%i,s), %r` writes d + s*i to %r and nothing else (no flags, no memory). With base registers:
    # s = 1: `leaq d(%i), %r`; s = 2: `leaq d(%i,%i), %r`; s = 4: `leaq (%i,%i), %r` then `leaq d(%r,%r), %r`;
    # s = 8: `leaq (%i,%i), %r`, `leaq (%r,%r), %r`, `leaq d(%r,%r), %r`. Each step reads only %i or the %r the
    # previous step wrote, so %r ends as d + s*i (mod 2^64) and nothing else is written. `leal d(,%i,s), %e` writes the
    # low 32 bits of d + s*i, zero-extended, to the 64-bit register of %e: the same steps as `leal` (the later ones with
    # that 64-bit register as base and index, holding the previous step's low 32 bits zero-extended) leave the low 32
    # bits of the same sum, as the low 32 bits of a sum or a double depend only on the low 32 bits of its operands.
    def lea(self, i, mn, ops):
        if mn not in ("leaq", "leal") or len(ops) != 2 or not reg(ops[1]):
            return None
        m = re.fullmatch(r"([^(]*)\(,(%\w+)(?:,(\d))?\)", ops[0])
        if not m or reg(m.group(2)) is None or (mn == "leaq") != (reg(ops[1]) == ops[1][1:]):
            return None
        d, ix, s, r = m.group(1), m.group(2), int(m.group(3) or 1), ops[1]
        r64 = f"%{reg(r)}"
        o = self.lines[i]
        steps = {1: [f"{d}({ix})"], 2: [f"{d}({ix},{ix})"], 4: [f"({ix},{ix})", f"{d}({r64},{r64})"],
                 8: [f"({ix},{ix})", f"({r64},{r64})", f"{d}({r64},{r64})"]}[s]
        return [ins(mn, a, r, rule="lea", orig=o) for a in steps]

    def run(self):
        # out[i]: the replacement of line i, a list of (text, rule, original); a single entry with rule None is the
        # line unchanged.
        out = {i: [(l, None, l)] for i, l in enumerate(self.lines)}
        for f in self.core:
            for i in self.body(f):
                c = parse(self.lines[i])
                if c:
                    new = self.got(i, *c)
                    if new:
                        out[i] = new
        for f in self.core:
            self.reg_calls(f, out)
        for f in self.core:
            no_red_zone = any((parse(self.lines[i]) or ("",))[0] in ("callq", "call") for i in self.body(f)) or not any(
                re.search(r"-\d+\(%rsp", self.lines[i].split("#", 1)[0]) for i in self.body(f))
            for i in self.body(f):
                c = parse(self.lines[i])
                if c and out[i][0][1] is None:
                    new = self.bt(i, *c, no_red_zone) or self.bts(i, *c, no_red_zone) or self.lea(i, *c)
                    if new:
                        out[i] = new
        bad = []
        for f in self.core:
            for i in self.body(f):
                for text, _, _ in out[i]:
                    c = parse(text)
                    if c and (re.fullmatch(r"bts?[wlq]?", c[0]) or any(
                            "@" in o or o.startswith("*") or re.match(r"[^(]*\(,", o) for o in c[1])):
                        bad.append(f"{i + 1}: {text.strip()}")
        if bad:
            sys.exit("x86-postpass: core instructions no rule applies to:\n" + "\n".join(bad))
        result = []
        for i in range(len(self.lines)):
            for text, rule, orig in out[i]:
                result.append(text if rule is None else f"{text}\t# postpass {rule}: {orig.split('#', 1)[0].strip()}")
        return result


def main():
    if len(sys.argv) not in (2, 3):
        sys.exit("usage: x86-postpass.py IN.s [OUT.s]")
    with open(sys.argv[1]) as fh:
        lines = fh.read().split("\n")
    text = "\n".join(Postpass(lines).run())
    if len(sys.argv) == 3:
        with open(sys.argv[2], "w") as fh:
            fh.write(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
