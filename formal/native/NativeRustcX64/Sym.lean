module

public import NativeRustcX64.Sym.Sound
public import NativeRustcX64.Sym.Simp
public import NativeRustcX64.Sym.Run
public import NativeRustcX64.Sym.Tactic

/-!
# The verified symbolic executor for Kraken's x86-64

`Sym.exec ds S` runs a basic block on a symbolic state (`NativeRustcX64.Sym.Exec`);
`Sym.exec_sound` makes its result a fact about the machine (`NativeRustcX64.Sym.Sound`);
`sym_block` computes the result as a literal, checked by the kernel (`NativeRustcX64.Sym.Tactic`);
`Match.read` and `sym_simp` read it (`NativeRustcX64.Sym.Simp`).
-/
