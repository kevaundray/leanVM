module

public import NativeRustcX64.Mem.Memcpy
public import NativeRustcX64.Mem.Memset
public import NativeRustcX64.KeccakF.Spec
public import NativeRustcX64.Hasher.Update
public import NativeRustcX64.Hasher.Finalize
public import NativeRustcX64.Sphincs
public import NativeRustcX64.Xmss
public import NativeRustcX64.Rodata

/-!
# The rustc-compiled verifiers on x86-64

The deployed `lean_xmss::verify` and `lean_sphincs::verify`, compiled by the pinned rustc
(`rustc/build.sh`) to x86-64 assembly and rewritten by `rustc/x86-postpass.py` into instructions
Kraken reads, ingested as Kraken programs (`NativeRustcX64.Code`, `rustc/ingest/`, checked against
the assembly by `rustc/ingest/faithful.sh`) and proved against Kraken's semantics function by
function: each function's contract (`NativeRustcX64.Spec`), proved from its blocks run by the
verified symbolic executor (`NativeRustcX64.Sym`) and its callees' contracts. The build fails if an
axiom footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeRustcX64.Mem.Memcpy.memcpy_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcX64.Mem.Memcpy.memcpy_spec

/-- info: 'NativeRustcX64.Mem.Memset.memset_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcX64.Mem.Memset.memset_spec

/-- info: 'NativeRustcX64.keccakF_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcX64.keccakF_spec

/-- info: 'NativeRustcX64.Hasher.Update.update_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcX64.Hasher.Update.update_spec

/-- info: 'NativeRustcX64.Hasher.Finalize.finalize_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcX64.Hasher.Finalize.finalize_spec

/-- info: 'NativeRustcX64.SphincsVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcX64.SphincsVerifier.verify_correct

/-- info: 'NativeRustcX64.XmssVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcX64.XmssVerifier.verify_correct

/-- info: 'NativeRustcX64.Xmss.rc_data' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcX64.Xmss.rc_data

/-- info: 'NativeRustcX64.Sphincs.rc_data' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcX64.Sphincs.rc_data

/-- info: 'NativeRustcX64.Sphincs.lh_data' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcX64.Sphincs.lh_data
