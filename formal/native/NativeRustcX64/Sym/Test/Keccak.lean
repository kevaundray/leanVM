module

public import NativeRustcX64.Code.Common.KeccakF.Names
public import NativeRustcX64.Code.Xmss.Names

public import NativeRustcX64.Sym
public import NativeRustcX64.Code.Common.KeccakF
public meta import NativeRustcX64.Code.Common.KeccakF

/-!
# The executor on `keccak_f`'s round loop

The loop body of rustc's x86-64 `keccak_f` (`NativeRustcX64.Common.KeccakF.b1`, one Keccak-f
round: 249 instructions from `.LKeccakF_1` to `jne .LKeccakF_1`, with stack traffic below and
above RSP and memory operands in `xor`), run from a state with its stack frame as region 0 (RSP
at offset 128, the red zone below it), the round-constant table (the label
`.Lanon.5ef9b7c546f4dc64388b910df55ec241.1`) as region 1, and the round counter at `24(%rsp)` a
literal.
-/

namespace NativeRustcX64.Sym.Test.Keccak

set_option Elab.async false

open NativeRustcX64.Common.KeccakF


/-- Before round `i`: RSP 128 bytes into the 256-byte frame, the counter `8 * i` at `24(%rsp)`,
the round constants region 1. -/
def atRound (i : Nat) : SState :=
  { init [256, 192] [(.rsp, .ptr 0 128)] [(NativeRustcX64.Xmss.Symbols.rodata0Label, 1)] with mem := [⟨0, 152, 8, .lit (8 * i)⟩] }

sym_block round0_exec := exec b1 (atRound 0)

sym_block round23_exec := exec b1 (atRound 23)

/-- The first round loops back, the last falls out. -/
example : (exec b1 (atRound 0)).map (·.2) = some (.cond (.lit true) NativeRustcX64.Common.KeccakF.label_1) := by
  rw [round0_exec]
  rfl

example : (exec b1 (atRound 23)).map (·.2) = some (.cond (.lit false) NativeRustcX64.Common.KeccakF.label_1) := by
  rw [round23_exec]
  rfl

/-- The machine runs a round from any state `atRound i` describes, to the state the executor
computed. -/
theorem round0_spec [Host] {k : Nat} (hk : b1.IsInfixAt Host.prog k) {env : Env}
    (hwf : env.WF) {m : MachineData} (hm : Match env (atRound 0) m) :
    Eventually (step1 Host.exe) (fun st =>
      Match env ((exec b1 (atRound 0)).map (·.1) |>.getD (atRound 0)) st.data ∧
      st.pc = Labels.label NativeRustcX64.Common.KeccakF.label_1) ⟨m, Host.addrOf k⟩ := by
  refine NativeRustcX64.Eventually.mono (exec_sound hk round0_exec hwf nofun hm)
    fun st ⟨hm', hpc⟩ => ⟨by rw [round0_exec]; exact hm', ?_⟩
  simp only [PcOk, SBool.eval, ite_true] at hpc
  exact hpc

end NativeRustcX64.Sym.Test.Keccak
