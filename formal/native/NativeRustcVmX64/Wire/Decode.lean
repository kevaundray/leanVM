module

public import NativeRustcVmX64.Wire.Decode.Loop
public import NativeRustcVmX64.Wire.Decode.Room

/-!
# `decode` meets its contract (x86-64)

`decode_spec`: the prologue and the stream's count (`entry_run`), the stream's words and the
phase count (`stream_run`), the phases and the cursor against the wire's length (`loop_run`);
every failed read or check leaves with AL `0` (`none_run`), as `decodeM` gives `none`.
-/

namespace NativeRustcVmX64.Wire.Decode

open NativeRustcX64 NativeRustcVmX64.Vm.Decode

public section

variable [Host] {k : Nat}

/-- **`decode` meets its contract.** -/
theorem decode_spec (hp : Placed code k)
    (hle : Spec (Labels.label readerLeLabel) ReaderLePre ReaderLePost)
    (hrw : Spec (Labels.label readerWordsLabel) ReaderWordsPre ReaderWordsPost)
    (hpm : Spec (Labels.label phaseMLabel) PhaseMPre PhaseMPost) :
    Spec (Labels.label decodeLabel) DecodePre DecodePost := by
  intro m0 hpre
  have G := geo_of hpre
  rw [hp.label (j := 0) (l := decodeLabel) rfl]
  refine Eventually.bind (entry_run hp G hle) fun s1 h1 ↦ ?_
  rcases h1 with h1 | ⟨n, h1⟩
  · exact .done _ h1
  refine Eventually.bind (stream_run hp G hle hrw h1) fun s2 h2 ↦ ?_
  rcases h2 with h2 | ⟨ws, p, h2⟩
  · exact .done _ h2
  exact loop_run hp G hpm h2

end

end NativeRustcVmX64.Wire.Decode
