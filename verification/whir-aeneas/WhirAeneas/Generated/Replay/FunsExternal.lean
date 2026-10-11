module
public import WhirAeneas.Generated.Replay.Types
public import WhirAeneas.Std.Bulk
public import WhirAeneas.Std.Replay
@[expose] public section
open Aeneas Aeneas.Std Result

namespace ReplaySource

/-- `FromUniform for F192`: the 24 squeezed bytes as three little-endian limbs, lowest first.
    `sample_queries_ordered` passes it in the `Challenger` dictionary of `verifier_message::<F192>`.
    The source body (`as_chunks`, `array::from_fn`) is outside the backend's library, so its content is stated here. -/
@[rust_fun
  "fiat_shamir::codec::{fiat_shamir::codec::FromUniform<primitives::field::gf2_64x3::F192, [u8; 24]>}::from_uniform"]
def primitives.field.gf2_64x3.F192.Insts.Fiat_shamirCodecFromUniformArrayU824.from_uniform
    (repr : Array Std.U8 24#usize) : Result primitives.field.gf2_64x3.F192 :=
  let limb (k : Nat) : Std.U64 :=
    ⟨BitVec.ofNat 64 ((List.range 8).foldl
      (fun acc i => acc + (repr.val.getD (8 * k + i) 0#u8).val * 256 ^ i) 0)⟩
  .ok { c0 := limb 0, c1 := limb 1, c2 := limb 2 }

end ReplaySource
