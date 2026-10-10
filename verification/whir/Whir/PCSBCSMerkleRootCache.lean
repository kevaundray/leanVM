import Whir.PCSBCSMerkleQueryLog

/-! At the commitment/oracle-message boundary, first registration freezes the
CURRENT public-query prefix and its full extracted table. This API is called by
the causal caller, not with a final transcript log. Repeat announcements/clones
retain the literal same prefix and table; later fresh queries do not fill absent
rows retroactively. Agreement with later openings is charged by OpenPrimitiveBad. -/
namespace Whir.PCSBCSMerkleRootCache
open Concrete FiatShamirGame PublicMerkleLog MerkleQueryLogExtraction PCSBCSMerkleQueryLog

structure Shape where
  height : Nat
  occupied : Nat

structure Frozen where
  shape : Shape
  queryPrefix : PublicLog
  raw : Array (Array K)

abbrev Registry := Std.ExtHashMap Key Frozen

/-- `queryPrefix` is already public at the announcement. It is retained by
reference, not recopied; extraction never consults later answers. -/
def freeze (queryPrefix : PublicLog) (root : Digest32) (shape : Shape) : Frozen :=
  ⟨shape,queryPrefix,rawRoot0 queryPrefix root shape.height shape.occupied⟩

theorem freeze_prefix (queryPrefix : PublicLog) (root : Digest32) (shape : Shape) :
    (freeze queryPrefix root shape).queryPrefix = queryPrefix := rfl

/-- Runtime branches BEFORE invoking extraction; existing roots do no work. -/
def register (registry : Registry) (log : PublicLog) (root : Digest32) (shape : Shape) : Registry :=
  match registry[key root]? with
  | some _ => registry
  | none => registry.insert (key root) (freeze log root shape)

theorem register_existing (registry : Registry) (log : PublicLog) (root : Digest32)
    (shape : Shape) (frozen : Frozen) (known : registry[key root]? = some frozen) :
    register registry log root shape = registry := by simp [register,known]

theorem register_preserves (registry : Registry) (log : PublicLog) (root other : Digest32)
    (shape : Shape) (frozen : Frozen) (known : registry[key root]? = some frozen) :
    (register registry log other shape)[key root]? = some frozen := by
  unfold register
  split
  next => exact known
  next miss =>
    rw [Std.ExtHashMap.getElem?_insert]
    split
    next eq =>
      have hk : key other = key root := by simpa using eq
      rw [hk,known] at miss
      contradiction
    next => exact known

theorem register_first (registry : Registry) (log : PublicLog) (root : Digest32)
    (shape : Shape) (absent : registry[key root]? = none) :
    (register registry log root shape)[key root]? = some (freeze log root shape) := by
  simp [register,absent]

theorem freeze_shape (log : PublicLog) (root : Digest32) (shape : Shape) :
    (freeze log root shape).raw.size = 2^shape.height ∧
    ∀ row ∈ (freeze log root shape).raw.toList, row.size = shape.occupied := by
  exact rawRoot0_shape log root shape.height shape.occupied

end Whir.PCSBCSMerkleRootCache
