/-
  LeanVM.Guest.Program.MerklePaths

  The guest's section "Merkle paths".
-/

module

public import LeanVM.Guest.Program.MultilinearPrimitives

/-!
# Merkle paths
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

/-- Unrolled over the cap's nodes, so every address is an immediate. Every node's hinted digest (node k at heap cells 2k, 2k+1) is read once into a frame run, node k at cells 2(k - 1) and 2k - 1, where an internal node's hash writes its digest, landing on (and so asserting) the hinted value. An active (flagged) node is hashed; an inactive one pins its children's flags to zero, so every active node's parent is active too, up to the root, which is always hashed. The queries flag the parents of the cap leaves they reach. The run is sized per depth, the cap depths a configuration reaches. -/
def verifyMerkleCap (depth : Nat) : GFn where
  name := instName "verify_merkle_cap" [.L depth]
  arity := 2
  rets := 2
  body ps := do
    let cap := ps[0]
    let flags := ps[1]
    let mut root0 : Word := default
    let mut root1 : Word := default
    if depth ≠ 0 then
      let nLeaves := 2 ^ depth
      let mut runs : List V := default
      if depth = 4 then
        runs ← B.stackBuf 62
      else if depth = 5 then
        runs ← B.stackBuf 126
      else if depth = 6 then
        runs ← B.stackBuf 254
      else if depth = 7 then
        runs ← B.stackBuf 510
      else
        runs ← B.stackBuf 1022
      let mut at' : Nat := default
      for node in [1:2 * nLeaves] do
        at' := 2 * (node - 1)
        runs[at'] := cap[GEN ^ (2 * node)]
        runs[at' + 1] := cap[GEN ^ (2 * node + 1)]
      for node in [1:nLeaves] do
        let left := 2 * (2 * node - 1)
        let right := left + 2
        at' := 2 * (node - 1)
        if node = 1 then
          B.keccak runs[left:left + 2] runs[right:right + 2] runs[at':at' + 2]
        else
          let t0 ← val flags[GEN ^ node]
          let _ ← B.ite t0
            (do
              if 2 * node / nLeaves = 0 then  -- node has flagged children
                flags[GEN ^ (2 * node)] := 0
                flags[GEN ^ (2 * node + 1)] := 0)
            (do
              B.keccak runs[left:left + 2] runs[right:right + 2] runs[at':at' + 2])
          pure ()
      root0 := runs[0]
      root1 := runs[1]
    else
      root0 ← val cap[GEN ^ 2]
      root1 ← val cap[GEN ^ 3]
    return [.v root0.v, .v root1.v]

end
end LeanVM.Guest.Program
