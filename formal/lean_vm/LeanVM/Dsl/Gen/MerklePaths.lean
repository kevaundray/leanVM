/-
  LeanVM.Dsl.Gen.MerklePaths

  The guest's section `MerklePaths`, translated.
-/

module

public import LeanVM.Dsl.Gen.Inline

namespace LeanVM.Dsl.Gen

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

@[expose] public section

set_option linter.unusedVariables false in
/-- `verify_merkle_cap`, a `Const` family (`guests/lean_ethereum.py`, line 1154):

```
def verify_merkle_cap(cap, flags, depth: Const):
    # Unrolled over the cap's nodes, so every address is an immediate. Every node's
    # hinted digest (node k at heap cells 2k, 2k+1) is read once into a frame run,
    # node k at cells 2(k - 1) and 2k - 1, where an internal node's hash writes its
    # digest, landing on (and so asserting) the hinted value. An active (flagged)
    # node is hashed; an inactive one pins its children's flags to zero, so every
    # active node's parent is active too, up to the root, which is always hashed.
    # The queries flag the parents of the cap leaves they reach. The run is sized
    # per depth, the cap depths a configuration reaches.
    if depth != 0:
        n_leaves = 2 ** depth
        if const(depth == 4):
            runs = StackBuf(4 * 16 - 2)
        elif const(depth == 5):
            runs = StackBuf(4 * 32 - 2)
        elif const(depth == 6):
            runs = StackBuf(4 * 64 - 2)
        elif const(depth == 7):
            runs = StackBuf(4 * 128 - 2)
        else:
            runs = StackBuf(4 * 256 - 2)
        for node in unroll(1, 2 * n_leaves):
            at = 2 * (node - 1)
            runs[at] = cap[GEN ** (2 * node)]
            runs[at + 1] = cap[GEN ** (2 * node + 1)]
        for node in unroll(1, n_leaves):
            left = 2 * (2 * node - 1)
            right = left + 2
            at = 2 * (node - 1)
            if const(node == 1):
                keccak(runs[left:left + 2], runs[right:right + 2], runs[at:at + 2])
            else:
                if flags[GEN ** node] != 0:
                    keccak(runs[left:left + 2], runs[right:right + 2], runs[at:at + 2])
                else:
                    if const(2 * node // n_leaves == 0):  # node has flagged children
                        flags[GEN ** (2 * node)] = 0
                        flags[GEN ** (2 * node + 1)] = 0
        root_0 = runs[0]
        root_1 = runs[1]
    else:
        root_0 = cap[GEN ** 2]
        root_1 = cap[GEN ** 3]
    return root_0, root_1
```
-/
def verifyMerkleCap (depth : Nat) : GFn where
  name := instName "verify_merkle_cap" [.L depth]
  arity := 2
  rets := 2
  body ps := do
    let cap := cellOf ps 0
    let flags := cellOf ps 1
    let mut root0 : Word := default
    let mut root1 : Word := default
    if depth ≠ 0 then
      let nLeaves := 2 ^ depth
      let mut runs : List V := default
      if depth = 4 then
        runs ← B.stackBuf 62
      else
        if depth = 5 then
          runs ← B.stackBuf 126
        else
          if depth = 6 then
            runs ← B.stackBuf 254
          else
            if depth = 7 then
              runs ← B.stackBuf 510
            else
              runs ← B.stackBuf 1022
      let mut at' : Nat := default
      for node_k in [1:2 * nLeaves] do
        at' := 2 * (node_k - 1)
        B.loadInto (cellOf runs at') cap (2 * node_k)
        B.loadInto (cellOf runs (at' + 1)) cap ((2 * node_k) + 1)
      for node_k in [1:nLeaves] do
        let left := 2 * ((2 * node_k) - 1)
        let right := left + 2
        at' := 2 * (node_k - 1)
        if node_k = 1 then
          B.keccak (a := (.cells (.frame ((runs.drop left).take ((left + 2) - left))))) (b := (.cells (.frame ((runs.drop right).take ((right + 2) - right))))) (out := (.frame ((runs.drop at').take ((at' + 2) - at'))))
        else
          let t0 ← B.load flags node_k
          let _ ← B.ite t0
            (do
              if ((2 * node_k) / nLeaves) = 0 then
                B.store flags (2 * node_k) (← B.const 0)
                B.store flags ((2 * node_k) + 1) (← B.const 0)
              else
                pure ())
            (do
              B.keccak (a := (.cells (.frame ((runs.drop left).take ((left + 2) - left))))) (b := (.cells (.frame ((runs.drop right).take ((right + 2) - right))))) (out := (.frame ((runs.drop at').take ((at' + 2) - at')))))
          pure ()
      root0 := cellOf runs 0
      root1 := cellOf runs 1
    else
      root0 ← B.load cap 2
      root1 ← B.load cap 3
    return [.v root0.v] ++ [.v root1.v]

end
end LeanVM.Dsl.Gen
