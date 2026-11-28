/-
  LeanVM.Dsl.Gen.Check

  Every translated function against `Expand`: its core functions, its loop helpers and its `Const`
  instances equal up to the numbering of values and the names of the loop helpers.
-/

import LeanVM.Dsl.Gen.Checks

/-!
# The translated guest against `Expand`

For each function `Expand` lowers as written, the core functions elaborated from its translation,
with its loop helpers and the `Const` instances it reaches, against those `Expand` makes from the
exported source (`Checks.check`, `Compare.sameProg`): both lists walked from the function through
its callees, loop helpers renamed in that order, values numbered by first occurrence.
-/

namespace LeanVM.Dsl.Gen.Check

open LeanVM.Dsl.Gen.Checks

#guard check "main"
#guard check "exponent_tables"
#guard check "g_power_of_word"
#guard check "assert_small_g_power"
#guard check "eq_prefix_chain"
#guard check "rs_eq_run"
#guard check "sumcheck_round4"
#guard check "opening_round"
#guard check "opening_tail_round"
#guard check "verify_bus_gkr"
#guard check "selector_run_nibbles"
#guard check "shared_selector_tables"
#guard check "verify_tables"
#guard check "verify_keccak"
#guard check "ring_switch_target"
#guard check "ring_switch_weight"
#guard check "certify_placement"
#guard check "selector_tables"
#guard check "check_opening_terminal"
#guard check "verify_sub"
#guard check "sp_wots"
#guard check "verify_sig_lean_sphincs"
#guard check "statement_digest"
#guard check "list_split"
#guard check "claim_list_digest"
#guard check "child_claim_list_digest"
#guard check "child_claim_list_any"
#guard check "child_claim_list_mono"
#guard check "da_verify"
#guard check "da_padding"
#guard check "da_verify_column"
#guard check "da_verify_cell"
#guard check "da_vector"
#guard check "da_column_offsets"
#guard check "aggregate_claims"

end LeanVM.Dsl.Gen.Check
