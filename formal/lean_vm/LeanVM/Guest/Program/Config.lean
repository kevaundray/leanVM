/-
  LeanVM.Guest.Program.Config

  The guest's constants: the configuration's, from the placeholders the prover computes, and the protocol's own.
-/

module

public import LeanVM.Guest.Data.Placeholders

/-!
# The guest's constants

Every constant the guest names. A configuration constant is the placeholder of the same name (`LeanVM.Guest.Placeholders`, `placeholder_map` in `crates/aggregation/src/placeholders.rs` at the bytecode's log size), so one guest serves every inner shape; the others are the protocol's layout, defined here.
-/

namespace LeanVM.Guest.Program

@[expose] public section

/-! ## Proof stream -/

/-! The proof stream rides ONE padded witness hint (the guest walks only the prefix the shape dictates); binding always comes from the per-word absorbs. -/

def STREAM_CAP : Nat := LeanVM.Guest.Placeholders.STREAM_CAP
def MIN_LOG_MEM : Nat := LeanVM.Guest.Placeholders.MIN_LOG_MEM
def MAX_LOG_MEM : Nat := LeanVM.Guest.Placeholders.MAX_LOG_MEM
def INV_GEN : Nat := LeanVM.Guest.Placeholders.INV_GEN

/-! ## The field, GF(2^128) -/

/-! Tower F128 = F64[Y]/(Y^2+x*Y+1). Y_TOWER embeds Y for reassembling a word lo + hi*Y, and Y_INV = Y + x splits a word into its limbs once the low one is hinted. COORD_BASIS is the coordinate basis e_i of F128 (which spans the WHOLE field, unlike the g-power basis GEN**i, which spans only F64): hint_decompose_bits emits a word's coordinate bits, so a value reconstructs as Σ b_i·COORD_BASIS[i]. -/

def FIELD_BITS : Nat := 128

/-! A query position's path bits are dispatched on QW at a time (`walk_path`), and the windows one squeezed word's positions take fill at most QUERY_WINDOWS_CAP cells (`decode_query_windows`). -/

def QW : Nat := LeanVM.Guest.Placeholders.QW
def QUERY_WINDOWS_CAP : Nat := LeanVM.Guest.Placeholders.QUERY_WINDOWS_CAP
def BASE_FIELD_BITS : Nat := 64
def Y_TOWER : Nat := LeanVM.Guest.Placeholders.Y_TOWER
def Y_INV : Nat := LeanVM.Guest.Placeholders.Y_INV
def COORD_BASIS : List (Nat × Nat) := LeanVM.Guest.Placeholders.COORD_BASIS

/-! Phi, the F2-linear map that batches the 64 ring-switch slice claims, is drawn as two rows of RING_MAP_WIDTH challenges, f_p then g_b. RING_W[p] = x^(-2^(64 - 8p)), the inverse of the target's Horner point z_p. -/

def RING_MAP_WIDTH : Nat := 8
def RING_W : List (Nat × Nat) := LeanVM.Guest.Placeholders.RING_W
/-- ring-switch rows (target) or coordinates (weight) per loop iteration -/
def RS_CHUNK : Nat := 8
def RS_CHUNK_BITS : Nat := 3
/-- residual queries per loop iteration -/
def RES_BATCH : Nat := 8
/-- a ring-switch coordinate count is below 2^RS_COUNT_BITS -/
def RS_COUNT_BITS : Nat := 6

/-! Exponent bit-widths, wider than the 2^30 caps need: a count's log is below COUNT_BITS; a structural size (sums of 2^kappa, packing offsets) fits SIZE_BITS bits; and a structural LOG announced as an integer word (log_mem, log_inv_rate), raised to a g-power by g_power_of_word, is below SIZE_BITS, so LOG_WORD_BITS bits make the reconstruction the bound (a larger log cannot reproduce itself from them). -/

def COUNT_BITS : Nat := 33
def SIZE_BITS : Nat := 34
def LOG_WORD_BITS : Nat := 6

/-! ## Fiat-Shamir -/

/-! An absorbed scalar's fourth lane is its domain tag (fs_pack), so a role is never smuggled through the data lanes. The capacity a sponge carries is FS_CELLS cells. -/

def DS_OBSERVE : Nat := 1
def DS_POW_NONCE : Nat := 4
def FS_CELLS : Nat := 5

/-! ## Loop-carried chains -/

/-! A loop whose state is several fields keeps ONE heap run of N cells per iteration, so a step is one pointer multiply rather than one per field. -/

/-- a two-field chain -/
def PAIR_SLOTS : Nat := 2

/-! A record's Fiat-Shamir sponge is its FS_CELLS capacity cells, from field *_FS on. A sponge with a full rate waiting: its capacity, then those eight rate cells. -/

def PEND_SLOTS : Nat := 13

/-! One sumcheck round of the bus GKR or the table batch. -/

def ROUND_FS : Nat := 0
def ROUND_CURSOR : Nat := 5
def ROUND_CLAIM : Nat := 6
def ROUND_SLOTS : Nat := 7

/-! One product layer of the bus GKR. -/

def LAYER_FS : Nat := 0
def LAYER_CURSOR : Nat := 5
/-- the trees' claims, N_GKR_TREES of them -/
def LAYER_VALS : Nat := 6
def LAYER_ROW : Nat := 9
def LAYER_POS : Nat := 10
/-- g^(k // 4) at radix-four layer k -/
def LAYER_HALF : Nat := 11
/-- g^(k % 4) -/
def LAYER_PARITY : Nat := 12
def LAYER_SLOTS : Nat := 13

/-! ## The bus: sides and blocks -/

/-! Bus sides, whose blocks the layout gives, and the GKR's trees, one a side: push and pull under the fingerprint (fp_w, beta), then count, whose tuples weigh the count alone, at beta = 0. MU_CAP caps a GKR point row (`verify_bus_gkr`). -/

def PUSH_SIDE : Nat := 0
def PULL_SIDE : Nat := 1
def COUNT_SIDE : Nat := 2
def N_GKR_SIDES : Nat := 3
def N_GKR_TREES : Nat := N_GKR_SIDES
def MU_CAP : Nat := LeanVM.Guest.Placeholders.MU_CAP

/-! Bus blocks, flattened across the 3 sides (side s covers blocks [SIDE_BLOCK_START[s], SIDE_BLOCK_START[s+1])). The block STRUCTURE is protocol-fixed and baked: each block's coord range [BLOCK_COORD_OFF, +BLOCK_COORD_COUNT), per coord its COORD_TYPE kind (mirroring leaf.rs::Coord), COORD_CONST (the const value, a product's or gcol's g^k, else 0), and the kappa SOURCE map (BLOCK_KAPPA_SRC/ADJ: 0 = const adj, 1 = log_mem, 2+t = tau_t). The block SHAPES are all reconstructed at runtime from the certified logs: kappa directly, the selector bits by pinned advice-decompositions. BLOCK_TABLE names the table a block's flush belongs to, or NO_TABLE for the framework blocks (boundary, memory seed/finalize, bytecode seed/finalize); it is also what marks a block as owned, an owned block's fingerprint being settled by the table sumcheck off its table's column evaluations. -/

def COORD_KIND_CONST : Nat := 0
def COORD_KIND_COL : Nat := 1
def COORD_KIND_GCOL : Nat := 2
def COORD_KIND_INDEX : Nat := 3
def COORD_KIND_PUBLIC : Nat := 4
def COORD_KIND_PROD : Nat := 5
def NO_TABLE : Nat := LeanVM.Guest.Placeholders.NO_TABLE
def SIDE_BLOCK_START : List (Nat × Nat) := LeanVM.Guest.Placeholders.SIDE_BLOCK_START
def N_BLOCKS : Nat := LeanVM.Guest.Placeholders.N_BLOCKS
def N_COORDS : Nat := LeanVM.Guest.Placeholders.N_COORDS
def BLOCK_KAPPA_SRC : List (Nat × Nat) := LeanVM.Guest.Placeholders.BLOCK_KAPPA_SRC
def BLOCK_KAPPA_ADJ : List (Nat × Nat) := LeanVM.Guest.Placeholders.BLOCK_KAPPA_ADJ
def BLOCK_TABLE : List (Nat × Nat) := LeanVM.Guest.Placeholders.BLOCK_TABLE
def BLOCK_SIDE : List (Nat × Nat) := LeanVM.Guest.Placeholders.BLOCK_SIDE
def N_BLOCK_GROUPS : Nat := LeanVM.Guest.Placeholders.N_BLOCK_GROUPS
/-- a block group's first block, then N_BLOCKS -/
def BLOCK_GROUP_START : List (Nat × Nat) := LeanVM.Guest.Placeholders.BLOCK_GROUP_START
/-- a side's first block group, then N_BLOCK_GROUPS -/
def SIDE_GROUP_START : List (Nat × Nat) := LeanVM.Guest.Placeholders.SIDE_GROUP_START
def BLOCK_COORD_OFF : List (Nat × Nat) := LeanVM.Guest.Placeholders.BLOCK_COORD_OFF
def BLOCK_COORD_COUNT : List (Nat × Nat) := LeanVM.Guest.Placeholders.BLOCK_COORD_COUNT
def COORD_TYPE : List (Nat × Nat) := LeanVM.Guest.Placeholders.COORD_TYPE
def COORD_CONST : List (Nat × Nat) := LeanVM.Guest.Placeholders.COORD_CONST

/-! A table coord's value on its table's padding row (doc sec:e2e-pad), zero for a framework coord: a block's rows past its table's announced count flush nothing, their leaves being 1, so the decompose adds back what its form sums there. -/

def COORD_PADDING : List (Nat × Nat) := LeanVM.Guest.Placeholders.COORD_PADDING

/-! Claim dedup: push/pull share their GKR point, so a column read by two blocks with the same kappa (across OR within the sides) is streamed and opened ONCE. COORD_FRESH = 1 on the first occurrence (read the stream, fill pool slot COORD_CLAIM_SLOT), 0 on a duplicate (reuse that slot). -/

def COORD_FRESH : List (Nat × Nat) := LeanVM.Guest.Placeholders.COORD_FRESH
/-- a fresh coordinate's place among the words the decomposition absorbs -/
def COORD_FRESH_POS : List (Nat × Nat) := LeanVM.Guest.Placeholders.COORD_FRESH_POS
def N_FRESH : Nat := LeanVM.Guest.Placeholders.N_FRESH
def COORD_CLAIM_SLOT : List (Nat × Nat) := LeanVM.Guest.Placeholders.COORD_CLAIM_SLOT

/-! A TABLE block's coordinates, flattened into TERMS: coord c is Σ_{j < COORD_TERM_COUNT[c]} term(COORD_TERM_OFF[c] + j), each term a TERM_TYPE kind over that table's LOCAL column indices TERM_COL_A/TERM_COL_B, scaled by TERM_CONST. Those coords raise no claim (the table sumcheck settles them), which is what lets one carry a value the row DERIVES from its columns: an XOR/MUL result, a DEREF store, a JUMP successor. A framework coord has no terms. -/

def COORD_TERM_OFF : List (Nat × Nat) := LeanVM.Guest.Placeholders.COORD_TERM_OFF
def COORD_TERM_COUNT : List (Nat × Nat) := LeanVM.Guest.Placeholders.COORD_TERM_COUNT
def TERM_TYPE : List (Nat × Nat) := LeanVM.Guest.Placeholders.TERM_TYPE
def TERM_CONST : List (Nat × Nat) := LeanVM.Guest.Placeholders.TERM_CONST
def TERM_COL_A : List (Nat × Nat) := LeanVM.Guest.Placeholders.TERM_COL_A
def TERM_COL_B : List (Nat × Nat) := LeanVM.Guest.Placeholders.TERM_COL_B
/-- a pull coordinate less its push twin's, as terms -/
def COORD_DIFF_OFF : List (Nat × Nat) := LeanVM.Guest.Placeholders.COORD_DIFF_OFF
def COORD_DIFF_COUNT : List (Nat × Nat) := LeanVM.Guest.Placeholders.COORD_DIFF_COUNT
def N_BUS_CLAIMS : Nat := LeanVM.Guest.Placeholders.N_BUS_CLAIMS
/-- 1 + g^(2^i) -/
def INDEX_MLE_FACTORS : List (Nat × Nat) := LeanVM.Guest.Placeholders.INDEX_MLE_FACTORS

/-! Committed-coordinate claims (Col/GCol coords across all sides) and the deferred bytecode values (Public coords). -/

def N_CLAIMS : Nat := LeanVM.Guest.Placeholders.N_CLAIMS

/-! A bus tuple's coordinates index the 2^N_TUPLE_BITS fingerprint slots, a weight each (doc sec:gp). The stacked bytecode has BYTECODE_COLS encoding columns, stacked along LOG2_BYTECODE_COLS selector bits into ONE multilinear; push and pull share their GKR point, so the columns are opened ONCE. -/

def N_TUPLE_BITS : Nat := 4
def N_TUPLE_SLOTS : Nat := 16
def BYTECODE_COLS : Nat := LeanVM.Guest.Placeholders.BYTECODE_COLS
def LOG2_BYTECODE_COLS : Nat := LeanVM.Guest.Placeholders.LOG2_BYTECODE_COLS

/-! ## The six tables -/

/-! The table sumcheck's batch carries EVERY committed column of a table, because its bus forms read the flushed ones and its constraint the rest; TABLE_COLS_CAP caps the evaluation frame. ETA_OFFSET[t] starts table t's disjoint range of zc_xi powers; the bus forms take ETA_FORM_BASE + tree, the SAME N_GKR_TREES powers for every table, and that sharing is what makes the batch's target derivable from the trees' leaf claims. FLOORS[t] is the table's least log height (the Keccak reduction is sized for at least one block of 2^9 steps). -/

def TABLE_JUMP : Nat := 4
def TABLE_KECCAK : Nat := 5
def N_TABLES : Nat := LeanVM.Guest.Placeholders.N_TABLES
def FLOORS : List (Nat × Nat) := LeanVM.Guest.Placeholders.FLOORS
def N_TABLE_COLS : List (Nat × Nat) := LeanVM.Guest.Placeholders.N_TABLE_COLS
/-- a table's first column among all the evaluations -/
def TABLE_COL_BASE : List (Nat × Nat) := LeanVM.Guest.Placeholders.TABLE_COL_BASE
def N_COL_EVALS : Nat := LeanVM.Guest.Placeholders.N_COL_EVALS
def TABLE_COLS_CAP : Nat := LeanVM.Guest.Placeholders.TABLE_COLS_CAP
def ETA_OFFSET : List (Nat × Nat) := LeanVM.Guest.Placeholders.ETA_OFFSET
def ETA_FORM_BASE : Nat := LeanVM.Guest.Placeholders.ETA_FORM_BASE
def N_ETA_POWS : Nat := LeanVM.Guest.Placeholders.N_ETA_POWS

/-! ## Keccak, by GKR over its rounds -/

/-! q_keccak holds a step's state every KECCAK_DEPTH rounds but its output, a lane per slot and a word per step; a pack is KECCAK_PACK consecutive steps, embedded in a polynomial of degree under KECCAK_EMBED_BITS whose products have KECCAK_PROD_BITS coefficients. The *_START / *_IDX pairs are index lists: row i is IDX[START[i] .. START[i + 1]]. -/

def KECCAK_DEPTH : Nat := LeanVM.Guest.Placeholders.KECCAK_DEPTH
def KECCAK_SEGMENTS : Nat := LeanVM.Guest.Placeholders.KECCAK_SEGMENTS
def KECCAK_SEG_LOG : Nat := LeanVM.Guest.Placeholders.KECCAK_SEG_LOG
def KECCAK_PACK : Nat := LeanVM.Guest.Placeholders.KECCAK_PACK
def KECCAK_PACK_LOG : Nat := 4
def KECCAK_EMBED_BITS : Nat := LeanVM.Guest.Placeholders.KECCAK_EMBED_BITS
def KECCAK_PROD_BITS : Nat := LeanVM.Guest.Placeholders.KECCAK_PROD_BITS
def KECCAK_PROJ_A : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_PROJ_A
def KECCAK_PROJ_B : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_PROJ_B
def KECCAK_PROJ_OUT : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_PROJ_OUT
def KECCAK_PROJ_CELLS : Nat := LeanVM.Guest.Placeholders.KECCAK_PROJ_CELLS
def KECCAK_FAC_START : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_FAC_START
def KECCAK_FAC_IDX : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_FAC_IDX
def KECCAK_FAC_DEG : Nat := LeanVM.Guest.Placeholders.KECCAK_FAC_DEG
def KECCAK_EMB_A : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_EMB_A
def KECCAK_EMB_B : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_EMB_B
def KECCAK_EMB_OUT : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_EMB_OUT
def KECCAK_FAC_N : Nat := LeanVM.Guest.Placeholders.KECCAK_FAC_N
def KECCAK_EMB_CELLS : Nat := LeanVM.Guest.Placeholders.KECCAK_EMB_CELLS
def KECCAK_IOTA_START : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_IOTA_START
def KECCAK_IOTA_IDX : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_IOTA_IDX
def KECCAK_PI : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_PI
def KECCAK_RHO : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_RHO
def KECCAK_SHIFT_USED : List (Nat × Nat) := LeanVM.Guest.Placeholders.KECCAK_SHIFT_USED
def KECCAK_LANES : Nat := 25
/-- a bit position is z + 64 * lane -/
def KECCAK_Z_BITS : Nat := 6
def KECCAK_LANE_BITS : Nat := 5
def KECCAK_LOCAL_BITS : Nat := KECCAK_Z_BITS + KECCAK_LANE_BITS
/-- where a frame eqtree's last level starts -/
def LANE_OFF : Nat := 2 ^ KECCAK_LANE_BITS - 2
/-- iota flips slices 2^i - 1 of lane 0 only -/
def KECCAK_IOTA_BITS : Nat := 7
def QKECCAK_SLOT_LOG : Nat := LeanVM.Guest.Placeholders.QKECCAK_SLOT_LOG

/-! A claim's record: its value, the sum of its instance weights, pointers to its point, its lane table, the local point whose slice coordinates' eq is its slice table, and its weight on each position iota can flip (slice 2^i - 1 of lane 0), then the instance weights. -/

def KC_VALUE : Nat := 0
def KC_KAPPA : Nat := 1
def KC_POINT : Nat := 2
def KC_LANES : Nat := 3
def KC_LOCAL : Nat := 4
def KC_FLIPS : Nat := 5
def KC_MU : Nat := 6
def KC_SIZE : Nat := KC_MU + KECCAK_PACK

/-! One round of a layer's sumcheck over packs and segments. -/

def KR_FS : Nat := 0
def KR_CURSOR : Nat := 5
def KR_CLAIM : Nat := 6
def KR_SLOTS : Nat := 7

/-! A layer's round records lie field by field, KR_CAP apart, one per KR_STEP rounds and one per round of the remainder after the first: a layer has tau - 3 < 32 rounds, so at most 1 + 3 + 7 of them. -/

def KR_STEP_LOG : Nat := 3
def KR_STEP : Nat := 2 ^ KR_STEP_LOG
def KR_CAP : Nat := 11

/-! ## The stacked WHIR opening -/

/-! The opening is dispatched by the certified committed log-size m through `match`, one arm per m, and by the announced rate inside it. The LIG_* tables carry one row per (rate, m), emitted from the same level_shapes the prover uses: scalars index as TBL[m_idx], per-level values as TBL[m_idx * LIG_MAX_LEVELS + lvl], where m_idx is the rate-major candidate index rate * LIG_N_LOG_SIZES + m - LIG_MIN_LOG_SIZE. -/

def LIG_MIN_LOG_SIZE : Nat := LeanVM.Guest.Placeholders.LIG_MIN_LOG_SIZE
def LIG_N_LOG_SIZES : Nat := LeanVM.Guest.Placeholders.LIG_N_LOG_SIZES
def LIG_N_RATES : Nat := LeanVM.Guest.Placeholders.LIG_N_RATES

/-! Committed-column kappa sources (0 = const COL_KAPPA_ADJ, 1 = log_mem, 2+t = tau_t) and the PCS floor for the stacked size. -/

def N_COMMITTED_COLS : Nat := LeanVM.Guest.Placeholders.N_COMMITTED_COLS
def N_COLUMN_LOGS : Nat := LeanVM.Guest.Placeholders.N_COLUMN_LOGS
def COL_KAPPA_SRC : List (Nat × Nat) := LeanVM.Guest.Placeholders.COL_KAPPA_SRC
def COL_KAPPA_ADJ : List (Nat × Nat) := LeanVM.Guest.Placeholders.COL_KAPPA_ADJ
def N_COL_GROUPS : Nat := LeanVM.Guest.Placeholders.N_COL_GROUPS
/-- a column group's first column, then N_COMMITTED_COLS -/
def COL_GROUP_START : List (Nat × Nat) := LeanVM.Guest.Placeholders.COL_GROUP_START
def PCS_MIN_MU : Nat := LeanVM.Guest.Placeholders.PCS_MIN_MU

/-! Global maxima; StackBuf frame sizes are parse-time, so they must be baked. -/

def LIG_MAX_LEVELS : Nat := LeanVM.Guest.Placeholders.LIG_MAX_LEVELS

/-! A rate's tables follow the previous rate's, every size and level of it. -/

def LIG_RATE_STRIDE : Nat := LIG_N_LOG_SIZES * LIG_MAX_LEVELS
def YR_LOG_CAP : Nat := LeanVM.Guest.Placeholders.YR_LOG_CAP

/-! The opening's grinding (pcs::whir_config): before each fold round's (alpha, beta), before every commitment's OOD point, before every level's queries (a non-final level's lambda rides that message), and before level 0's batching, the ring switch's map. -/

def FOLD_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.FOLD_GRIND_BITS
def OOD_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.OOD_GRIND_BITS
def QUERY_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.QUERY_GRIND_BITS
def BATCH_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.BATCH_GRIND_BITS

/-! Every other challenge grinds for its numerator (fiat_shamir::grinding_bits), zero bits being no nonce at all: the bus fingerprint by the push depth mu, BUS_GRIND_BITS[mu], never zero at an admitted depth; a sumcheck round for its degree d, eq factor included, as ROUNDd (the opening's tail and a Keccak opening's are degree 2, the table sumcheck's and a Keccak layer's degree 3, a bus GKR round degree 5); the GKR's combiner, its y (a binary layer's, a radix-four one's, the last layer's, read by the zerocheck too); the table sumcheck's xi; and the Keccak reduction's first message (its segment and lane), its s and its beta. -/

def BUS_GRIND_BITS : List (Nat × Nat) := LeanVM.Guest.Placeholders.BUS_GRIND_BITS
/-- the least push depth of an execution of this bytecode -/
def BUS_MIN_MU : Nat := LeanVM.Guest.Placeholders.BUS_MIN_MU
/-- the bus depths from BUS_MIN_MU, below SIZE_BITS -/
def BUS_GRIND_ARMS : Nat := SIZE_BITS - BUS_MIN_MU
def ROUND2_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.ROUND2_GRIND_BITS
def ROUND3_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.ROUND3_GRIND_BITS
def ROUND5_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.ROUND5_GRIND_BITS
def GKR_COMBINER_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.GKR_COMBINER_GRIND_BITS
def GKR_Y1_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.GKR_Y1_GRIND_BITS
def GKR_Y_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.GKR_Y_GRIND_BITS
def GKR_Y_LAST_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.GKR_Y_LAST_GRIND_BITS
def XI_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.XI_GRIND_BITS
def KECCAK_SEG_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.KECCAK_SEG_GRIND_BITS
def KECCAK_S_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.KECCAK_S_GRIND_BITS
def KECCAK_BETA_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.KECCAK_BETA_GRIND_BITS
def BATCH_LAM_GRIND_BITS : Nat := LeanVM.Guest.Placeholders.BATCH_LAM_GRIND_BITS
/-- the batching challenge's nonce, if it grinds -/
def BC_LAM_WORDS : Nat := LeanVM.Guest.Placeholders.BC_LAM_WORDS
/-- a batching round's (g1, g_inf), then its nonce, if it grinds -/
def BC_ROUND_WORDS : Nat := LeanVM.Guest.Placeholders.BC_ROUND_WORDS

/-! A level's high part has at most 2^HIGH_BITS_CAP coefficients, one per fold. -/

def HIGH_BITS_CAP : Nat := 3
def MAX_STACK_LOG : Nat := LIG_MIN_LOG_SIZE + LIG_N_LOG_SIZES - 1
/-- four selector bits share one table lookup -/
def SEL_NIBBLES : Nat := (MAX_STACK_LOG + 3) / 4
/-- a nibble's eq tables over its top 1..4 coords, strided -/
def SEL_EQ_STRIDE : Nat := 64
/-- eq prefix chain lengths -/
def EQ_CHAIN_ARMS : Nat := SIZE_BITS + QKECCAK_SLOT_LOG + 1
/-- nibbles of a bus selector run -/
def SEL_TAB_NIBBLES : Nat := (SIZE_BITS + 3) / 4
/-- a nibble's eq tables over its low 1..4 coords, padded -/
def SEL_TAB_EQ_STRIDE : Nat := 32
/-- where exponent_tables keeps the rank keys -/
def RANK_KEYS_AT : Nat := SIZE_BITS + 16 * SEL_TAB_NIBBLES
/-- above any block or column index -/
def RANK_STRIDE : Nat := N_BLOCKS + N_COMMITTED_COLS
/-- above any step between two rank keys -/
def RANK_KEY_BOUND : Nat := SIZE_BITS * RANK_STRIDE
def SIDE_TAB_AT : Nat := RANK_KEYS_AT + SIZE_BITS
/-- a bit window's pattern by its g-power: [g^n] = n -/
def WIN_TAB_AT : Nat := SIDE_TAB_AT + N_BLOCK_GROUPS
def WIN_TAB_BITS : Nat := 11
def WIN_TAB_LEN : Nat := 2 ^ WIN_TAB_BITS
def LIG_N_LEVELS : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_N_LEVELS
def LIG_YR_LEVEL : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_YR_LEVEL
def LIG_YR_LOG_LEN : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_YR_LOG_LEN
def LIG_YR_LEN : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_YR_LEN
def LIG_TOTAL_FOLDS : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_TOTAL_FOLDS
def LIG_CAP_DEPTH : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_CAP_DEPTH
/-- a level's first query position, the most any rate draws before it -/
def LIG_POS_OFF : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_POS_OFF
def LIG_POS_TOTAL : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_POS_TOTAL
/-- the subspace-vanishing values of n columns at n(n+1)/2 -/
def VANISH_BY_COLS : List (Nat × Nat) := LeanVM.Guest.Placeholders.VANISH_BY_COLS
/-- and their inverses -/
def VANISH_INVS_BY_COLS : List (Nat × Nat) := LeanVM.Guest.Placeholders.VANISH_INVS_BY_COLS
def LIG_QUERIES : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_QUERIES
def LIG_FOLDS : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_FOLDS
def LIG_LEAF_CELLS : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_LEAF_CELLS
def LIG_PACKED_ROW_CAP : Nat := LeanVM.Guest.Placeholders.LIG_PACKED_ROW_CAP
def LIG_ROW_CAP : Nat := LeanVM.Guest.Placeholders.LIG_ROW_CAP
def LIG_PATH_CAP : Nat := LeanVM.Guest.Placeholders.LIG_PATH_CAP
def LIG_TREE_DEPTH : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_TREE_DEPTH
def LIG_SQUEEZES : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_SQUEEZES
def LIG_LOG_MSG_COLS : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_LOG_MSG_COLS
def LIG_RESIDUAL_FOLD_OFF : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_RESIDUAL_FOLD_OFF
def LIG_RESIDUAL_PREFIX_LEN : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_RESIDUAL_PREFIX_LEN
/-- the bits of a level's high-part index, j < folds -/
def LIG_HIGH_BITS : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_HIGH_BITS
def LIG_FOLDS_OFF : List (Nat × Nat) := LeanVM.Guest.Placeholders.LIG_FOLDS_OFF
def LIG_MIN_SHIFT_INV : Nat := LeanVM.Guest.Placeholders.LIG_MIN_SHIFT_INV

/-! eval_b claim descriptors. CLAIM_POINT_BUF says which point buffer a pooled claim's x-part lives in, CLAIM_COMMITTED_COL maps it to the compact index of the committed column it must open (a virtual KECCAK value claim maps to QKECCAK), CLAIM_QKECCAK_SLOT_BITS holds the bits of the q_keccak slot a virtual claim reads (zero for a non-virtual one), and QKECCAK_COMMITTED_COL is the ring-switch target. A KECCAK output lane's claim is POINT_BUF_KECCAK_OUT: never opened, the 25 of them, from KECCAK_OUT_POOL on, are the Keccak reduction's claim on the output. -/

def POINT_BUF_ZETA : Nat := 0
def POINT_BUF_RHO : Nat := 1
def POINT_BUF_PI : Nat := 2
def POINT_BUF_QKECCAK_RHO : Nat := 3
def POINT_BUF_KECCAK_OUT : Nat := 4
def KECCAK_OUT_POOL : Nat := LeanVM.Guest.Placeholders.KECCAK_OUT_POOL
def CLAIM_POINT_BUF : List (Nat × Nat) := LeanVM.Guest.Placeholders.CLAIM_POINT_BUF
def CLAIM_COMMITTED_COL : List (Nat × Nat) := LeanVM.Guest.Placeholders.CLAIM_COMMITTED_COL
/-- a claim's low dimension, as a kappa source -/
def CLAIM_KAPPA_SRC : List (Nat × Nat) := LeanVM.Guest.Placeholders.CLAIM_KAPPA_SRC
def CLAIM_KAPPA_ADJ : List (Nat × Nat) := LeanVM.Guest.Placeholders.CLAIM_KAPPA_ADJ
def CLAIM_QKECCAK_SLOT_BITS : List (Nat × Nat) := LeanVM.Guest.Placeholders.CLAIM_QKECCAK_SLOT_BITS
def QKECCAK_COMMITTED_COL : Nat := LeanVM.Guest.Placeholders.QKECCAK_COMMITTED_COL
def QKECCAK_VARS_CAP : Nat := LeanVM.Guest.Placeholders.QKECCAK_VARS_CAP

/-! ## Statements and deferral -/

/-! A node defers one claim on the stacked bytecode. DEFER_SIZE is the region one sub-proof's verification exports (the claim's point, then its value); DEFER_STMT_* index the batched claim a node's OWN statement carries, laid out the same way. The Fiat-Shamir seed rides the public input rather than being baked, so one compiled guest verifies proofs of any inner program. -/

/-- log rows of the bytecode blocks -/
def BYTECODE_LOG : Nat := LeanVM.Guest.Placeholders.BYTECODE_LOG
def DEFER_SIZE : Nat := LeanVM.Guest.Placeholders.DEFER_SIZE
/-- = BYTECODE_LOG + LOG2_BYTECODE_COLS -/
def BYTECODE_VARS : Nat := LeanVM.Guest.Placeholders.BYTECODE_VARS
def FRESH_BC_VALUE : Nat := BYTECODE_VARS
def DEFER_STMT_CELLS : Nat := BYTECODE_VARS + 1
def DEFER_STMT_BC_VALUE : Nat := BYTECODE_VARS

/-! The aggregation transcript's seeded capacity, and the zeros padding a child's words to whole rates (so every child starts with a full rate waiting). -/

def AGG_SEED_0 : Nat := LeanVM.Guest.Placeholders.AGG_SEED_0
def AGG_SEED_1 : Nat := LeanVM.Guest.Placeholders.AGG_SEED_1
def AGG_SEED_2 : Nat := LeanVM.Guest.Placeholders.AGG_SEED_2
def AGG_SEED_3 : Nat := LeanVM.Guest.Placeholders.AGG_SEED_3
def AGG_SEED_4 : Nat := LeanVM.Guest.Placeholders.AGG_SEED_4
def AGG_CHILD_PAD : Nat := LeanVM.Guest.Placeholders.AGG_CHILD_PAD
def AGG_CHILD_WORDS : Nat := 2 + DEFER_SIZE + DEFER_STMT_CELLS

/-! The statement digest's preimage: the STMT_HEADER header cells (the seed, then the leanXMSS and leanSPHINCS claim-list digests and the DA one), then the deferred cells. No domain tag: every field has a fixed width, and the seed leads, binding this bytecode and the proof system's version. -/

def STMT_HEADER : Nat := LeanVM.Guest.Placeholders.STMT_HEADER
def STMT_DEFER_OFF : Nat := STMT_HEADER
def STMT_CELLS : Nat := STMT_DEFER_OFF + DEFER_STMT_CELLS

/-! ## The hash -/

/-! Every hash is Keccak-256 (primitives::hash::hash): a block is 136 bytes, eight and a half cells, XORed into the previous KECCAK_STATE-cell sponge state before a KECCAK, and the last output's first two cells are the digest. A hash of runtime length carries that state through a heap run between loop frames, KECCAK_STATE cells a step (`claim_list_digest`). -/

def KECCAK_STATE : Nat := LeanVM.Guest.Placeholders.KECCAK_STATE

/-! Claims a declared claim list absorbs a loop frame: 68 cells, four block pairs. The list's bulk goes CLAIM_BIG claims a frame, BIG_GROUPS of those groups, so that the sponge state's trip through the heap is paid once per CLAIM_BIG claims; the rest CLAIM_GROUP a frame, then a `match` on the last group's count. -/

def CLAIM_GROUP : Nat := LeanVM.Guest.Placeholders.CLAIM_GROUP
def BIG_GROUPS : Nat := LeanVM.Guest.Placeholders.BIG_GROUPS
def CLAIM_BIG : Nat := CLAIM_GROUP * BIG_GROUPS

/-! A child list's walk record: the sponge state, then a coverage slot and a table entry. -/

def MONO_REC : Nat := KECCAK_STATE + 2

/-! ## WOTS+C (host-supplied) -/

/-! Both schemes' one-time keys: chains of CHAIN_LENGTH positions, whose digits are dispatched a group at a time (leanSPHINCS DIGIT_GROUP and the last chain alone, leanXMSS LX_DIGIT_GROUP and the rest), and the leanXMSS address, a cell whose low lane is lo:32 | hi:24 | type:5 | step:3; TW_* hold the type. Every 16-byte native value is one cell. -/

def W : Nat := LeanVM.Guest.Placeholders.W
def CHAIN_LENGTH : Nat := 2 ^ W
def CHAIN_STEPS : Nat := CHAIN_LENGTH - 1
def DIGIT_GROUP : Nat := LeanVM.Guest.Placeholders.DIGIT_GROUP
def DIGIT_GROUPS : Nat := CHAIN_LENGTH ^ DIGIT_GROUP

/-! The digit sum of group k, at k. -/

def DIGIT_SUMS : List (Nat × Nat) := LeanVM.Guest.Placeholders.DIGIT_SUMS

/-! ## LeanXMSS (host-supplied) -/

/-! Two layers of trees of height LX_HEIGHT over keys of LX_V chains. A layer's digest is a codeword when its first LX_V digits sum to LX_TARGET_SUM and the rest are zero. An address is a cell whose low lane is lo:32 | hi:24 | type:5 | step:3, TW_* holding the type; LX_TOP is the top layer's flag where an address holds it. -/

def TW_CHAIN : Nat := LeanVM.Guest.Placeholders.TW_CHAIN
def TW_LEAF : Nat := LeanVM.Guest.Placeholders.TW_LEAF
def TW_NODE : Nat := LeanVM.Guest.Placeholders.TW_NODE
def TW_MSG : Nat := LeanVM.Guest.Placeholders.TW_MSG
def HI_MUL : Nat := 2 ^ 32
def STEP_MUL : Nat := 2 ^ 61
def LX_V : Nat := LeanVM.Guest.Placeholders.LX_V
def LX_TARGET_SUM : Nat := LeanVM.Guest.Placeholders.LX_TARGET_SUM
def LX_HEIGHT : Nat := LeanVM.Guest.Placeholders.LX_HEIGHT
def LX_TOP : Nat := LeanVM.Guest.Placeholders.LX_TOP

/-! The path is dispatched LX_WINDOW index bits at a time (`lx_window`), LX_LAYER_WINDOWS a layer. -/

def LX_WINDOW : Nat := LeanVM.Guest.Placeholders.LX_WINDOW
def LX_LAYER_WINDOWS : Nat := LX_HEIGHT / LX_WINDOW
def LX_WINDOWS : Nat := 2 * LX_LAYER_WINDOWS
def LX_WINDOW_ARMS : Nat := 2 ^ LX_WINDOW

/-! A layer's codeword digits are dispatched LX_DIGIT_GROUP at a time, then the LX_DIGIT_TAIL left. -/

def LX_DIGIT_GROUP : Nat := LeanVM.Guest.Placeholders.LX_DIGIT_GROUP
def LX_DIGIT_GROUPS : Nat := CHAIN_LENGTH ^ LX_DIGIT_GROUP
def LX_DIGIT_TAIL : Nat := LX_V % LX_DIGIT_GROUP
def LX_TAIL_GROUPS : Nat := CHAIN_LENGTH ^ LX_DIGIT_TAIL
def LX_DIGIT_DISPATCHES : Nat := LX_V / LX_DIGIT_GROUP + 1
def LX_GROUP_SIZES : List (Nat × Nat) := LeanVM.Guest.Placeholders.LX_GROUP_SIZES

/-! Where a chain index lives (`walk`): the zero cell for 0, powers[LX_TAG_LOG[i]] for a power of two (slot 0), else LX_TAG_SLOT[i] - 1 of the LX_N_TAGS carried tags. -/

def LX_TAG_SLOT : List (Nat × Nat) := LeanVM.Guest.Placeholders.LX_TAG_SLOT
def LX_TAG_LOG : List (Nat × Nat) := LeanVM.Guest.Placeholders.LX_TAG_LOG
def LX_N_TAGS : Nat := LeanVM.Guest.Placeholders.LX_N_TAGS

/-! ## LeanSPHINCS (host-supplied) -/

/-! The scheme's own letters, prefixed SP_: under each bottom leaf a FORS instance of SP_FORS_TREES trees of height SP_FORS_HEIGHT, and above them three layers of trees over WOTS+C keys of SP_V chains, of heights SP_HEIGHT_0, SP_HEIGHT_1 and SP_HEIGHT_2 from the bottom. An addressed hash is PK.seed, FIPS 205's 32-byte address (two cells), then the payload. -/

def SP_V : Nat := LeanVM.Guest.Placeholders.SP_V
def SP_TARGET_SUM : Nat := LeanVM.Guest.Placeholders.SP_TARGET_SUM
def SP_HEIGHT_0 : Nat := LeanVM.Guest.Placeholders.SP_HEIGHT_0
def SP_HEIGHT_1 : Nat := LeanVM.Guest.Placeholders.SP_HEIGHT_1
def SP_HEIGHT_2 : Nat := LeanVM.Guest.Placeholders.SP_HEIGHT_2
def SP_H : Nat := SP_HEIGHT_0 + SP_HEIGHT_1 + SP_HEIGHT_2
def SP_FORS_TREES : Nat := LeanVM.Guest.Placeholders.SP_FORS_TREES
def SP_FORS_HEIGHT : Nat := LeanVM.Guest.Placeholders.SP_FORS_HEIGHT

/-! The message digest is H_msg's two calls: the first call's two cells, then the low two bytes of the second call's first cell. Its first SP_MD_BYTES bytes are the FORS leaves, SP_FORS_HEIGHT bits each, most significant first; then the tree index, three bytes big endian of which the low SP_H - SP_HEIGHT_0 bits count, the high byte holding the 2 bits the others leave; then the bottom leaf, one byte. -/

def SP_CELL_BITS : Nat := 2 * BASE_FIELD_BITS
def SP_MD_BYTES : Nat := SP_FORS_TREES * SP_FORS_HEIGHT / 8
def SP_DIGEST_BYTES : Nat := LeanVM.Guest.Placeholders.SP_DIGEST_BYTES

/-! The digest's bytes in the second call's first cell: the middle leaf, then the bottom leaf, one byte each. -/

def SP_TAIL_BYTES : Nat := SP_DIGEST_BYTES - 32

/-! The layers' leaves one after the other, bottom first: the middle leaf's first bit, the top leaf's, and the top leaf's bits in the tree index's high byte, whose other bits are unused. -/

def SP_MID : Nat := SP_HEIGHT_0
def SP_TOP : Nat := SP_HEIGHT_0 + SP_HEIGHT_1
def SP_TOP_HIGH_BITS : Nat := SP_HEIGHT_2 - 8
def SP_PAD_BITS : Nat := 8 - SP_TOP_HIGH_BITS

/-! The cell bits of the first call's second cell where the tree index's high byte (digest byte SP_MD_BYTES) and middle byte (the next) start. -/

def SP_TREE_HI_BIT : Nat := 8 * (SP_MD_BYTES - 16)
def SP_TREE_MID_BIT : Nat := SP_TREE_HI_BIT + 8

/-! A codeword's digits in each byte of its encoding digest, base_2b. -/

def SP_DIGITS_PER_BYTE : Nat := 8 / W

/-! Each H_msg call's input: R, PK.seed, PK.root and the 32-byte M, five cells, then the counter BE_32(i), a cell of its own whose byte 3 is i. -/

def SP_HMSG_LEN : Nat := 5 * 16 + 4
def SP_COUNTER_ONE : Nat := 2 ^ 24

/-! FIPS 205's address is two cells, A0 the layer and the tree words and A1 the type and the three words after it, each word big endian, so a value's low byte is its word's last. The cell bit each such byte starts at: -/

/-- A0's byte 3: the layer -/
def SP_LAYER_MUL : Nat := LeanVM.Guest.Placeholders.SP_LAYER_MUL
/-- A0's bytes 15, 14 and 13: the tree's three low bytes -/
def SP_TREE_MUL_0 : Nat := LeanVM.Guest.Placeholders.SP_TREE_MUL_0
def SP_TREE_MUL_1 : Nat := LeanVM.Guest.Placeholders.SP_TREE_MUL_1
def SP_TREE_MUL_2 : Nat := LeanVM.Guest.Placeholders.SP_TREE_MUL_2
/-- A1's bytes 23 and 22: the key pair's two low bytes -/
def SP_KEY_MUL_0 : Nat := LeanVM.Guest.Placeholders.SP_KEY_MUL_0
def SP_KEY_MUL_1 : Nat := LeanVM.Guest.Placeholders.SP_KEY_MUL_1
/-- A1's byte 27: a chain index or a tree height -/
def SP_WORD2_MUL : Nat := LeanVM.Guest.Placeholders.SP_WORD2_MUL
/-- A1's bytes 31 and 30: a hash address or a tree index -/
def SP_WORD3_MUL_0 : Nat := LeanVM.Guest.Placeholders.SP_WORD3_MUL_0
def SP_WORD3_MUL_1 : Nat := LeanVM.Guest.Placeholders.SP_WORD3_MUL_1

/-! The address types as A1 holds them; WOTS_HASH is zero. -/

def SP_WOTS_PK : Nat := LeanVM.Guest.Placeholders.SP_WOTS_PK
def SP_TREE : Nat := LeanVM.Guest.Placeholders.SP_TREE
def SP_FORS_TREE : Nat := LeanVM.Guest.Placeholders.SP_FORS_TREE
def SP_FORS_ROOTS : Nat := LeanVM.Guest.Placeholders.SP_FORS_ROOTS
def SP_WOTS_ENC : Nat := LeanVM.Guest.Placeholders.SP_WOTS_ENC

/-! Values bounded a byte at a time: each byte hinted in the exponent, range checked, and read as the bits it spells off a table of the SP_BYTE_VALUES bytes. -/

def SP_BYTE_VALUES : Nat := 256

/-! The encoding counter, BE_32 in the low four bytes of its cell: bounded by rebuilding it from exactly that many bytes, so the guest accepts no preimage the native verifier cannot parse. -/

def SP_COUNTER_BYTES : Nat := 4

/-! An encoding's input: PK.seed, the address, the value it signs, then the counter. -/

def SP_ENCODING_BYTES : Nat := 16 * 4 + SP_COUNTER_BYTES

/-! The second call's low lane past the digest: bytes, likewise. -/

def SP_UNUSED_BYTES : Nat := 8 - SP_TAIL_BYTES

/-! ## Node capacities -/

/-! The coverage table's slots, both schemes' declared claims and their duplicates, are bounded by the memory itself: each count is a g-power address (`assert_gpow`), so its log is below the announced memory size, at most 2^30, and sums of a few never wrap. MAX_RECURSIONS is the arity of an aggregation tree. -/

def MAX_RECURSIONS : Nat := LeanVM.Guest.Placeholders.MAX_RECURSIONS

/-! ## LeanDA -/

/-! Blob and cell widths are fixed. The blob count is hinted and bounded by DA_MAX_ROWS; zero rows pad the matrix to DA_MAX_ROWS. -/

def LOG_BLOB_SYMBOLS : Nat := LeanVM.Guest.Placeholders.LOG_BLOB_SYMBOLS
def LOG_CELL_SYMBOLS : Nat := LeanVM.Guest.Placeholders.LOG_CELL_SYMBOLS
def DA_MAX_ROWS : Nat := LeanVM.Guest.Placeholders.DA_MAX_ROWS
def DA_LOG_MAX_ROWS : Nat := LeanVM.Guest.Placeholders.DA_LOG_MAX_ROWS
def DA_PAD_BLOB_0 : Nat := LeanVM.Guest.Placeholders.DA_PAD_BLOB_0
def DA_PAD_BLOB_1 : Nat := LeanVM.Guest.Placeholders.DA_PAD_BLOB_1

/-! Vhat_j at the points the membership vector's product tree needs (da_factors): each parent node of the tree over a cell index, then of the tree inside a cell, at the bit j it splits; and Vhat_j(beta_(LOG_CELL_SYMBOLS + b)) at LOG_CELL_SYMBOLS * b + j, for each factor j inside a cell and bit b of the cell index. -/

def DA_VHAT : List (Nat × Nat) := LeanVM.Guest.Placeholders.DA_VHAT
def DA_VHAT_COLUMN : List (Nat × Nat) := LeanVM.Guest.Placeholders.DA_VHAT_COLUMN
/-- log of the symbols per encoded row -/
def DA_LOG_M : Nat := LOG_BLOB_SYMBOLS + 1
/-- symbols in a cell -/
def DA_CELL : Nat := 2 ^ LOG_CELL_SYMBOLS
/-- log of the cells per row -/
def DA_BLOCK_BITS : Nat := DA_LOG_M - LOG_CELL_SYMBOLS
/-- cells per row -/
def DA_CELLS : Nat := 2 ^ DA_BLOCK_BITS
/-- where a blob's running sum starts, past its tree -/
def DA_SUM : Nat := 4 * DA_CELLS
/-- cells of one blob's tree and running sum -/
def DA_REGION : Nat := DA_SUM + DA_CELLS + 1

end
end LeanVM.Guest.Program
