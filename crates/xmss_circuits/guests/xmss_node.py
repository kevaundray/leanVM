# One node of an XMSS-only aggregation: zkDSL, not runnable Python (see
# crates/lean_compiler/zkDSL.md). A node verifies raw XMSS signatures grouped by
# (leaf index, message) and merges the signer sets of up to MAX_RECURSIONS child
# nodes, then publishes either its signer-set digest (no children) or the digest of
# that set and the children's set digests (a merge). Child PROOFS are not verified
# here: the host verifies each child natively against the set digest this node
# binds (`xmss_circuits::XmssAggregate::verify`).
#
# The XMSS verification, the coverage table and the signer-set digest are those of
# the recursion guest (crates/rec_aggregation/guests/lean_ethereum.py) with the
# SPHINCS, LeanDA, deferred-claim and in-circuit verifier parts removed, so a
# node's signer-set digest is byte-identical to rec_aggregation's `signers_hash`
# of an XMSS-only set. Every `*_PLACEHOLDER` is filled by `xmss_circuits::program`.
from snark_lib import *

INV_GEN = INV_GEN_PLACEHOLDER
Y_TOWER = Y_TOWER_PLACEHOLDER
COORD_BASIS = COORD_BASIS_PLACEHOLDER

# ------------------------------------------------------------- list digests
# A list is hashed a window of SIGNERS_WINDOW blocks per loop frame, the rest in a
# dispatched tail, the byte counter of each window split off as a bit pattern
# (doc/leanvm §Byte counters for a hash of runtime length).
SIGNERS_WINDOW = SIGNERS_WINDOW_PLACEHOLDER
SIGNERS_WINDOW_LOG = SIGNERS_WINDOW_LOG_PLACEHOLDER
SIGNERS_MAX_WINDOWS = SIGNERS_MAX_WINDOWS_PLACEHOLDER
SIGNERS_COUNT_BITS = SIGNERS_COUNT_BITS_PLACEHOLDER
BLAKE2S_IV_0 = BLAKE2S_IV_0_PLACEHOLDER
BLAKE2S_IV_1 = BLAKE2S_IV_1_PLACEHOLDER
MD_FINAL = MD_FINAL_PLACEHOLDER
# The digest of the empty SPHINCS claim list, which every signer set here carries.
SP_EMPTY_0 = SP_EMPTY_0_PLACEHOLDER
SP_EMPTY_1 = SP_EMPTY_1_PLACEHOLDER

# ------------------------------------------------------------------- XMSS
V = V_PLACEHOLDER
W = W_PLACEHOLDER
TARGET_SUM = TARGET_SUM_PLACEHOLDER
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER
CHAIN_LENGTH = 2 ** W
CHAIN_STEPS = CHAIN_LENGTH - 1
WORDS_PER_VALUE = 1
WORDS_PER_BLOCK = 2
N_TWEAKS = 1 + V * CHAIN_STEPS + 1 + LOG_LIFETIME
N_TWEAK_CELLS = WORDS_PER_VALUE * N_TWEAKS
WOTS_PK_TWEAK_IDX = 1 + V * CHAIN_STEPS
MERKLE_TWEAK_IDX = WOTS_PK_TWEAK_IDX + 1
MERKLE_BIT_CELLS = WORDS_PER_VALUE * LOG_LIFETIME
XM_ENC_TWEAK = XM_ENC_TWEAK_PLACEHOLDER
XM_PK_TWEAK = XM_PK_TWEAK_PLACEHOLDER
XM_CHAIN_TWEAKS = XM_CHAIN_TWEAKS_PLACEHOLDER  # indexed CHAIN_STEPS·i + s
XM_MERKLE_TWEAKS = XM_MERKLE_TWEAKS_PLACEHOLDER  # indexed by level
XM_INDEX_WEIGHT = XM_INDEX_WEIGHT_PLACEHOLDER
DIGITS_PER_WORD = V / 2
PAIR_DIGITS = CHAIN_LENGTH * CHAIN_LENGTH  # values of two chains' digits together
TIP_CELLS = 2 * V
WOTS_PK_BLOCKS = (2 + V) / 4

# --------------------------------------------------------------- capacities
MAX_KEYS = MAX_KEYS_PLACEHOLDER
MAX_RECURSIONS = MAX_RECURSIONS_PLACEHOLDER
MAX_LEAF_INDICES = MAX_LEAF_INDICES_PLACEHOLDER


def squares_table():
    # g_squares[g^j] = g^(2^j), which turns a bit decomposition of an exponent
    # back into the g-power it decomposes.
    g_squares = HeapBuf(SIGNERS_COUNT_BITS)
    sq_run = GEN
    for j in unroll(0, SIGNERS_COUNT_BITS):
        g_squares[GEN ** j] = sq_run
        sq_run *= sq_run
    return g_squares


@inline
def order_children(node, sibling, bit):
    # `bit` is boolean-pinned, so `m` selects: (node, sibling) at 0, (sibling, node) at 1.
    m = bit * (node + sibling)
    kids = [node + m, sibling + m]
    return kids


# ============================ XMSS signature verification ===========================
# Tweak table layout (tweak index t at cell g^t):
#     0                        : encoding tweak
#     1 + CHAIN_STEPS·i + s    : chain tweak, chain i < V, step s < CHAIN_STEPS
#     WOTS_PK_TWEAK_IDX        : wots-pk tweak
#     MERKLE_TWEAK_IDX + l     : merkle tweak, level l < LOG_LIFETIME


def fill_xmss_leaf_index_tables(leaf_index, merkle_bits, tweak_table):
    # One bit decomposition of the leaf index gives every tweak's index field and
    # the Merkle direction bits; the reconstruction also bounds it to LOG_LIFETIME bits.
    hint_decompose_bits(merkle_bits, leaf_index, LOG_LIFETIME)
    bits = StackBuf(LOG_LIFETIME)
    reconstructed = 0
    index = 0
    for b in unroll(0, LOG_LIFETIME):
        bit = merkle_bits[GEN ** b]
        merkle_bits[GEN ** b] = bit * bit
        bits[b] = bit
        reconstructed += bit * COORD_BASIS[b]
        index += bit * XM_INDEX_WEIGHT[b]
    assert reconstructed == leaf_index
    tweak_table[1] = index + XM_ENC_TWEAK
    for i in unroll(0, V):
        for s in unroll(0, CHAIN_STEPS):
            tweak_table[GEN ** (1 + CHAIN_STEPS * i + s)] = index + XM_CHAIN_TWEAKS[CHAIN_STEPS * i + s]
    tweak_table[GEN ** WOTS_PK_TWEAK_IDX] = index + XM_PK_TWEAK
    for lvl in unroll(1, LOG_LIFETIME + 1):
        parent = 0
        for b in unroll(lvl, LOG_LIFETIME):
            parent += bits[b] * XM_INDEX_WEIGHT[b - lvl]
        tweak_table[GEN ** (MERKLE_TWEAK_IDX + lvl - 1)] = parent + XM_MERKLE_TWEAKS[lvl - 1]
    return


def verify_sig(message, tweak_table, merkle_bits, pk_ptr):
    # One signature against the key at pk_ptr = (merkle_root, public_param).
    pp = pk_ptr[GEN]

    # Encoding digest D = BLAKE2s(tweak | pp | msg | randomness | zero-pad), 96 bytes.
    after_msg = StackBuf(WORDS_PER_BLOCK)
    blake2s([tweak_table[1], pp], [message[1], message[GEN]], after_msg, counter=64, final=0)
    rand_block = StackBuf(WORDS_PER_BLOCK)
    hint_witness(rand_block, "rand")
    assert_in_k(rand_block[1], 0)
    digest = StackBuf(WORDS_PER_BLOCK)
    blake2s(rand_block, [0, 0], digest, cv=after_msg, counter=96, final=1)

    # V WOTS chains, each walking only the CHAIN_STEPS - e_i steps its digit needs.
    # Two neighbouring chains of one digest lane share one hinted exponent
    # g^(e_c + CHAIN_LENGTH·e_{c+1}), range checked and dispatched once, and a lane's
    # odd chain out has its own. Each arm returns its digits weighted into the lane
    # and g^(their sum): the product of those is the target sum, and the weighted
    # digits rebuild D's first cell as `acc_lo + acc_hi·Y`.
    tips = StackBuf(TIP_CELLS)
    step_md = StackBuf(1)
    step_md[0] = MD_FINAL + 48
    digit_product = 1
    acc_lo = 0
    acc_hi = 0
    for half in unroll(0, 2):
        acc = 0
        for p in unroll(0, DIGITS_PER_WORD // 2):
            ct = tweak_table * GEN ** (WORDS_PER_VALUE * (1 + CHAIN_STEPS * (half * DIGITS_PER_WORD + 2 * p)))
            pair = hint_witness("digits")
            assert log(pair) < PAIR_DIGITS
            start_a = hint_witness("chain_starts")
            start_b = hint_witness("chain_starts")
            term, digits = match(log(pair), range(0, PAIR_DIGITS), lambda k: walk_pair(start_a, start_b, ct, pp, step_md[0], tips, half, p, k))
            digit_product = digit_product * digits
            acc = acc + term
        if const(DIGITS_PER_WORD % 2 == 1):
            ct = tweak_table * GEN ** (WORDS_PER_VALUE * (1 + CHAIN_STEPS * (half * DIGITS_PER_WORD + DIGITS_PER_WORD - 1)))
            digit = hint_witness("digits")
            assert log(digit) < CHAIN_LENGTH
            start = hint_witness("chain_starts")
            term = match(log(digit), range(0, CHAIN_LENGTH), lambda k: walk(start, ct, pp, step_md[0], tips, half * DIGITS_PER_WORD + DIGITS_PER_WORD - 1, k))
            digit_product = digit_product * digit
            acc = acc + term
        if const(half == 0):
            acc_lo = acc
        else:
            acc_hi = acc
    assert digit_product == GEN ** TARGET_SUM
    assert acc_lo + acc_hi * Y_TOWER == digest[0]

    # WOTS public-key leaf: BLAKE2s over the prefix (tweak, pp) and the V tips.
    leaf = StackBuf(WORDS_PER_BLOCK)
    blake2s([tweak_table[GEN ** (WORDS_PER_VALUE * WOTS_PK_TWEAK_IDX)], pp], [tips[0], tips[2]], leaf, counter=64, final=0)
    for q in unroll(1, WOTS_PK_BLOCKS):
        next_leaf = StackBuf(WORDS_PER_BLOCK)
        blake2s([tips[8 * q - 4], tips[8 * q - 2]], [tips[8 * q], tips[8 * q + 2]], next_leaf, cv=leaf, counter=64 * (q + 1), final=(q + 1) // WOTS_PK_BLOCKS)
        leaf = next_leaf

    # Merkle path to the root, ordered by the leaf index bits.
    node = leaf[0]
    for lvl in unroll(0, LOG_LIFETIME):
        sibling = hint_witness("siblings")
        children = order_children(node, sibling, merkle_bits[GEN ** (WORDS_PER_VALUE * lvl)])
        parent = StackBuf(WORDS_PER_BLOCK)
        blake2s([tweak_table[GEN ** (WORDS_PER_VALUE * (MERKLE_TWEAK_IDX + lvl))], pp], children, parent)
        node = parent[0]
    assert node == pk_ptr[1]
    return


@inline
def walk(value, chain_tweaks, pp, md, tips, i: Const, k: Const):
    # Chain i's steps k..CHAIN_STEPS-1, the tip landing in tips[2i].
    if const(k == CHAIN_STEPS):
        tips[2 * i] = value
    else:
        word = value
        for s in unroll(k, CHAIN_STEPS - 1):
            out = StackBuf(WORDS_PER_BLOCK)
            blake2s([chain_tweaks[GEN ** (WORDS_PER_VALUE * s)], pp], [word, 0], out, md=md)
            word = out[0]
        blake2s([chain_tweaks[GEN ** (WORDS_PER_VALUE * (CHAIN_STEPS - 1))], pp], [word, 0], tips[2 * i:2 * i + 2], md=md)
    return const(k * CHAIN_LENGTH ** (i % DIGITS_PER_WORD))



@inline
def walk_pair(a, b, ct, pp, md, tips, half: Const, p: Const, k: Const):
    # Chains c = half·DIGITS_PER_WORD + 2p and c + 1, at digits k % CHAIN_LENGTH and
    # k // CHAIN_LENGTH; `ct` points at chain c's tweaks.
    term_a = walk(a, ct, pp, md, tips, half * DIGITS_PER_WORD + 2 * p, k % CHAIN_LENGTH)
    term_b = walk(b, ct * GEN ** (WORDS_PER_VALUE * CHAIN_STEPS), pp, md, tips, half * DIGITS_PER_WORD + 2 * p + 1, k // CHAIN_LENGTH)
    return term_a + term_b, GEN ** (k % CHAIN_LENGTH + k // CHAIN_LENGTH)


# =================================== list digests ===================================


def scaled_log(x, g_squares, shift: Const):
    # 2^shift times the exponent of `x`, as a bit pattern; the advice bits are tied
    # back by the g-power product, so they ARE that exponent.
    bits = StackBuf(SIGNERS_COUNT_BITS)
    hint_decompose_bits_exponent(bits, x, SIGNERS_COUNT_BITS)
    value = 0
    rebuilt = GEN ** 0
    for j in unroll(0, SIGNERS_COUNT_BITS):
        b = bits[j]
        bits[j] = b * b
        value += b * COORD_BASIS[j]
        rebuilt *= (1 + b * (g_squares[GEN ** j] + 1))
    assert rebuilt == x
    return value * COORD_BASIS[shift]


def keys_window(state_0, state_1, base, keys_ptr, x_q, g_squares):
    # One window of a group's key hash: SIGNERS_WINDOW blocks, two keys a block.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, SIGNERS_WINDOW):
        pair = keys_ptr * (GEN ** (4 * j))
        hint_witness(pair[0:4], "pubkeys")
        out = StackBuf(2)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(pair[0:2], pair[2:4], out, cv=st, md=nxt)
        else:
            blake2s(pair[0:2], pair[2:4], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], nxt


def keys_tail(state_0, state_1, base, keys_ptr, k: Const):
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, k):
        pair = keys_ptr * (GEN ** (4 * j))
        hint_witness(pair[0:4], "pubkeys")
        out = StackBuf(2)
        blake2s(pair[0:2], pair[2:4], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], keys_ptr * (GEN ** (4 * k))


def key_list_digest(keys_ptr, half_g, odd_g, n_keys_g, g_squares):
    # BLAKE2s of one group's declared keys, 32 bytes a key, hinted into the table.
    split = StackBuf(2)
    hint_witness(split, "signers_split")
    windows = split[0]
    tail = split[1]
    assert log(tail) < SIGNERS_WINDOW
    assert log(windows) < SIGNERS_MAX_WINDOWS
    assert windows ** SIGNERS_WINDOW * tail == half_g * odd_g * INV_GEN
    chain = HeapBuf((windows * GEN) ** 4)
    chain[1] = BLAKE2S_IV_0
    chain[GEN] = BLAKE2S_IV_1
    chain[GEN ** 2] = 0
    chain[GEN ** 3] = keys_ptr
    for xq in mul_range(1, windows):
        slot = chain * (xq ** 4)
        s0, s1, nb = keys_window(slot[1], slot[GEN], slot[GEN ** 2], slot[GEN ** 3], xq, g_squares)
        step = chain * ((xq * GEN) ** 4)
        step[1] = s0
        step[GEN] = s1
        step[GEN ** 2] = nb
        step[GEN ** 3] = slot[GEN ** 3] * (GEN ** (4 * SIGNERS_WINDOW))
    end = chain * (windows ** 4)
    t0, t1, last = match(log(tail), range(0, SIGNERS_WINDOW), lambda k: keys_tail(end[1], end[GEN], end[GEN ** 2], end[GEN ** 3], k))
    final = scaled_log(n_keys_g, g_squares, 5) + MD_FINAL
    digest = StackBuf(2)
    if odd_g == 1:
        hint_witness(last[0:4], "pubkeys")
        blake2s(last[0:2], last[2:4], digest, cv=[t0, t1], md=final)
    else:
        hint_witness(last[0:2], "pubkeys")
        blake2s(last[0:2], [0, 0], digest, cv=[t0, t1], md=final)
    return digest[0], digest[1]


def child_keys_window(state_0, state_1, base, keys_ptr, cover, marks, origin_g, limit_g, x_q, g_squares):
    # One window of a child's key hash, both keys of a block read at hinted offsets
    # into this node's group region and marked in the coverage table.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, SIGNERS_WINDOW):
        two = StackBuf(2)
        hint_witness(two, "child_index")
        assert log(two[0]) < log(limit_g)
        assert log(two[1]) < log(limit_g)
        cover[origin_g * two[0]] = marks * (GEN ** (2 * j))
        cover[origin_g * two[1]] = marks * (GEN ** (2 * j + 1))
        key_a = keys_ptr * (two[0] * two[0])
        key_b = keys_ptr * (two[1] * two[1])
        out = StackBuf(2)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(key_a[0:2], key_b[0:2], out, cv=st, md=nxt)
        else:
            blake2s(key_a[0:2], key_b[0:2], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], nxt


def child_keys_tail(state_0, state_1, base, keys_ptr, cover, marks, origin_g, limit_g, k: Const):
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, k):
        two = StackBuf(2)
        hint_witness(two, "child_index")
        assert log(two[0]) < log(limit_g)
        assert log(two[1]) < log(limit_g)
        cover[origin_g * two[0]] = marks * (GEN ** (2 * j))
        cover[origin_g * two[1]] = marks * (GEN ** (2 * j + 1))
        key_a = keys_ptr * (two[0] * two[0])
        key_b = keys_ptr * (two[1] * two[1])
        out = StackBuf(2)
        blake2s(key_a[0:2], key_b[0:2], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], marks * (GEN ** (2 * k))


def child_key_list_digest(keys_ptr, cover, base, origin_g, limit_g, half_g, odd_g, n_keys_g, g_squares):
    # The digest of one child group's keys over the same 32·n bytes the child
    # hashed, every key read out of this node's table through a covered slot.
    split = StackBuf(2)
    hint_witness(split, "signers_split")
    windows = split[0]
    tail = split[1]
    assert log(tail) < SIGNERS_WINDOW
    assert log(windows) < SIGNERS_MAX_WINDOWS
    assert windows ** SIGNERS_WINDOW * tail == half_g * odd_g * INV_GEN
    chain = HeapBuf((windows * GEN) ** 4)
    chain[1] = BLAKE2S_IV_0
    chain[GEN] = BLAKE2S_IV_1
    chain[GEN ** 2] = 0
    chain[GEN ** 3] = base
    for xq in mul_range(1, windows):
        slot = chain * (xq ** 4)
        s0, s1, nb = child_keys_window(slot[1], slot[GEN], slot[GEN ** 2], keys_ptr, cover, slot[GEN ** 3], origin_g, limit_g, xq, g_squares)
        step = chain * ((xq * GEN) ** 4)
        step[1] = s0
        step[GEN] = s1
        step[GEN ** 2] = nb
        step[GEN ** 3] = slot[GEN ** 3] * (GEN ** (2 * SIGNERS_WINDOW))
    end = chain * (windows ** 4)
    t0, t1, marks = match(log(tail), range(0, SIGNERS_WINDOW), lambda k: child_keys_tail(end[1], end[GEN], end[GEN ** 2], keys_ptr, cover, end[GEN ** 3], origin_g, limit_g, k))
    final = scaled_log(n_keys_g, g_squares, 5) + MD_FINAL
    digest = StackBuf(2)
    if odd_g == 1:
        two = StackBuf(2)
        hint_witness(two, "child_index")
        assert log(two[0]) < log(limit_g)
        assert log(two[1]) < log(limit_g)
        cover[origin_g * two[0]] = marks
        cover[origin_g * two[1]] = marks * GEN
        key_a = keys_ptr * (two[0] * two[0])
        key_b = keys_ptr * (two[1] * two[1])
        blake2s(key_a[0:2], key_b[0:2], digest, cv=[t0, t1], md=final)
    else:
        tail_idx = hint_witness("child_index")
        assert log(tail_idx) < log(limit_g)
        cover[origin_g * tail_idx] = marks
        key_last = keys_ptr * (tail_idx * tail_idx)
        blake2s(key_last[0:2], [0, 0], digest, cv=[t0, t1], md=final)
    return digest[0], digest[1]


def plain_window(state_0, state_1, base, run_ptr, x_q, g_squares):
    # One window over a run of cells already in memory, four to a block.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, SIGNERS_WINDOW):
        block = run_ptr * (GEN ** (4 * j))
        out = StackBuf(2)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(block[0:2], block[2:4], out, cv=st, md=nxt)
        else:
            blake2s(block[0:2], block[2:4], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], nxt


def plain_tail(state_0, state_1, base, run_ptr, k: Const):
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, k):
        block = run_ptr * (GEN ** (4 * j))
        out = StackBuf(2)
        blake2s(block[0:2], block[2:4], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], run_ptr * (GEN ** (4 * k))


def plain_digest(run_ptr, blocks, g_squares):
    # BLAKE2s of `log(blocks)` whole 64-byte blocks already in memory at run_ptr.
    split = StackBuf(2)
    hint_witness(split, "signers_split")
    windows = split[0]
    tail = split[1]
    assert log(tail) < SIGNERS_WINDOW
    assert log(windows) < SIGNERS_MAX_WINDOWS
    assert windows ** SIGNERS_WINDOW * tail == blocks * INV_GEN
    chain = HeapBuf((windows * GEN) ** 4)
    chain[1] = BLAKE2S_IV_0
    chain[GEN] = BLAKE2S_IV_1
    chain[GEN ** 2] = 0
    chain[GEN ** 3] = run_ptr
    for xq in mul_range(1, windows):
        slot = chain * (xq ** 4)
        s0, s1, nb = plain_window(slot[1], slot[GEN], slot[GEN ** 2], slot[GEN ** 3], xq, g_squares)
        step = chain * ((xq * GEN) ** 4)
        step[1] = s0
        step[GEN] = s1
        step[GEN ** 2] = nb
        step[GEN ** 3] = slot[GEN ** 3] * (GEN ** (4 * SIGNERS_WINDOW))
    end = chain * (windows ** 4)
    t0, t1, last = match(log(tail), range(0, SIGNERS_WINDOW), lambda k: plain_tail(end[1], end[GEN], end[GEN ** 2], end[GEN ** 3], k))
    final = scaled_log(blocks, g_squares, 6) + MD_FINAL
    digest = StackBuf(2)
    blake2s(last[0:2], last[2:4], digest, cv=[t0, t1], md=final)
    return digest[0], digest[1]


def rebuild_child_groups(nsub_e_g, run_ptr, base, leaf_indices, msgs, group_base, group_slots, n_leaf_indices_g, xmss_table, cover, g_squares):
    # A child's groups, laid out as its own signer-set hash covers them, each tied
    # by a hinted map to this node's group with the same leaf index AND message, in
    # whose region its keys are covered. Returns the child's claim count.
    counts = HeapBuf(nsub_e_g * GEN)
    counts[GEN ** 0] = 1
    for xj in mul_range(1, nsub_e_g):
        grp = StackBuf(4)
        hint_witness(grp, "child_group")  # leaf index, msg_lo, msg_hi, count
        n_keys = grp[3]
        assert log(n_keys) < MAX_KEYS
        parent = hint_witness("child_group_map")
        assert log(parent) < log(n_leaf_indices_g)
        assert leaf_indices[parent] == grp[0]
        parent_msg = msgs * (parent * parent)
        assert parent_msg[1] == grp[1]
        assert parent_msg[GEN] == grp[2]
        halves = StackBuf(2)
        hint_witness(halves, "child_halves")
        assert log(halves[1]) < 2
        assert log(halves[0]) < MAX_KEYS
        assert halves[0] * halves[0] * halves[1] == n_keys
        gb = group_base[parent]
        prefix = counts[xj]
        kd_0, kd_1 = child_key_list_digest(xmss_table * (gb * gb), cover, base * prefix, gb, group_slots[parent], halves[0], halves[1], n_keys, g_squares)
        slot = run_ptr * (xj ** 8) * (GEN ** 4)
        slot[1] = grp[0]
        slot[GEN] = n_keys
        slot[GEN ** 2] = grp[1]
        slot[GEN ** 3] = grp[2]
        slot[GEN ** 4] = kd_0
        slot[GEN ** 5] = kd_1
        slot[GEN ** 6] = 0
        slot[GEN ** 7] = 0
        counts[xj * GEN] = prefix * n_keys
    return counts[nsub_e_g]


def main():
    # The coverage table is one region per (leaf index, message) group, its declared
    # keys then its duplicates; the first n_decl groups are the published set, the
    # n_drop after them hold covered but unpublished groups. Every slot is written
    # exactly once (write-once memory plus the final count), by a raw signature
    # verified at that group or by a child key mapped to that group, and each write
    # is range-checked into its own group's region.
    meta = StackBuf(3)
    hint_witness(meta, "meta")  # n_decl, n_drop, n_children, in the exponent
    n_decl_g = meta[0]
    n_drop_g = meta[1]
    n_children_g = meta[2]
    assert log(n_decl_g) < MAX_LEAF_INDICES + 1
    assert log(n_drop_g) < MAX_LEAF_INDICES + 1
    n_leaf_indices_g = n_decl_g * n_drop_g
    assert log(n_leaf_indices_g) < MAX_LEAF_INDICES + 1
    assert log(n_children_g) < MAX_RECURSIONS + 1

    # ---- geometry: per group its leaf index, message and slot counts ----
    leaf_indices = HeapBuf(n_leaf_indices_g)
    msgs = HeapBuf(n_leaf_indices_g * n_leaf_indices_g)
    group_n_keys = HeapBuf(n_leaf_indices_g)
    group_n_dups = HeapBuf(n_leaf_indices_g)
    group_n_raw = HeapBuf(n_leaf_indices_g)
    group_base = HeapBuf(n_leaf_indices_g)
    group_slots = HeapBuf(n_leaf_indices_g)
    geo = HeapBuf((n_leaf_indices_g * GEN) ** 4)  # [base, n_raw product]
    geo[1] = 1
    geo[GEN] = 1
    for xe in mul_range(1, n_leaf_indices_g):
        grp = StackBuf(6)
        hint_witness(grp, "group")  # leaf index, msg_lo, msg_hi, n, n_dup, n_raw
        assert log(grp[3]) < MAX_KEYS
        assert log(grp[4]) < MAX_KEYS
        assert log(grp[5]) < MAX_KEYS
        leaf_indices[xe] = grp[0]
        msg = msgs * (xe * xe)
        msg[1] = grp[1]
        msg[GEN] = grp[2]
        group_n_keys[xe] = grp[3]
        group_n_dups[xe] = grp[4]
        group_n_raw[xe] = grp[5]
        state = geo * (xe ** 4)
        base = state[1]
        group_base[xe] = base
        slots = grp[3] * grp[4]
        group_slots[xe] = slots
        nxt = geo * ((xe * GEN) ** 4)
        nxt[1] = base * slots
        nxt[GEN] = state[GEN] * grp[5]
    geo_end = geo * (n_leaf_indices_g ** 4)
    n_total_g = geo_end[1]
    n_raw_g = geo_end[GEN]
    assert log(n_total_g) < MAX_KEYS
    g_squares = squares_table()

    # ---- the signer set: rec_aggregation's signers_hash with no SPHINCS claims ----
    xmss_table = HeapBuf(n_total_g * n_total_g)
    signers_run = HeapBuf(n_decl_g ** 8 * GEN ** 4)
    signers_run[1] = n_decl_g
    signers_run[GEN] = 1
    signers_run[GEN ** 2] = SP_EMPTY_0
    signers_run[GEN ** 3] = SP_EMPTY_1
    decl_keys = HeapBuf(n_decl_g * GEN)
    decl_keys[GEN ** 0] = 1
    for xe in mul_range(1, n_decl_g):
        n_keys = group_n_keys[xe]
        base = group_base[xe]
        decl_keys[xe * GEN] = decl_keys[xe] * n_keys
        halves = StackBuf(2)
        hint_witness(halves, "pk_halves")
        assert log(halves[1]) < 2
        assert log(halves[0]) < MAX_KEYS
        assert halves[0] * halves[0] * halves[1] == n_keys
        kd_0, kd_1 = key_list_digest(xmss_table * (base * base), halves[0], halves[1], n_keys, g_squares)
        group_msg = msgs * (xe * xe)
        slot = signers_run * (xe ** 8) * (GEN ** 4)
        slot[1] = leaf_indices[xe]
        slot[GEN] = n_keys
        slot[GEN ** 2] = group_msg[1]
        slot[GEN ** 3] = group_msg[GEN]
        slot[GEN ** 4] = kd_0
        slot[GEN ** 5] = kd_1
        slot[GEN ** 6] = 0
        slot[GEN ** 7] = 0
    for xe in mul_range(1, n_leaf_indices_g):
        n_keys = group_n_keys[xe]
        base = group_base[xe]
        dup_ptr = xmss_table * (base * base * n_keys * n_keys)
        for xd in mul_range(1, group_n_dups[xe]):
            dup = dup_ptr * (xd * xd)
            hint_witness(dup[0:2], "dup_pubkeys")
    assert decl_keys[n_decl_g] != 1
    set_0, set_1 = plain_digest(signers_run, n_decl_g * n_decl_g * GEN, g_squares)

    # ---- coverage by raw signatures, one loop per group ----
    cover = HeapBuf(n_total_g)
    merkle_bits = HeapBuf(n_leaf_indices_g ** MERKLE_BIT_CELLS)
    tweak_tables = HeapBuf(n_leaf_indices_g ** N_TWEAK_CELLS)
    raw_count = HeapBuf(n_leaf_indices_g * GEN)
    raw_count[GEN ** 0] = 1
    for xe in mul_range(1, n_leaf_indices_g):
        n_raw = group_n_raw[xe]
        prefix = raw_count[xe]
        if n_raw != 1:
            tweak_table = tweak_tables * (xe ** N_TWEAK_CELLS)
            group_bits = merkle_bits * (xe ** MERKLE_BIT_CELLS)
            fill_xmss_leaf_index_tables(leaf_indices[xe], group_bits, tweak_table)
            slots = group_slots[xe]
            base = group_base[xe]
            keys = xmss_table * (base * base)
            group_msg = msgs * (xe * xe)
            for xi in mul_range(1, n_raw):
                idx = hint_witness("raw_index")
                assert log(idx) < log(slots)
                cover[base * idx] = prefix * xi
                verify_sig(group_msg, tweak_table, group_bits, keys * (idx * idx))
            raw_count[xe * GEN] = prefix * n_raw
        else:
            raw_count[xe * GEN] = prefix

    # ---- coverage by children: each child's set rebuilt from this node's table ----
    node_run = HeapBuf((n_children_g * GEN) ** 4)
    written = HeapBuf(n_children_g * GEN)
    written[GEN ** 0] = n_raw_g
    for xc in mul_range(1, n_children_g):
        base = written[xc]
        nsub_e_g = hint_witness("child_meta")
        assert log(nsub_e_g) < MAX_LEAF_INDICES + 1
        sub_run = HeapBuf(nsub_e_g ** 8 * GEN ** 4)
        sub_run[1] = nsub_e_g
        sub_run[GEN] = 1
        sub_run[GEN ** 2] = SP_EMPTY_0
        sub_run[GEN ** 3] = SP_EMPTY_1
        nsub_x_g = rebuild_child_groups(nsub_e_g, sub_run, base, leaf_indices, msgs, group_base, group_slots, n_leaf_indices_g, xmss_table, cover, g_squares)
        sub_0, sub_1 = plain_digest(sub_run, nsub_e_g * nsub_e_g * GEN, g_squares)
        entry = node_run * (xc ** 4) * (GEN ** 4)
        entry[1] = sub_0
        entry[GEN] = sub_1
        entry[GEN ** 2] = 0
        entry[GEN ** 3] = 0
        written[xc * GEN] = base * nsub_x_g
    assert written[n_children_g] == n_total_g

    # ---- the statement ----
    # A leaf publishes its signer-set digest; a merge publishes the digest of
    # [n_children, 0, set digest] and one block per child set digest. The zero
    # second cell keeps it apart from a signer-set string, whose second cell is 1.
    pub_ptr = GEN ** 0
    if n_children_g == 1:
        pub_ptr[1] = set_0
        pub_ptr[GEN] = set_1
    else:
        node_run[1] = n_children_g
        node_run[GEN] = 0
        node_run[GEN ** 2] = set_0
        node_run[GEN ** 3] = set_1
        st_0, st_1 = plain_digest(node_run, n_children_g * GEN, g_squares)
        pub_ptr[1] = st_0
        pub_ptr[GEN] = st_1
    return
