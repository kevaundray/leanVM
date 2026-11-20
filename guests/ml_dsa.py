# ML-DSA (FIPS 204) signature verification: ML-DSA.Verify_internal on N_SIGS claims.
#
# A claim is (pk, mu, sig). The guest hashes pk into tr = H(pk, 64) itself and publishes,
# for each claim, Keccak-256(tr || mu), chained: the public input is d_1 = c_0 and
# d_{s+1} = Keccak-256(d_s || c_s). Whoever checks a claim on (pk, M) computes mu from tr and
# the message, as Verify does, so the guest never reads a message.
#
# Arithmetic mod q lives in the exponent: an integer v is the field element g^v, exact while
# |v| < 2^63, so + is MUL and a product by a constant is a power. A reduction v = r + q t is
# advice, r and t in 12-bit limbs, each range checked and weighted by a table lookup. SHAKE
# runs on the KECCAK permutation, absorbing its own blocks; bytes enter as hinted g-powers,
# each range checked and tied back to its lane through a table of its bits. The widest range
# checks, z's 2 ZB + 1 and UseHint's gamma2, need a memory past them, which every run's own
# size gives.
from snark_lib import *

K = K_PLACEHOLDER
L = L_PLACEHOLDER
TAU = TAU_PLACEHOLDER
OMEGA = OMEGA_PLACEHOLDER
GAMMA2 = GAMMA2_PLACEHOLDER
W1_BITS = W1_BITS_PLACEHOLDER
ZB = ZB_PLACEHOLDER  # gamma1 - beta - 1: a valid z has |z_i| <= ZB
CT_LANES = CT_LANES_PLACEHOLDER  # c~ is lambda / 4 bytes, CT_LANES lanes
N_SIGS = N_SIGS_PLACEHOLDER
# UseHint by table: index k' = r1 + (M_W1 + 1) s + (2 M_W1 + 1) h, for the hint bit h, r0 > 0
# as s, and r1 = HighBits; each array gives one column, from the host.
UH_D = UH_D_PLACEHOLDER  # r1 * 2 gamma2 + s * gamma2
UH_H = UH_H_PLACEHOLDER  # h
UH_W1 = UH_W1_PLACEHOLDER  # UseHint's result

Q = 8380417
M_W1 = (Q - 1) // (2 * GAMMA2)
NKP = 4 * M_W1 + 2
Y_TOWER = 18446744073709551616
PAD_FIRST = 31  # SHAKE's suffix 1111 and pad10*1's first bit
PAD_LAST = 9223372036854775808  # pad10*1's last bit, the top of a lane
PAD128_LAST = PAD_LAST * Y_TOWER  # SHAKE128's last rate lane, lane 20, is cell 10's high limb

PK_LANES = 4 + 40 * K
PK_BLOCKS = (8 * PK_LANES + 136) // 136
NW1 = 4 * K * W1_BITS  # lanes of w1Encode
W1H_BLOCKS = (64 + 8 * NW1 + 136) // 136
CHW = CHW_PLACEHOLDER  # w1 coefficients a packing chunk, 64 / gcd(64, W1_BITS): LPC whole lanes
LPC = W1_BITS * CHW // 64
NCH = 256 // CHW
EXA_STRIDE = 280  # accepted candidates a poly can take: five blocks of 56
EXA_POLY = 3 * EXA_STRIDE  # its three limb arrays

# NTT^-1's outputs carry 512 (its 256 and the pointwise products' 2), so NTT(z) takes f = 512^-1 mod q
# with z: layer 0 multiplies both its inputs, by f and by f zeta_1, the twiddles 256 and 257 of the tables.
F512 = 8364049
FZ1 = 8357072  # f zeta_1 mod q
KF = F512 * ZB - Q * (F512 * ZB // Q)  # f ZB mod q
KFZ = FZ1 * ZB - Q * (FZ1 * ZB // Q)  # f zeta_1 ZB mod q
GQ = GEN ** Q
GQ4 = GEN ** (4 * Q)

# Tables in main's frame, which starts at cell TB; a sub-table of 256 holds byte v at v.
TB = 2
OFF_LB = 0  # 8: byte v as lane byte k, v << 8k
OFF_T1 = 2048  # 8: a t1 coefficient's share of byte v, times 2^d, in the exponent
OFF_X256 = 4096  # g^(256 v)
OFF_M127 = 4352  # g^(v & 127)
OFF_TOP = 4608  # v & 127 == 127
OFF_SG = 4864  # 8: g^(256 bit_t(v))
OFF_S12 = 6912  # 2048: g^(4096 v)
# Squares for the pointwise products: SQ_kl[s] = g^(2^(12k + 8l) s^2), s up to a 12- or 11-bit limb of
# NTT(z) plus a byte (or b2 & 127) of A.
OFF_SQ00 = 8960
OFF_SQ01 = OFF_SQ00 + 4351
OFF_SQ02 = OFF_SQ01 + 4351
OFF_SQ10 = OFF_SQ02 + 4223
OFF_SQ11 = OFF_SQ10 + 2303
OFF_SQ12 = OFF_SQ11 + 2303
SQ_OFF = [OFF_SQ00, OFF_SQ01, OFF_SQ02, OFF_SQ10, OFF_SQ11, OFF_SQ12]
OFF_BC = OFF_SQ12 + 2175  # 3: g^(4097 256^l v^2), byte l of A's share of its squares
OFF_R6 = OFF_BC + 768  # 3: g^(64^k v), k = 1..3
OFF_QU = OFF_R6 + 192  # 1024: g^(q v)
OFF_W9 = OFF_QU + 1024  # 3 of 512: g^(q 2^(9k) v)
OFF_TW = OFF_W9 + 1536  # 257 twiddles of 64, 64, 64, 32: g^(zeta_i 64^k v mod q), then f and f zeta_1
OFF_UH = OFF_TW + 257 * 224  # 7 columns of NKP: D, H, w1, the two straddles' low and high parts
TAB_SIZE = OFF_UH + 7 * NKP

ZETAS = [1, 4808194, 3765607, 3761513, 5178923, 5496691, 5234739, 5178987, 7778734, 3542485, 2682288, 2129892, 3764867, 7375178, 557458, 7159240, 5010068, 4317364, 2663378, 6705802, 4855975, 7946292, 676590, 7044481, 5152541, 1714295, 2453983, 1460718, 7737789, 4795319, 2815639, 2283733, 3602218, 3182878, 2740543, 4793971, 5269599, 2101410, 3704823, 1159875, 394148, 928749, 1095468, 4874037, 2071829, 4361428, 3241972, 2156050, 3415069, 1759347, 7562881, 4805951, 3756790, 6444618, 6663429, 4430364, 5483103, 3192354, 556856, 3870317, 2917338, 1853806, 3345963, 1858416, 3073009, 1277625, 5744944, 3852015, 4183372, 5157610, 5258977, 8106357, 2508980, 2028118, 1937570, 4564692, 2811291, 5396636, 7270901, 4158088, 1528066, 482649, 1148858, 5418153, 7814814, 169688, 2462444, 5046034, 4213992, 4892034, 1987814, 5183169, 1736313, 235407, 5130263, 3258457, 5801164, 1787943, 5989328, 6125690, 3482206, 4197502, 7080401, 6018354, 7062739, 2461387, 3035980, 621164, 3901472, 7153756, 2925816, 3374250, 1356448, 5604662, 2683270, 5601629, 4912752, 2312838, 7727142, 7921254, 348812, 8052569, 1011223, 6026202, 4561790, 6458164, 6143691, 1744507, 1753, 6444997, 5720892, 6924527, 2660408, 6600190, 8321269, 2772600, 1182243, 87208, 636927, 4415111, 4423672, 6084020, 5095502, 4663471, 8352605, 822541, 1009365, 5926272, 6400920, 1596822, 4423473, 4620952, 6695264, 4969849, 2678278, 4611469, 4829411, 635956, 8129971, 5925040, 4234153, 6607829, 2192938, 6653329, 2387513, 4768667, 8111961, 5199961, 3747250, 2296099, 1239911, 4541938, 3195676, 2642980, 1254190, 8368000, 2998219, 141835, 8291116, 2513018, 7025525, 613238, 7070156, 6161950, 7921677, 6458423, 4040196, 4908348, 2039144, 6500539, 7561656, 6201452, 6757063, 2105286, 6006015, 6346610, 586241, 7200804, 527981, 5637006, 6903432, 1994046, 2491325, 6987258, 507927, 7192532, 7655613, 6545891, 5346675, 8041997, 2647994, 3009748, 5767564, 4148469, 749577, 4357667, 3980599, 2569011, 6764887, 1723229, 1665318, 2028038, 1163598, 5011144, 3994671, 8368538, 7009900, 3020393, 3363542, 214880, 545376, 7609976, 3105558, 7277073, 508145, 7826699, 860144, 3430436, 140244, 6866265, 6195333, 3123762, 2358373, 6187330, 5365997, 6663603, 2926054, 7987710, 8077412, 3531229, 4405932, 4606686, 1900052, 7598542, 1054478, 7648983]


def main():
    tab = StackBuf(TAB_SIZE)
    for v in unroll(0, 256):
        for k in unroll(0, 8):
            tab[OFF_LB + 256 * k + v] = const(v * 2 ** (8 * k))
            tab[OFF_SG + 256 * k + v] = GEN ** const(256 * ((v // 2 ** k) % 2))
        # t1 = b0 | (b1 & 3) << 8, (b1 >> 2) | (b2 & 15) << 6, (b2 >> 4) | (b3 & 63) << 4, (b3 >> 6) | b4 << 2
        tab[OFF_T1 + v] = GEN ** const(v * 8192)
        tab[OFF_T1 + 256 + v] = GEN ** const((v % 4) * 256 * 8192)
        tab[OFF_T1 + 512 + v] = GEN ** const((v // 4) * 8192)
        tab[OFF_T1 + 768 + v] = GEN ** const((v % 16) * 64 * 8192)
        tab[OFF_T1 + 1024 + v] = GEN ** const((v // 16) * 8192)
        tab[OFF_T1 + 1280 + v] = GEN ** const((v % 64) * 16 * 8192)
        tab[OFF_T1 + 1536 + v] = GEN ** const((v // 64) * 8192)
        tab[OFF_T1 + 1792 + v] = GEN ** const(v * 4 * 8192)
        tab[OFF_X256 + v] = GEN ** const(256 * v)
        tab[OFF_M127 + v] = GEN ** const(v % 128)
        if const(v % 128 == 127):
            tab[OFF_TOP + v] = 1
        else:
            tab[OFF_TOP + v] = 0
    for v in unroll(0, 2048):
        tab[OFF_S12 + v] = GEN ** const(4096 * v)
    # `GEN ** e` takes e below 2^32, so a wider exponent is a power of a power.
    for s in unroll(0, 4351):
        tab[OFF_SQ00 + s] = GEN ** const(s * s)
        tab[OFF_SQ01 + s] = (GEN ** 256) ** const(s * s)
    for s in unroll(0, 4223):
        tab[OFF_SQ02 + s] = (GEN ** 65536) ** const(s * s)
    for s in unroll(0, 2303):
        tab[OFF_SQ10 + s] = (GEN ** 4096) ** const(s * s)
        tab[OFF_SQ11 + s] = (GEN ** 1048576) ** const(s * s)
    for s in unroll(0, 2175):
        tab[OFF_SQ12 + s] = (GEN ** 268435456) ** const(s * s)
    for v in unroll(0, 256):
        for l in unroll(0, 3):
            tab[OFF_BC + 256 * l + v] = (GEN ** const(4097 * 256 ** l)) ** const(v * v)
    for v in unroll(0, 64):
        for k in unroll(0, 3):
            tab[OFF_R6 + 64 * k + v] = GEN ** const(64 ** (k + 1) * v)
    for v in unroll(0, 1024):
        tab[OFF_QU + v] = GQ ** v
    for v in unroll(0, 512):
        for k in unroll(0, 3):
            tab[OFF_W9 + 512 * k + v] = (GQ ** const(512 ** k)) ** v
    for zi in unroll(1, 256):
        for k in unroll(0, 4):
            for v in unroll(0, 64 - 32 * (k // 3)):
                tab[OFF_TW + 224 * zi - 224 + 64 * k + v] = GEN ** const(ZETAS[zi] * 64 ** k * v % Q)
    for k in unroll(0, 4):
        for v in unroll(0, 64 - 32 * (k // 3)):
            tab[OFF_TW + 224 * 255 + 64 * k + v] = GEN ** const(F512 * 64 ** k * v % Q)
            tab[OFF_TW + 224 * 256 + 64 * k + v] = GEN ** const(FZ1 * 64 ** k * v % Q)
    for kp in unroll(0, NKP):
        tab[OFF_UH + kp] = GEN ** UH_D[kp]
        tab[OFF_UH + NKP + kp] = GEN ** UH_H[kp]
        tab[OFF_UH + 2 * NKP + kp] = UH_W1[kp]
        # A 6-bit w1 straddles a lane at bit 60 and at bit 62.
        tab[OFF_UH + 3 * NKP + kp] = const((UH_W1[kp] % 16) * 2 ** 60)
        tab[OFF_UH + 4 * NKP + kp] = const(UH_W1[kp] // 16)
        tab[OFF_UH + 5 * NKP + kp] = const((UH_W1[kp] % 4) * 2 ** 62)
        tab[OFF_UH + 6 * NKP + kp] = const(UH_W1[kp] // 4)
    tp = addr(tab)
    # Lookups name a table cell absolutely, as cell TB + OFF + v of the frame at g^0.
    assert tp == GEN ** TB
    digs = HeapBuf(2 * N_SIGS)
    for s in mul_range(1, GEN ** N_SIGS):
        verify_sig(tp, digs * s * s)
    acc = StackBuf(2)
    acc[0] = digs[1]
    acc[1] = digs[GEN]
    for s in unroll(1, N_SIGS):
        nxt = StackBuf(2)
        keccak(acc, [digs[GEN ** (2 * s)], digs[GEN ** (2 * s + 1)]], nxt)
        acc = nxt
    p = GEN ** 0
    p[1] = acc[0]
    p[GEN] = acc[1]
    return


def verify_sig(tp, dg):
    # pk = rho || t1: rho hinted as lanes, t1 as bytes; both go into the lanes tr hashes.
    ml = HeapBuf(17 * PK_BLOCKS)
    hint_witness(ml[0:4], "rho")
    s1 = HeapBuf(1024 * K)
    for i in unroll(0, K):
        t1_row(tp, ml * GEN ** (4 + 40 * i), s1 * GEN ** (1024 * i))
    pad_lanes(ml, PK_LANES, PK_BLOCKS)
    tr = absorb17(ml, PK_BLOCKS)
    hl = HeapBuf(17 * W1H_BLOCKS)
    hint_witness(hl[0:8], "mu")
    mc = [hl[1] + Y_TOWER * hl[GEN], hl[GEN ** 2] + Y_TOWER * hl[GEN ** 3], hl[GEN ** 4] + Y_TOWER * hl[GEN ** 5], hl[GEN ** 6] + Y_TOWER * hl[GEN ** 7]]
    dig = StackBuf(2)
    keccak(tr[0:2], tr[2:4], dig, tail=mc)
    dg[1] = dig[0]
    dg[GEN] = dig[1]

    a = HeapBuf(EXA_POLY * K * L)
    rc0 = ml[1] + Y_TOWER * ml[GEN]
    rc1 = ml[GEN ** 2] + Y_TOWER * ml[GEN ** 3]
    for i in unroll(0, K):
        for j in unroll(0, L):
            expand_poly(tp, rc0, rc1, const(j + 256 * i + PAD_FIRST * 65536), a * GEN ** (EXA_POLY * (L * i + j)))

    ct = HeapBuf(CT_LANES)
    hint_witness(ct[0:CT_LANES], "ct")
    pp = HeapBuf(TAU)
    sample_in_ball(tp, ct, s1, pp)

    zh = HeapBuf(768 * L)
    for j in unroll(0, L):
        ntt_fwd(zh * GEN ** (768 * j))
    wb = HeapBuf(256 * K)
    pointwise(a, zh, wb)
    ob = HeapBuf(256 * K)
    for i in unroll(0, K):
        intt(wb * GEN ** (256 * i), ob * GEN ** (256 * i))
    zc = HeapBuf(256 * K)
    sparse_ct1(pp, zc)

    hw = HeapBuf(NCH * K)
    for i in unroll(0, K):
        final_row(ob * GEN ** (256 * i), zc * GEN ** (256 * i), hl * GEN ** (8 + 4 * W1_BITS * i), hw * GEN ** (NCH * i))
    weight = hw[1]
    for n in unroll(1, NCH * K):
        weight = weight * hw[GEN ** n]
    assert log(weight) < OMEGA + 1
    pad_lanes(hl, 8 + NW1, W1H_BLOCKS)
    st = absorb17(hl, W1H_BLOCKS)
    for c in unroll(0, CT_LANES // 2):
        st[c] = ct[GEN ** (2 * c)] + Y_TOWER * ct[GEN ** (2 * c + 1)]
    return


# ================================ SHAKE on KECCAK ================================


@inline
def pad_lanes(ln, n: Const, nblocks: Const):
    # pad10*1 after n message lanes, to nblocks blocks of 17 lanes.
    ln[GEN ** n] = PAD_FIRST
    for m in unroll(n + 1, 17 * nblocks - 1):
        ln[GEN ** m] = 0
    ln[GEN ** (17 * nblocks - 1)] = PAD_LAST
    return


@inline
def absorb17(ln, nblocks: Const):
    # SHAKE256's absorption of the 17 nblocks lanes at ln, padded: the state after it,
    # whose first rate lanes are the first output.
    for b in unroll(0, nblocks):
        nx = StackBuf(13)
        for c in unroll(0, 8):
            cell = ln[GEN ** (17 * b + 2 * c)] + Y_TOWER * ln[GEN ** (17 * b + 2 * c + 1)]
            if const(b == 0):
                nx[c] = cell
            else:
                nx[c] = st[c] + cell
        if const(b == 0):
            nx[8] = ln[GEN ** 16]
            for c in unroll(9, 13):
                nx[c] = 0
        else:
            nx[8] = st[8] + ln[GEN ** (17 * b + 16)]
            for c in unroll(9, 13):
                nx[c] = st[c]
        st = StackBuf(13)
        keccak(nx[0:2], nx[2:4], st, tail=nx[4:8], cap=nx)
    return st


@inline
def lane_of(tp, eb, at: Const):
    # The lane whose eight bytes, low first, are hinted at eb[at..at+8] in the exponent.
    for k in unroll(0, 8):
        e = eb[at + k]
        assert log(e) < 256
        if const(k == 0):
            acc = tp[e * GEN ** OFF_LB]
        else:
            acc = acc + tp[e * GEN ** (OFF_LB + 256 * k)]
    return acc


# ===================================== t1 ========================================


def t1_row(tp, ml, s1):
    # Row i of t1: its 40 lanes into ml and its 256 coefficients, times 2^d, into the
    # row's sparse-product table s1: [g^T | g^-T | g^T | g^-T].
    for u in mul_range(1, GEN ** 8):
        t1_unit(tp, ml * u ** 5, s1 * u ** 32)
    return


def t1_unit(tp, ml, s1):
    # Five lanes, 40 bytes, 32 coefficients of ten bits.
    eb = StackBuf(40)
    hint_witness(eb, "t1")
    for w in unroll(0, 5):
        ml[GEN ** w] = lane_of(tp, eb, 8 * w)
    for g in unroll(0, 8):
        b0 = tp * eb[5 * g]
        b1 = tp * eb[5 * g + 1]
        b2 = tp * eb[5 * g + 2]
        b3 = tp * eb[5 * g + 3]
        b4 = tp * eb[5 * g + 4]
        t1_store(s1, 4 * g, b0[GEN ** OFF_T1] * b1[GEN ** (OFF_T1 + 256)])
        t1_store(s1, 4 * g + 1, b1[GEN ** (OFF_T1 + 512)] * b2[GEN ** (OFF_T1 + 768)])
        t1_store(s1, 4 * g + 2, b2[GEN ** (OFF_T1 + 1024)] * b3[GEN ** (OFF_T1 + 1280)])
        t1_store(s1, 4 * g + 3, b3[GEN ** (OFF_T1 + 1536)] * b4[GEN ** (OFF_T1 + 1792)])
    return


@inline
def t1_store(s1, n: Const, gt):
    s1[GEN ** n] = gt
    s1[GEN ** (n + 512)] = gt
    gi = 1 / gt
    s1[GEN ** (n + 256)] = gi
    s1[GEN ** (n + 768)] = gi
    return


# =================================== ExpandA =====================================


def expand_poly(tp, rc0, rc1, lane4, ap):
    # RejNTTPoly(rho || s || r): SHAKE128, five squeezed blocks of 56 three-byte
    # candidates, the accepted ones' limbs (b0, b1, b2 & 127) in the exponent at ap.
    cp = [0, 0, PAD128_LAST, 0, 0]
    st = StackBuf(13)
    keccak([rc0, rc1], [lane4, 0], st, tail=[0, 0, 0, 0], cap=cp)
    cnt = expand_block(tp, st, ap, GEN ** 0)
    for b in unroll(1, 5):
        nx = StackBuf(13)
        keccak(st[0:2], st[2:4], nx, tail=st[4:8], cap=st)
        st = nx
        cnt = expand_block(tp, st, ap, cnt)
    # At least 256 accepted; any past them are never read.
    assert log(cnt / GEN ** 256) < EXA_STRIDE - 255
    return


def expand_block(tp, st: StackBuf(13), ap, cnt):
    # The 21 rate lanes of st, as 168 hinted bytes.
    eb = StackBuf(168)
    hint_witness(eb, "exa")
    for c in unroll(0, 8):
        st[c] = lane_of(tp, eb, 16 * c) + Y_TOWER * lane_of(tp, eb, 16 * c + 8)
    st[8] = lane_of(tp, eb, 128)
    st[9] = lane_of(tp, eb, 136) + Y_TOWER * lane_of(tp, eb, 144)
    st[10] = lane_of(tp, eb, 152) + Y_TOWER * lane_of(tp, eb, 160)
    for c in unroll(0, 56):
        cnt = candidate(tp, eb, ap, cnt, c)
    return cnt


@inline
def candidate(tp, eb, ap, cnt, c: Const):
    # Candidate b0 + 256 b1 + 65536 (b2 & 127) is below q unless b2 & 127 == 127 and
    # b0 + 256 b1 > 0xE000; only then does the prover say which.
    e0 = eb[3 * c]
    e1 = eb[3 * c + 1]
    e2 = eb[3 * c + 2]
    nc = StackBuf(1)
    if tp[e2 * GEN ** OFF_TOP] == 0:
        accept(tp, ap, cnt, e0, e1, e2)
        nc[0] = cnt * GEN
    else:
        y = e0 * tp[e1 * GEN ** OFF_X256]
        rej = hint_witness("exr")
        if rej == 0:
            assert log(y) < 57345
            accept(tp, ap, cnt, e0, e1, e2)
            nc[0] = cnt * GEN
        else:
            assert log(y / GEN ** 57345) < 8191
            nc[0] = cnt
    return nc[0]


@inline
def accept(tp, ap, cnt, e0, e1, e2):
    p = ap * cnt
    p[1] = e0
    p[GEN ** EXA_STRIDE] = e1
    p[GEN ** (2 * EXA_STRIDE)] = tp[e2 * GEN ** OFF_M127]
    return


# ================================= SampleInBall ==================================


@inline
def sib_lane(ct, n: Const):
    if const(n // CT_LANES == 0):
        v = ct[GEN ** n]
    elif const(n == CT_LANES):
        v = PAD_FIRST
    elif const(n == 16):
        v = PAD_LAST
    else:
        v = 0
    return v


def sample_in_ball(tp, ct, s1, pp):
    # c = SampleInBall(c~), as the pointers its sparse product reads: nonzero k at
    # position p with sign bit b is s1 g^(256 - p + 256 b), read at + m for coefficient m.
    nx = StackBuf(13)
    for c in unroll(0, 8):
        nx[c] = sib_lane(ct, 2 * c) + Y_TOWER * sib_lane(ct, 2 * c + 1)
    nx[8] = PAD_LAST
    for c in unroll(9, 13):
        nx[c] = 0
    st = StackBuf(13)
    keccak(nx[0:2], nx[2:4], st, tail=nx[4:8], cap=nx)
    eb = StackBuf(136)
    hint_witness(eb, "sib")
    for c in unroll(0, 8):
        st[c] = lane_of(tp, eb, 16 * c) + Y_TOWER * lane_of(tp, eb, 16 * c + 8)
    st[8] = lane_of(tp, eb, 128)
    # The positions j_k: byte t is taken while k < TAU, accepted if j <= i = 256 - TAU + k.
    jb = HeapBuf(TAU)
    # A cell, so that every step's bound is a runtime one.
    kc0 = StackBuf(1)
    kc0[0] = GEN ** 0
    kc = kc0[0]
    for t in unroll(8, 136):
        nc = StackBuf(1)
        sib_step(eb, jb, kc, nc, t)
        kc = nc[0]
    assert kc == GEN ** TAU
    # Step k sets c_i = c_j, c_j = sign k: the sign sitting at j_k moves to i.
    pos = StackBuf(TAU)
    pos[0] = jb[1]
    for k in unroll(1, TAU):
        jk = jb[GEN ** k]
        nxt = StackBuf(TAU)
        for m in unroll(0, k):
            sib_move(pos, nxt, jk, m, k)
        nxt[k] = jk
        pos = nxt
    for k in unroll(0, TAU):
        sg = tp[eb[k // 8] * GEN ** (OFF_SG + 256 * (k % 8))]
        pp[GEN ** k] = s1 * GEN ** 256 * sg / pos[k]
    return


@inline
def sib_step(eb, jb, kc, nc, t: Const):
    if kc == GEN ** TAU:
        nc[0] = kc
    else:
        e = eb[t]
        f = hint_witness("sibf")
        bound = kc * GEN ** (257 - TAU)
        if f == 0:
            assert log(e) < log(bound)
            jb[kc] = e
            nc[0] = kc * GEN
        else:
            assert log(e / bound) < 256
            nc[0] = kc
    return


@inline
def sib_move(pos, nxt, jk, m: Const, k: Const):
    if pos[m] == jk:
        nxt[m] = GEN ** (256 - TAU + k)
    else:
        nxt[m] = pos[m]
    return


def sparse_ct1(pp, zc):
    # zc row i, coefficient m: g^(-(c t1 2^d)_m), eight coefficients a frame.
    for mm in mul_range(1, GEN ** 32):
        m8 = mm ** 8
        for k in unroll(0, TAU):
            p = pp[GEN ** k] * m8
            nacc = StackBuf(8 * K)
            for i in unroll(0, K):
                for c in unroll(0, 8):
                    if const(k == 0):
                        nacc[8 * i + c] = p[GEN ** (1024 * i + c)]
                    else:
                        nacc[8 * i + c] = acc[8 * i + c] * p[GEN ** (1024 * i + c)]
            acc = nacc
        for i in unroll(0, K):
            for c in unroll(0, 8):
                zc[m8 * GEN ** (256 * i + c)] = acc[8 * i + c]
    return


# ===================================== NTT =======================================


@inline
def tw_mul(b, zi: Const, wq: Const):
    # t = sum_k T_k[j_k] = zeta_zi b (mod q), t < 4q, for the advice b = r + q u with r = sum_k 64^k j_k,
    # j_3 < 32 and the others below 64, and u < 1024 (u = 0 when wq = 0): an identity of integers, both
    # sides being below 2^34.
    h = StackBuf(5)
    hint_witness(h[0:4 + wq], "tw")
    assert log(h[0]) < 64
    assert log(h[1]) < 64
    assert log(h[2]) < 64
    assert log(h[3]) < 32
    e0 = h[0]
    e1 = h[1]
    e2 = h[2]
    e3 = h[3]
    if const(wq == 1):
        assert log(h[4]) < 1024
        eu = h[4]
        assert b == e0 * e1[GEN ** (TB + OFF_R6)] * e2[GEN ** (TB + OFF_R6 + 64)] * e3[GEN ** (TB + OFF_R6 + 128)] * eu[GEN ** (TB + OFF_QU)]
    else:
        assert b == e0 * e1[GEN ** (TB + OFF_R6)] * e2[GEN ** (TB + OFF_R6 + 64)] * e3[GEN ** (TB + OFF_R6 + 128)]
    t = e0[GEN ** (TB + OFF_TW + 224 * zi - 224)] * e1[GEN ** (TB + OFF_TW + 224 * zi - 160)] * e2[GEN ** (TB + OFF_TW + 224 * zi - 96)] * e3[GEN ** (TB + OFF_TW + 224 * zi - 32)]
    return t


def ntt_fwd(zo):
    # f NTT(z) in the frame from the hinted z + ZB, both inputs of layer 0 multiplied (by f and f zeta_1),
    # lifted to f z and f zeta_1 z by constants: values below 10 q after layer 0, each later layer adding
    # less than 4q, so below 38 q throughout. Reduced into zo: limbs x0 < 2^12 at m and x1 < 2^11 at
    # 256 + m, and at 512 + m their squares' share of the pointwise products.
    zz = StackBuf(256)
    hint_witness(zz, "z")
    v = StackBuf(256)
    for n in unroll(0, 128):
        assert log(zz[n]) < 2 * ZB + 1
        assert log(zz[n + 128]) < 2 * ZB + 1
        a = tw_mul(zz[n], 256, 0)
        t = tw_mul(zz[n + 128], 257, 0)
        v[n] = a * t * GEN ** (2 * Q - KF - KFZ)
        v[n + 128] = a * GEN ** (5 * Q - KF + KFZ) / t
    for lay in unroll(1, 8):
        nv = StackBuf(256)
        for blk in unroll(0, 2 ** lay):
            for jj in unroll(0, 2 ** (7 - lay)):
                a = v[2 ** (8 - lay) * blk + jj]
                t = tw_mul(v[2 ** (8 - lay) * blk + jj + 2 ** (7 - lay)], 2 ** lay + blk, 1)
                nv[2 ** (8 - lay) * blk + jj] = a * t
                nv[2 ** (8 - lay) * blk + jj + 2 ** (7 - lay)] = a * GQ4 / t
        v = nv
    for m in unroll(0, 256):
        h = StackBuf(3)
        hint_witness(h, "zr")
        assert log(h[0]) < 4096
        assert log(h[1]) < 2048
        assert log(h[2]) < 1024
        x0 = h[0]
        x1 = h[1]
        xu = h[2]
        assert v[m] == x0 * x1[GEN ** (TB + OFF_S12)] * xu[GEN ** (TB + OFF_QU)]
        zo[GEN ** m] = x0
        zo[GEN ** (256 + m)] = x1
        zo[GEN ** (512 + m)] = x0[GEN ** (TB + OFF_SQ00)] * x0[GEN ** (TB + OFF_SQ01)] * x0[GEN ** (TB + OFF_SQ02)] * x1[GEN ** (TB + OFF_SQ10)] * x1[GEN ** (TB + OFF_SQ11)] * x1[GEN ** (TB + OFF_SQ12)]
    return


@inline
def reduce_w(x):
    # g^r for x = g^(r + q t), r < 2^23 in limbs of 12 and 11 bits and t < 2^27 in three of 9: both sides
    # are below 2^51.
    h = StackBuf(5)
    hint_witness(h, "wr")
    assert log(h[0]) < 4096
    assert log(h[1]) < 2048
    assert log(h[2]) < 512
    assert log(h[3]) < 512
    assert log(h[4]) < 512
    r1 = h[1]
    t0 = h[2]
    t1 = h[3]
    t2 = h[4]
    r = h[0] * r1[GEN ** (TB + OFF_S12)]
    assert x == r * t0[GEN ** (TB + OFF_W9)] * t1[GEN ** (TB + OFF_W9 + 512)] * t2[GEN ** (TB + OFF_W9 + 1024)]
    return r


def pointwise(a, zh, wb):
    # 2 sum_j A_ij NTT(z_j), from 2 x y = (x + y)^2 - x^2 - y^2 over the limbs x of NTT(z) and y of A (its
    # bytes, b2 & 127): SQ_kl read at the pointer g^(x + y), less A's squares (BC) and NTT(z)'s (stored
    # with it). The sum is below 2^50; the doubling rides into NTT^-1, whose last step takes 512^-1.
    for mm in mul_range(1, GEN ** 256):
        pa = a * mm
        pz = zh * mm
        pw = wb * mm
        zv = StackBuf(2 * L)
        for j in unroll(0, L):
            zv[2 * j] = pz[GEN ** (768 * j)]
            zv[2 * j + 1] = pz[GEN ** (768 * j + 256)]
            if const(j == 0):
                zsq = pz[GEN ** 512]
            else:
                zsq = zsq * pz[GEN ** (768 * j + 512)]
        for i in unroll(0, K):
            for j in unroll(0, L):
                e = [pa[GEN ** (EXA_POLY * (L * i + j))], pa[GEN ** (EXA_POLY * (L * i + j) + EXA_STRIDE)], pa[GEN ** (EXA_POLY * (L * i + j) + 2 * EXA_STRIDE)]]
                for l in unroll(0, 3):
                    el = e[l]
                    for k in unroll(0, 2):
                        p = zv[2 * j + k] * el
                        f = p[GEN ** (TB + SQ_OFF[3 * k + l])]
                        if const(j + l + k == 0):
                            num = f
                        else:
                            num = num * f
                    if const(j + l == 0):
                        den = el[GEN ** (TB + OFF_BC)]
                    else:
                        den = den * el[GEN ** (TB + OFF_BC + 256 * l)]
            pw[GEN ** (256 * i)] = reduce_w(num / (den * zsq))
    return


def intt(wi, oo):
    # NTT^-1 without its factor 256^-1 in the frame, from inputs below 2^23: values entering layer lay > 0
    # are below 2^(lay + 1) q, by which each difference is lifted; the outputs, below 512 q, into oo.
    v = StackBuf(256)
    for m in unroll(0, 256):
        v[m] = wi[GEN ** m]
    for lay in unroll(0, 8):
        nv = StackBuf(256)
        for blk in unroll(0, 2 ** (7 - lay)):
            for jj in unroll(0, 2 ** lay):
                a = v[2 ** (lay + 1) * blk + jj]
                b = v[2 ** (lay + 1) * blk + jj + 2 ** lay]
                nv[2 ** (lay + 1) * blk + jj] = a * b
                nv[2 ** (lay + 1) * blk + jj + 2 ** lay] = tw_mul(b * GEN ** const(Q * 2 ** (lay + 1)) / a, 2 ** (8 - lay) - 1 - blk, 1)
        v = nv
    for m in unroll(0, 256):
        oo[GEN ** m] = v[m]
    return


# ================================ UseHint and w1 =================================


def final_row(o, zc, hl, hw):
    # Row i: w' = o - c t1 2^d, Decompose and UseHint by table, w1 packed into the lanes c~' hashes, the
    # hint bits' count into hw, one chunk of lanes a frame.
    for cc in mul_range(1, GEN ** NCH):
        base = cc ** CHW
        po = o * base
        pz = zc * base
        us = StackBuf(CHW)
        for c in unroll(0, CHW):
            us[c] = use_hint(po[GEN ** c], pz[GEN ** c])
        for c in unroll(0, CHW):
            uc = us[c]
            if const(c == 0):
                wt = uc[GEN ** (TB + OFF_UH + NKP)]
            else:
                wt = wt * uc[GEN ** (TB + OFF_UH + NKP)]
        hw[cc] = wt
        pl = hl * cc ** LPC
        for ln in unroll(0, LPC):
            pl[GEN ** ln] = w1_lane(us, ln)
    return


@inline
def use_hint(ov, zv):
    # x = o + Z + 64 q + gamma2 - 1 = D(k') + u + q t with u < gamma2 and t < 1024, both sides below 2^33
    # (o < 512 q, |Z| < 64 q); returns k', which indexes the UseHint columns.
    h = StackBuf(3)
    hint_witness(h, "fin")
    assert log(h[0]) < NKP
    assert log(h[1]) < GAMMA2
    assert log(h[2]) < 1024
    kp = h[0]
    tt = h[2]
    assert ov * zv * GEN ** (64 * Q + GAMMA2 - 1) == kp[GEN ** (TB + OFF_UH)] * h[1] * tt[GEN ** (TB + OFF_QU)]
    return kp


@inline
def w1_lane(us, ln: Const):
    # Lane ln of a chunk: coefficient c's W1_BITS bits at bit W1_BITS c of the chunk, a
    # lane starting inside a coefficient taking its high bits first.
    if const(64 * ln % W1_BITS != 0):
        cs = us[64 * ln // W1_BITS]
        if const(W1_BITS * (64 * ln // W1_BITS) % 64 == 60):
            acc = cs[GEN ** (TB + OFF_UH + 4 * NKP)]
        else:
            acc = cs[GEN ** (TB + OFF_UH + 6 * NKP)]
    for c in unroll(0, CHW):
        if const(W1_BITS * c // 64 == ln):
            uc = us[c]
            if const((W1_BITS * c % 64 + W1_BITS - 1) // 64 == 0):
                part = uc[GEN ** (TB + OFF_UH + 2 * NKP)] * const(2 ** (W1_BITS * c % 64))
            elif const(W1_BITS * c % 64 == 60):
                part = uc[GEN ** (TB + OFF_UH + 3 * NKP)]
            else:
                part = uc[GEN ** (TB + OFF_UH + 5 * NKP)]
            if const(W1_BITS * c == 64 * ln):
                acc = part
            else:
                acc = acc + part
    return acc
