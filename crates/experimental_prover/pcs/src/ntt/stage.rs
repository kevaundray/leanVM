//! The lane-major message: its transpose, and the stage a gathered first pass fills from it.

use primitives::field::F64;
use primitives::stream::Stream;

use super::scratch::with_scratch;
use super::source::Lanes;
use super::window::STREAM_MIN_WORDS;

/// Transpose a lane-major message into the row-major order the encodes read.
///
/// # Layout
///
/// ```text
///     input, lane-major:   [ block 0 | block 1 | ... | block n-1 ]   each 2^log_rows words
///     output, row-major:   row x = [ 0, ..., 0, block n-1 word x, ..., block 0 word x ]
/// ```
///
/// - A row is `row_words >= n` words: the first `row_words - n` lanes are zero padding.
/// - Codeword lane `t` past the padding takes message block `row_words - 1 - t`.
/// - Any lane count works: a commitment encodes only the lanes that carry data, and a caller pads
///   the row to a multiple of [`ROW_LANES`](super::ROW_LANES).
///
/// # Why descending
///
/// - The absent all-zero lanes lead every Merkle leaf image, so the proof can leave them out.
/// - `whir::commit` has the full reason.
///
/// # Performance
///
/// - Rows are handled one tile at a time.
/// - Each lane adds a contiguous burst of words to an L1-resident tile.
/// - The finished tile goes out as one contiguous run.
/// - That keeps an n-way gather at a `2^log_rows` stride near memory bandwidth.
pub(super) fn transpose_lane_major(out: &mut [F64], msg: &[F64], n_lanes: usize, row_words: usize, log_rows: usize) {
    let rows = 1usize << log_rows;
    assert!(n_lanes > 0, "a commitment needs at least one lane");
    assert!(n_lanes <= row_words, "a row holds its lanes");
    assert_eq!(msg.len(), n_lanes * rows, "message is n_lanes contiguous lane blocks");
    assert_eq!(out.len(), row_words * rows, "the output is whole padded rows");

    /// Words per cache-resident row tile.
    const TILE_WORDS: usize = 4096;
    assert!(row_words <= TILE_WORDS, "a codeword row must fit the transpose tile");
    // Largest power-of-two row count whose tile fits: both it and `rows` are then
    // powers of two, so the tiles cover every row. They have to: this is the sole
    // initializer of an uninitialized codeword's message region, and a truncating
    // tile count would leave the tail reading the previous phase's plausible bytes,
    // whose symptom is a proof that stops verifying rather than a crash.
    let tile_rows = (1usize << (TILE_WORDS / row_words).ilog2()).min(rows);
    assert_eq!(rows % tile_rows, 0, "row tiles must cover every row");

    // Nothing reads the output back before a buffer this large is evicted.
    let stream = out.len() >= STREAM_MIN_WORDS;
    let pad = row_words - n_lanes;
    parallel::chunks_mut(out, tile_rows * row_words, |t, out_tile| {
        with_scratch(out_tile.len(), |tile| {
            // First message row this tile covers.
            let r0 = t * tile_rows;
            // Fill the tile column by column: lane `lane` takes every `row_words`-th word.
            for lane in 0..row_words {
                let slots = tile[lane..].iter_mut().step_by(row_words);
                if lane < pad {
                    slots.for_each(|slot| *slot = F64::ZERO);
                } else {
                    let src = &msg[(row_words - 1 - lane) * rows + r0..][..tile_rows];
                    for (slot, &word) in slots.zip(src) {
                        *slot = word;
                    }
                }
            }
            // Write the finished tile out as one contiguous run.
            if stream {
                Stream::new().copy(out_tile, tile);
            } else {
                out_tile.copy_from_slice(tile);
            }
        });
    });
}

/// Residues a lane-major first pass takes at once, as a log: one cache line of a lane block.
pub(super) const LOG_BATCH: usize = 3;
pub(super) const BATCH: usize = 1 << LOG_BATCH;

/// The lane groups a stage moves across a row of `row_words` lanes, as `(first, lanes)`: whole octets, then a quad
/// where the row ends four lanes past one.
///
/// A group is line-aligned in the batch's rows rather than in each row. Row `s` starts `s * row_words` words into
/// the batch, half a line off when `s` is odd and the row ends in a quad, so there an odd residue takes its lanes
/// from `first + 4` on, and from lane 0 in the last group. Every group then writes whole cache lines of the batch
/// (see [`line_steps`]), which a streaming store needs.
///
/// ```text
///     36 lanes, rows 0 and 1 of a batch (288 words, 36 lines), lanes by group:
///
///     row 0:  [ 0..8 ][ 8..16 ][ 16..24 ][ 24..32 ][ 32..36 |
///     row 1:                                       | 0..4 ][ 4..12 ][ 12..20 ][ 20..28 ][ 28..36 ]
///               g 0     g 1       g 2       g 3      g 4  g 4  g 0     g 1       g 2       g 3
/// ```
pub(super) fn lane_groups(row_words: usize) -> impl Iterator<Item = (usize, usize)> {
    assert!(row_words.is_multiple_of(4), "a staged row is whole quads of lanes");
    (0..row_words)
        .step_by(8)
        .map(move |lane| (lane, (row_words - lane).min(8)))
}

/// Where the lines of a stage row of a lane group `(first, lanes)` land in the batch's `BATCH * row_words` words:
/// line `k` at word `first + k * stride + (k & 1) * odd`, as `(stride, odd)`.
///
/// A line of an octet group is residue `k`'s lanes; a line of the quad group is residue `2k`'s last quad, then
/// residue `2k + 1`'s first.
pub(super) fn line_steps(row_words: usize, lanes: usize) -> (usize, usize) {
    if lanes == 8 {
        (row_words, row_words % 8)
    } else {
        (2 * row_words, 0)
    }
}

/// The transpose of a lane-major message through a stage, for one gathered pass.
///
/// - It owns the message and the geometry of the fill: the step, the message rows and the row width.
/// - [`Stage::fill`] moves one group of lanes of a batch of residues into a stage buffer.
/// - A task fills the stage, then each block of the pass transforms a copy of it.
pub(super) struct Stage<'a> {
    lanes: Lanes<'a>,
    log_step: usize,
    msg_rows: usize,
    row_words: usize,
}

impl<'a> Stage<'a> {
    /// The stage of a pass whose groups are `2^log_step` rows apart, over `lanes` of `msg_rows` rows each.
    pub(super) fn new(lanes: Lanes<'a>, log_step: usize, msg_rows: usize, row_words: usize) -> Self {
        Self {
            lanes,
            log_step,
            msg_rows,
            row_words,
        }
    }

    /// Transpose the lane group `(first, lanes)` of [`lane_groups`] of a batch of [`BATCH`] consecutive residues
    /// from `t0` into `stage`.
    ///
    /// - Message row `j` is `msg_rows` words apart per lane block, and word `w` of a row of `row_words` words
    ///   is lane block `row_words - 1 - w` of the message, or zero while `w` is below the padding.
    /// - Residue `t0 + s` takes rows `t0 + s + i * step` for `i < rows`, `step = 2^log_step`.
    /// - Together with the residues, the group's lanes are `BATCH * lanes` lanes of one transform.
    /// - `stage` has `rows` rows of `BATCH * lanes` words. Lane `l + k` of row `t0 + s + i * step` is word
    ///   `(i * BATCH + s) * lanes + k`, `l` the lane residue `s` starts the group at (see [`lane_groups`]).
    /// - A tile is 8 words of each lane block the group reads, so each 64 byte line of a lane block is read once.
    ///
    /// In a row that ends in a quad, a group reads the quad the next group starts its even residues with, and the
    /// first group the quad the last group ends its odd residues with. Those halves wait in `carry`
    /// ([`carry_len`] words), so the groups of one batch must be filled in order.
    #[inline]
    pub(super) fn fill(&self, stage: &mut [F64], carry: &mut [F64], t0: usize, first: usize, lanes: usize) {
        let quad_ended = !self.row_words.is_multiple_of(8);
        match (lanes, quad_ended) {
            (8, false) => self.fill_group::<8, PLAIN>(stage, carry, t0, first),
            (4, true) if self.row_words == 4 => self.fill_group::<4, PLAIN>(stage, carry, t0, first),
            (8, true) if first == 0 => self.fill_group::<8, OPEN>(stage, carry, t0, first),
            (8, true) => self.fill_group::<8, MID>(stage, carry, t0, first),
            (4, true) => self.fill_group::<4, CLOSE>(stage, carry, t0, first),
            _ => unreachable!("a stage moves an octet, or a quad where a row ends in one"),
        }
    }

    #[inline(always)]
    fn fill_group<const W: usize, const G: u8>(&self, stage: &mut [F64], carry: &mut [F64], t0: usize, first: usize) {
        let Self {
            lanes: Lanes { words: msg, n_lanes },
            log_step,
            msg_rows,
            row_words,
        } = *self;
        let geometry = (t0, log_step, msg_rows, n_lanes, row_words, first);
        // SAFETY: AVX-512F is enabled at compile time.
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
        unsafe {
            fill_stage_tiles::<W, G>(stage, carry, msg, geometry)
        }
        // SAFETY: AVX2 is enabled at compile time.
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
        unsafe {
            fill_stage_tiles::<W, G>(stage, carry, msg, geometry)
        }
        #[cfg(not(any(
            all(target_arch = "x86_64", target_feature = "avx512f"),
            all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f"))
        )))]
        fill_stage_tiles::<W, G>(stage, carry, msg, geometry);
    }
}

/// Words of carry a stage of `rows` rows needs for rows of `row_words` lanes: see [`Stage::fill`].
pub(super) fn carry_len(row_words: usize, rows: usize) -> usize {
    if row_words % 8 == 4 && row_words > 4 {
        CARRY_WORDS * rows
    } else {
        0
    }
}

/// Carry words a stage row keeps: four lanes of the four even residues for the next group, then four lanes of the
/// four odd residues for the last group.
const CARRY_WORDS: usize = 32;

/// How a group fills its tile, by where its row stands.
///
/// - `PLAIN`: every residue takes the group's quads, in a row of whole octets or a row of one quad.
/// - `OPEN`: the first group where a row ends in a quad. It reads quads 0, 1 and 2: even residues take 0 and 1 and
///   carry 2 to the next group; odd residues take 1 and 2 and carry 0 to the last group.
/// - `MID`: a later octet group, from quad `f = first / 4`. It reads quads `f + 1` and `f + 2`: even residues take
///   the carried quad `f` and `f + 1`, and carry `f + 2`; odd residues take `f + 1` and `f + 2`.
/// - `CLOSE`: the last group, a quad. It reads nothing: even residues take the carried last quad, odd ones quad 0.
const PLAIN: u8 = 0;
const OPEN: u8 = 1;
const MID: u8 = 2;
const CLOSE: u8 = 3;

/// Quads of lanes a tile reads at most: the `OPEN` group's three.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
const TILE_QUADS: usize = 3;

/// The quads of the message a tile of `W` lanes in a group `G` reads, from quad `first / 4 + (G == MID)` on.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
const fn tile_quads(w: usize, g: u8) -> usize {
    match g {
        PLAIN => w / 4,
        OPEN => 3,
        MID => 2,
        _ => 0,
    }
}

/// [`Stage::fill`] of `W` lanes of a group `G`, a target-feature function where AVX-512 or AVX2 is enabled, so its
/// tiles move through registers. `geometry` is `(t0, log_step, msg_rows, n_lanes, row_words, first)`.
#[cfg_attr(
    all(target_arch = "x86_64", target_feature = "avx512f"),
    target_feature(enable = "avx512f"),
    inline
)]
#[cfg_attr(
    all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")),
    target_feature(enable = "avx2"),
    inline
)]
fn fill_stage_tiles<const W: usize, const G: u8>(
    stage: &mut [F64],
    carry: &mut [F64],
    msg: &[F64],
    (t0, log_step, msg_rows, n_lanes, row_words, first): (usize, usize, usize, usize, usize, usize),
) {
    let rows = stage.len() / (BATCH * W);
    let pad = row_words - n_lanes;
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    {
        let q0 = first / 4 + usize::from(G == MID);
        // Lane `k` of quad `q` the tile reads, and the lines of each quad that are padding lanes.
        let lane = |q: usize, k: usize| 4 * (q0 + q) + k;
        let read = |q: usize| q < tile_quads(W, G);
        let zeros: [u8; TILE_QUADS] = std::array::from_fn(|q| {
            (0..4)
                .filter(|&k| read(q) && lane(q, k) < pad)
                .fold(0u8, |m, k| m | 1 << k)
        });
        // Line `k` of quad `q`: 8 residues of one lane block, or zeros for a padding lane.
        let block: [[usize; 4]; TILE_QUADS] = std::array::from_fn(|q| {
            std::array::from_fn(|k| {
                if read(q) {
                    (row_words - 1 - lane(q, k)) * msg_rows
                } else {
                    0
                }
            })
        });
        let carries = G != PLAIN;
        for i in 0..rows {
            let src = block.map(|quad| quad.map(|b| b + t0 + (i << log_step)));
            let carry = if carries {
                &mut carry[i * CARRY_WORDS..][..CARRY_WORDS]
            } else {
                &mut [][..]
            };
            fill_tile::<W, G>(stage, i * BATCH, msg, &src, zeros, carry);
        }
    }
    // Word by word: residue `s` takes the lanes from `first`, half a line on in an odd row that ends in a quad.
    #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
    {
        let _ = carry;
        for i in 0..rows {
            for s in 0..BATCH {
                let start = (first + row_words % 8 * (s & 1)) % row_words;
                for w in 0..W {
                    let lane = start + w;
                    stage[(i * BATCH + s) * W + w] = if lane < pad {
                        F64::ZERO
                    } else {
                        msg[(row_words - 1 - lane) * msg_rows + t0 + s + (i << log_step)]
                    };
                }
            }
        }
    }
}

/// One tile of [`fill_stage_tiles`]: the 8 residues' lanes of a group, from the `src[q]` lines of the quads it reads
/// (a line in `zeros[q]` being zeros) and from the stage row's `carry`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
#[inline]
#[target_feature(enable = "avx512f")]
fn fill_tile<const W: usize, const G: u8>(
    stage: &mut [F64],
    tile: usize,
    msg: &[F64],
    src: &[[usize; 4]; TILE_QUADS],
    zeros: [u8; TILE_QUADS],
    carry: &mut [F64],
) {
    use core::arch::x86_64::*;
    use primitives::simd::{load, store, transpose8};
    if W != 8 || G != PLAIN {
        return fill_tile_ymm::<W, G>(stage, tile, msg, src, zeros, carry);
    }
    let r: [__m512i; 8] = std::array::from_fn(|k| {
        let (q, k) = (k / 4, k % 4);
        if zeros[q] >> k & 1 == 1 {
            _mm512_setzero_si512()
        } else {
            load(&msg[src[q][k]..], 0)
        }
    });
    let cols = transpose8(r);
    for (s, col) in cols.into_iter().enumerate() {
        store(stage, tile + s, col);
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
use fill_tile_ymm as fill_tile;

/// [`fill_tile`] as one 4x4 transpose of YMM halves per half of each quad of lines.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[inline]
#[target_feature(enable = "avx2")]
fn fill_tile_ymm<const W: usize, const G: u8>(
    stage: &mut [F64],
    tile: usize,
    msg: &[F64],
    src: &[[usize; 4]; TILE_QUADS],
    zeros: [u8; TILE_QUADS],
    carry: &mut [F64],
) {
    use core::arch::x86_64::*;
    use primitives::{load_at, store_at};
    // Line `k` of quad `q`, half `h`: words `4h..4h + 4` of the line's 8 residues.
    let lines: [[[__m256i; 2]; 4]; TILE_QUADS] = std::array::from_fn(|q| {
        std::array::from_fn(|k| {
            if q >= tile_quads(W, G) || zeros[q] >> k & 1 == 1 {
                [_mm256_setzero_si256(); 2]
            } else {
                [load_at(msg, src[q][k]), load_at(msg, src[q][k] + 4)]
            }
        })
    });
    // Quad `q`, half `h`: residue `4h + i`'s four lanes, a 4x4 transpose of the half.
    let r: [[[__m256i; 4]; 2]; TILE_QUADS] = std::array::from_fn(|q| {
        std::array::from_fn(|h| {
            let t = |k: usize| lines[q][k][h];
            let (a0, a1) = (_mm256_unpacklo_epi64(t(0), t(1)), _mm256_unpackhi_epi64(t(0), t(1)));
            let (a2, a3) = (_mm256_unpacklo_epi64(t(2), t(3)), _mm256_unpackhi_epi64(t(2), t(3)));
            [
                _mm256_permute2x128_si256::<0x20>(a0, a2),
                _mm256_permute2x128_si256::<0x20>(a1, a3),
                _mm256_permute2x128_si256::<0x31>(a0, a2),
                _mm256_permute2x128_si256::<0x31>(a1, a3),
            ]
        })
    });
    if G == PLAIN {
        for h in 0..2 {
            for q in 0..W / 4 {
                for (i, &col) in r[q][h].iter().enumerate() {
                    store_at(stage, (tile + 4 * h + i) * W + 4 * q, col);
                }
            }
        }
        return;
    }
    for s in 0..BATCH {
        let v = |q: usize| r[q][s / 4][s % 4];
        let at = |c: usize| (tile + s) * W + 4 * c;
        // This residue's quads of carry: for the next group if even, for the last group if odd.
        let kept = 4 * (s / 2) + 16 * (s & 1);
        match (G, s & 1) {
            (OPEN, 0) => {
                store_at(stage, at(0), v(0));
                store_at(stage, at(1), v(1));
                store_at(carry, kept, v(2));
            }
            (OPEN, _) => {
                store_at(carry, kept, v(0));
                store_at(stage, at(0), v(1));
                store_at(stage, at(1), v(2));
            }
            (MID, 0) => {
                store_at(stage, at(0), load_at::<_, __m256i>(carry, kept));
                store_at(stage, at(1), v(0));
                store_at(carry, kept, v(1));
            }
            (MID, _) => {
                store_at(stage, at(0), v(0));
                store_at(stage, at(1), v(1));
            }
            _ => store_at(stage, at(0), load_at::<_, __m256i>(carry, kept)),
        }
    }
}
