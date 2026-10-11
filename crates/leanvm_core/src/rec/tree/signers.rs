//! The union of signer sets in rows: a node reads its children's sets, declares a set of their claims, and proves
//! every declared claim is one of theirs.
//!
//! Each side is a pool of items, each item one compression of a set's written form ([`crate::signers`]):
//!
//! - The children's pool holds one run per child, in order, each starting at a chunk's first item; a run is its
//!   child's items, then padding to its last chunk's end. The declared pool holds one run, the node's set.
//! - Each item's kind (header, keys, end, padding) and whether its second key is one are hinted bits, which give
//!   its counter word. A set's counters say what each item is, so the chain of a run equals its set's digest only
//!   if its bits are those of the set's own written form, and the run is read as that set.
//! - Every run's end item holds the digest of its run, and the run's place says whose: a one-hot over the children,
//!   moved on at each chunk that begins a run. So a pool's contents are fixed by the digests before any challenge.
//! - Each child claim has a selection bit. A challenge point `(X, A)` is drawn from a transcript of the children's
//!   digests, the node's and the selection words, and the rows check
//!
//!   ```text
//!   prod over child slots (1 + s · valid · (X + 1 + fp(c)))  ==  prod over declared slots (1 + valid · (X + 1 + fp(d)))
//!   fp(t) = sum over k < 16 of eq(A, k) · t[k],   t = (1, scheme, leaf_index, message[0..4], key[0..4], 0, ...)
//!   ```
//!
//!   which holds at a random point only if the selected child claims and the declared claims are one multiset.
//!   A claim's tuple carries its scheme, leaf index and message, so a key can only back a declared claim of its
//!   own group.
//!
//! A run's group fingerprint is reset at its start, so a set read at any place in a pool is read the same way.

use crate::rec::circuit::{Builder, Dw, Ew, Kw, PARAM_IV};
use crate::rec::transcript::{ProofSource, Transcript};
use crate::rv::Hash;
use crate::signers::{Capacity, Claim, Item, Scheme, SignerSet, code};
use fiat_shamir::SessionId;
use primitives::field::F192;
use std::collections::HashMap;

/// Items in a chunk: a run starts only at a chunk's first item.
pub(crate) const CHUNK: usize = 32;

/// The tag of the union's transcript's session, beside the tree's.
const SESSION_TAG: &[u8] = b"leanvm-signers-1";

/// A pool's size, in chunks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PoolShape {
    /// Its chunks.
    pub(crate) chunks: usize,
}

/// What a node's union reads and declares: its children's pool, shared by its `arity` runs, and its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct UnionShape {
    /// The children.
    pub(crate) arity: usize,
    /// The children's pool.
    pub(crate) children: PoolShape,
    /// The declared pool.
    pub(crate) declared: PoolShape,
}

/// What an item is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ItemKind {
    /// A group's header.
    Header,
    /// A block of keys, the second one a key if `pair`.
    Keys {
        /// Whether the second key is one.
        pair: bool,
    },
    /// A set's end.
    End,
    /// Padding after a run's end.
    Pad,
}

/// One item as a prover fills it.
#[derive(Clone, Copy, Debug)]
struct FillItem {
    block: [u64; 8],
    kind: ItemKind,
    /// Whether each key slot is selected.
    select: [bool; 2],
}

/// A pool's values, as its prover fills it.
#[derive(Clone, Debug)]
pub(crate) struct PoolFill {
    items: Vec<FillItem>,
    /// Whether each chunk begins a run, the first chunk's unread.
    begins: Vec<bool>,
}

/// A union's values, as its prover fills it.
#[derive(Clone, Debug)]
pub(crate) struct UnionFill {
    children: PoolFill,
    declared: PoolFill,
    /// The declared set's digest.
    digest: [u64; 4],
}

/// Why a union cannot be filled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FillError {
    /// The children's sets do not fit the children's pool.
    Children,
    /// The declared set does not fit the declared pool.
    Declared,
    /// A declared claim no child holds, past those already taken.
    NotCovered(Claim),
}

/// The wires of one item the products read.
struct ItemWires {
    /// The block's words.
    m: [Kw; 8],
    /// One for a block of keys.
    is_keys: Ew,
    /// One for a block of two keys.
    is_pair: Ew,
    /// Zero for a header.
    not_header: Ew,
    /// Whether the item starts a run: a constant at the pool's first item, a begin bit at a chunk's first.
    start: Start,
    /// The key slots' selection bits, on the children's side.
    select: Option<[Kw; 2]>,
}

/// Whether an item starts a run.
#[derive(Clone, Copy)]
enum Start {
    /// It never does.
    No,
    /// It always does: the pool's first item.
    Yes,
    /// If this bit is set: a chunk's first item.
    If(Kw),
}

/// The challenge point.
struct Point {
    /// `X + 1`.
    x1: Ew,
    /// `eq(A, k)` for each tuple slot `k`.
    weights: [Ew; 16],
}

impl ItemKind {
    /// The kind of an item of a set's written form.
    const fn of(item: &Item) -> Self {
        if item.code & code::END != 0 {
            Self::End
        } else if item.code & code::KEY != 0 {
            Self::Keys {
                pair: item.code & code::PAIR != 0,
            }
        } else {
            Self::Header
        }
    }

    /// Its hinted bits: `b0`, `b1` (header 00, keys 10, end 01, padding 11), then whether its second key is one.
    const fn bits(self) -> [bool; 3] {
        match self {
            Self::Header => [false, false, false],
            Self::Keys { pair } => [true, false, pair],
            Self::End => [false, true, false],
            Self::Pad => [true, true, false],
        }
    }
}

impl PoolShape {
    /// A pool of runs together of at most `items` items: each run's last chunk wastes less than a chunk.
    pub(crate) const fn new(items: usize, runs: usize) -> Self {
        Self {
            chunks: items.div_ceil(CHUNK) + runs,
        }
    }

    /// Its items.
    pub(crate) const fn items(self) -> usize {
        self.chunks * CHUNK
    }
}

impl UnionShape {
    /// The union of `arity` children whose sets together are within `capacity`, declaring a set within it.
    pub(crate) const fn new(capacity: Capacity, arity: usize) -> Self {
        Self {
            arity,
            // Each child's set has its own end item; the capacity's count has one.
            children: PoolShape::new(capacity.items() + arity - 1, arity),
            declared: PoolShape::new(capacity.items(), 1),
        }
    }
}

impl PoolFill {
    /// A pool holding these sets, one run each, in order.
    fn new(shape: PoolShape, sets: &[&SignerSet]) -> Option<Self> {
        let mut items = Vec::with_capacity(shape.items());
        let mut begins = vec![false; shape.chunks];
        let pad = FillItem {
            block: [0; 8],
            kind: ItemKind::Pad,
            select: [false; 2],
        };
        for (r, set) in sets.iter().enumerate() {
            if r > 0 {
                items.resize(items.len().next_multiple_of(CHUNK), pad);
                *begins.get_mut(items.len() / CHUNK)? = true;
            }
            items.extend(set.items().iter().map(|item| FillItem {
                block: item.block,
                kind: ItemKind::of(item),
                select: [false; 2],
            }));
        }
        if items.len() > shape.items() {
            return None;
        }
        items.resize(shape.items(), pad);
        Some(Self { items, begins })
    }

    /// Every key slot's claim, by item and slot, as the rows read them.
    fn slots(&self) -> Vec<(usize, usize, Claim)> {
        let mut slots = Vec::new();
        let mut group: Option<(Scheme, u32, [u64; 4])> = None;
        for (i, item) in self.items.iter().enumerate() {
            if i % CHUNK == 0 && (i == 0 || self.begins[i / CHUNK]) {
                group = None;
            }
            let m = item.block;
            match item.kind {
                ItemKind::Header => {
                    let scheme = match m[0] {
                        code::XMSS => Some(Scheme::Xmss),
                        code::SPHINCS => Some(Scheme::Sphincs),
                        _ => None,
                    };
                    group = scheme
                        .zip(u32::try_from(m[1]).ok())
                        .map(|(s, l)| (s, l, [m[2], m[3], m[4], m[5]]));
                }
                ItemKind::Keys { pair } => {
                    if let Some((scheme, leaf_index, message)) = group {
                        for slot in 0..1 + usize::from(pair) {
                            let key = std::array::from_fn(|j| m[4 * slot + j]);
                            slots.push((
                                i,
                                slot,
                                Claim {
                                    scheme,
                                    leaf_index,
                                    message,
                                    key,
                                },
                            ));
                        }
                    }
                }
                ItemKind::End | ItemKind::Pad => {}
            }
        }
        slots
    }
}

impl UnionFill {
    /// The union's values: the children's sets, and the declared set, each of whose claims some child slot backs.
    pub(crate) fn new(shape: &UnionShape, children: &[&SignerSet], declared: &SignerSet) -> Result<Self, FillError> {
        Self::fill(shape, children, declared, true)
    }

    /// The union's values with each declared claim some child slot backs selected, the others left unbacked: what
    /// a prover forging coverage would hand the rows.
    #[cfg(test)]
    pub(crate) fn unbacked(shape: &UnionShape, children: &[&SignerSet], declared: &SignerSet) -> Self {
        Self::fill(shape, children, declared, false).expect("the sets fit")
    }

    /// The union's values, refusing a claim no child slot backs if `strict`, else leaving it unbacked.
    fn fill(
        shape: &UnionShape,
        children: &[&SignerSet],
        declared: &SignerSet,
        strict: bool,
    ) -> Result<Self, FillError> {
        assert_eq!(children.len(), shape.arity, "one set a child");
        let mut child = PoolFill::new(shape.children, children).ok_or(FillError::Children)?;
        let declared_pool = PoolFill::new(shape.declared, &[declared]).ok_or(FillError::Declared)?;
        let mut free: HashMap<Claim, Vec<(usize, usize)>> = HashMap::new();
        for (i, slot, claim) in child.slots().into_iter().rev() {
            free.entry(claim).or_default().push((i, slot));
        }
        for claim in declared.claims() {
            match free.get_mut(&claim).and_then(Vec::pop) {
                Some((i, slot)) => child.items[i].select[slot] = true,
                None if strict => return Err(FillError::NotCovered(claim)),
                None => {}
            }
        }
        Ok(Self {
            children: child,
            declared: declared_pool,
            digest: declared.digest(),
        })
    }
}

/// The session of a union's transcript, under the tree's.
pub(crate) fn session(tree: &SessionId) -> SessionId {
    SessionId::new(&[SESSION_TAG, &tree.0].concat())
}

/// A pool's rows before any challenge: each item's compression, its kind and the run it belongs to.
///
/// Returns the items' wires, and the selection bits packed in words when `selecting`.
fn pool_rows(
    b: &mut Builder,
    shape: PoolShape,
    digests: &[Dw],
    fill: Option<&PoolFill>,
    selecting: bool,
) -> (Vec<ItemWires>, Vec<Kw>) {
    let runs = digests.len();
    assert!(runs >= 1 && runs <= shape.chunks, "a run a chunk at most");
    let (zero, one) = (b.zero(), b.one());
    let k_zero = b.k_const(0);
    let [iv_lo, iv_hi] = [
        F192::new(PARAM_IV[0], PARAM_IV[1], 0),
        F192::new(PARAM_IV[2], PARAM_IV[3], 0),
    ]
    .map(|v| b.e_const(v));
    let [c_key, c_end, c_pair] = [code::KEY, code::END, code::PAIR].map(|c| b.e_const(F192::new(c, 0, 0)));
    let c_final = b.e_const(F192::new(0, Hash::FINAL, 0));
    let halves: Vec<[Ew; 2]> = digests.iter().map(|&d| b.d_to_halves(d)).collect();

    // The run the current chunk belongs to, one-hot over the runs.
    let mut current: Vec<Ew> = (0..runs).map(|r| if r == 0 { one } else { zero }).collect();
    let mut bits: Vec<Kw> = Vec::new();
    let mut selections: Vec<Kw> = Vec::new();
    let mut items = Vec::with_capacity(shape.items());
    let mut previous: Option<(Ew, [Ew; 2], Dw)> = None;
    for j in 0..shape.chunks {
        let begin = (j > 0 && runs > 1).then(|| {
            let bit = b.free_k(u64::from(fill.is_some_and(|f| f.begins[j])));
            bits.push(bit);
            bit
        });
        if let Some(bit) = begin {
            current = (0..runs)
                .map(|r| {
                    let moved = if r == 0 { zero } else { current[r - 1] };
                    let diff = b.add(moved, current[r]);
                    b.mul_k_add(diff, bit, current[r])
                })
                .collect();
        }
        // The digest the run's end item must have.
        let expected: [Ew; 2] = if runs == 1 {
            halves[0]
        } else {
            std::array::from_fn(|h| (0..runs).fold(zero, |acc, r| b.mul_add(current[r], halves[r][h], acc)))
        };
        for k in 0..CHUNK {
            let i = j * CHUNK + k;
            let item = fill.map(|f| f.items[i]);
            let [b0, b1, pair] = item
                .map_or([false; 3], |it| it.kind.bits())
                .map(|x| b.free_k(u64::from(x)));
            bits.extend([b0, b1, pair]);
            let e0 = b.mul_k_add(one, b0, zero);
            let e1 = b.mul_k_add(one, b1, zero);
            let is_pad = b.mul_k_add(e0, b1, zero);
            let is_keys = b.add(e0, is_pad);
            let is_end = b.add(e1, is_pad);
            let either = b.add(e0, e1);
            let not_header = b.add(either, is_pad);
            // The second key only in a block of keys.
            let e_pair = b.mul_k_add(one, pair, zero);
            let is_pair = b.mul_k_add(is_keys, pair, zero);
            b.eq_e(e_pair, is_pair);

            let start = match (i, k, begin) {
                (0, ..) => Start::Yes,
                (_, 0, Some(bit)) => Start::If(bit),
                _ => Start::No,
            };
            // Padding follows a run's end or padding, and only within the run; a run starts after its last.
            let start_e = match (start, previous) {
                (Start::Yes, _) => {
                    b.eq_e(is_pad, zero);
                    one
                }
                (Start::If(bit), Some((ended, ..))) => {
                    let e_bit = b.mul_k_add(one, bit, zero);
                    let after_end = b.mul(ended, e_bit);
                    b.eq_e(after_end, e_bit);
                    let pad = b.add(ended, e_bit);
                    b.eq_e(is_pad, pad);
                    e_bit
                }
                (_, Some((ended, ..))) => {
                    b.eq_e(is_pad, ended);
                    zero
                }
                (_, None) => unreachable!("only the first item has none before it"),
            };

            // The counter word: its kind's bits, and the finalization word of an end.
            let t = b.mul_k_add(c_key, b0, start_e);
            let t = b.mul_k_add(c_end, b1, t);
            let t = b.mul_k_add(c_pair, pair, t);
            let t = b.mul_add(c_final, is_end, t);
            let [t, f, _] = b.e_to_k(t);
            let tf = b.k_to_d([t, f, k_zero, k_zero]);

            // The chaining value: the parameter IV at a run's start, the previous output within it.
            let h = match (start, previous) {
                (Start::Yes, _) => b.d_const(PARAM_IV),
                (Start::If(bit), Some((_, [lo, hi], _))) => {
                    let d_lo = b.add(lo, iv_lo);
                    let d_hi = b.add(hi, iv_hi);
                    let lo = b.mul_k_add(d_lo, bit, lo);
                    let hi = b.mul_k_add(d_hi, bit, hi);
                    b.halves_to_d(lo, hi)
                }
                (_, Some((.., out))) => out,
                (_, None) => unreachable!("only the first item has none before it"),
            };
            let m: [Kw; 8] = std::array::from_fn(|w| b.free_k(item.map_or(0, |it| it.block[w])));
            let out = b.block(h, m, tf);
            let out_halves = b.d_to_halves(out);

            // A run's end holds its run's digest.
            for (&o, &e) in out_halves.iter().zip(&expected) {
                let diff = b.add(o, e);
                let held = b.mul(is_end, diff);
                b.eq_e(held, zero);
            }

            let select = selecting.then(|| {
                let s = item.map_or([false; 2], |it| it.select).map(|x| b.free_k(u64::from(x)));
                selections.extend(s);
                s
            });
            items.push(ItemWires {
                m,
                is_keys,
                is_pair,
                not_header,
                start,
                select,
            });
            previous = Some((e1, out_halves, out));
        }
    }
    // The pool ends after an end or padding, in its last run.
    let (ended, ..) = previous.expect("a pool has items");
    b.eq_e(ended, one);
    for (r, &c) in current.iter().enumerate() {
        b.eq_e_const(c, F192::new(u64::from(r + 1 == runs), 0, 0));
    }
    // The hinted bits are bits.
    for chunk in bits.chunks(64) {
        b.pack(chunk);
    }
    let words = selections.chunks(64).map(|chunk| b.pack(chunk)).collect();
    (items, words)
}

/// The product over a pool's claims of `1 + s · valid · (X + 1 + fp)`, `s` a slot's selection bit or one.
fn product(b: &mut Builder, items: &[ItemWires], point: &Point) -> Ew {
    let (zero, one) = (b.zero(), b.one());
    let w = &point.weights;
    let mut group = zero;
    let mut product = one;
    for item in items {
        group = match item.start {
            Start::Yes => zero,
            Start::If(bit) => b.mul_k_add(group, bit, group),
            Start::No => group,
        };
        // The fingerprint's group part, were the item a header: tag, scheme, leaf index, message.
        let header = (0..6).fold(w[0], |acc, j| b.mul_k_add(w[1 + j], item.m[j], acc));
        let diff = b.add(header, group);
        group = b.mul_add(item.not_header, diff, header);
        for (slot, valid) in [item.is_keys, item.is_pair].into_iter().enumerate() {
            let fp = (0..4).fold(group, |acc, j| b.mul_k_add(w[7 + j], item.m[4 * slot + j], acc));
            let term = b.add(point.x1, fp);
            let factor = match item.select {
                Some(select) => {
                    let held = b.mul(valid, term);
                    b.mul_k_add(held, select[slot], one)
                }
                None => b.mul_add(valid, term, one),
            };
            product = b.mul(product, factor);
        }
    }
    product
}

/// `eq(A, k)` for each `k < 16`, bit `j` of `k` choosing `A_j` over `1 + A_j`.
fn eq_weights(b: &mut Builder, a: [Ew; 4]) -> [Ew; 16] {
    let one = b.one();
    let mut table = vec![one];
    for &aj in &a {
        let not = b.add(aj, one);
        let low: Vec<Ew> = table.iter().map(|&x| b.mul(x, not)).collect();
        let high: Vec<Ew> = table.iter().map(|&x| b.mul(x, aj)).collect();
        table = [low, high].concat();
    }
    table.try_into().expect("sixteen weights")
}

/// The union's rows: the children's sets read from their digests, the declared set's digest, and the product check
/// that every declared claim is a selected child claim.
///
/// Returns the declared set's digest.
pub(crate) fn union_rows(
    b: &mut Builder,
    shape: &UnionShape,
    session: &SessionId,
    children: &[Dw],
    fill: Option<&UnionFill>,
) -> Dw {
    assert_eq!(children.len(), shape.arity, "one digest a child");
    let digest = b.free_d(fill.map_or([0; 4], |f| f.digest));
    let (child_items, selections) = b.scope("children's pool", |b| {
        pool_rows(b, shape.children, children, fill.map(|f| &f.children), true)
    });
    let (declared_items, _) = b.scope("declared pool", |b| {
        pool_rows(b, shape.declared, &[digest], fill.map(|f| &f.declared), false)
    });

    let mut instance = Vec::new();
    for &d in children.iter().chain([&digest]) {
        instance.extend(b.d_to_k(d));
    }
    instance.extend(selections);
    let mut t = Transcript::new(b, &self::session(session), &instance, ProofSource::Shape);
    let x = t.verifier_message(b);
    let a = std::array::from_fn(|_| t.verifier_message(b));
    let one = b.one();
    let point = Point {
        x1: b.add(x, one),
        weights: eq_weights(b, a),
    };
    b.scope("coverage", |b| {
        let selected = product(b, &child_items, &point);
        let declared = product(b, &declared_items, &point);
        b.eq_e(selected, declared);
    });
    digest
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rec::circuit::Unsatisfied;
    use crate::signers::{SphincsClaim, XmssGroup};

    fn key(i: u64) -> [u64; 4] {
        [i, 3 * i + 1, i << 7, 0xabcd ^ i]
    }

    fn group(leaf_index: u32, message: u64, keys: &[u64]) -> XmssGroup {
        XmssGroup {
            leaf_index,
            message: [message, 1, 2, 3],
            keys: keys.iter().map(|&i| key(i)).collect(),
        }
    }

    /// Two overlapping children, one of them with SPHINCS claims.
    fn children() -> [SignerSet; 2] {
        [
            SignerSet {
                xmss: vec![group(5, 1, &[1, 2, 3]), group(5, 2, &[1])],
                sphincs: vec![],
            },
            SignerSet {
                xmss: vec![group(5, 1, &[3, 4]), group(7, 1, &[2])],
                sphincs: vec![SphincsClaim {
                    key: key(9),
                    message: [4, 4, 4, 4],
                }],
            },
        ]
    }

    const CAPACITY: Capacity = Capacity { claims: 24, groups: 6 };

    fn union_of(sets: &[SignerSet]) -> SignerSet {
        SignerSet::from_claims(sets.iter().flat_map(SignerSet::claims))
    }

    /// The union's rows over these children and fill, and the checks that failed; the declared digest must be
    /// that of `expected`.
    fn run(sets: &[SignerSet], fill: &UnionFill, expected: Option<&SignerSet>) -> Vec<Unsatisfied> {
        let shape = UnionShape::new(CAPACITY, sets.len());
        let mut b = Builder::new();
        let digests: Vec<Dw> = sets.iter().map(|s| b.free_d(s.digest())).collect();
        let d = union_rows(&mut b, &shape, &SessionId([7; 32]), &digests, Some(fill));
        if let Some(e) = expected {
            assert_eq!(b.d(d), e.digest());
        }
        b.finish().failures
    }

    fn fill(sets: &[SignerSet], declared: &SignerSet) -> UnionFill {
        let refs: Vec<&SignerSet> = sets.iter().collect();
        UnionFill::new(&UnionShape::new(CAPACITY, sets.len()), &refs, declared).expect("covered")
    }

    #[test]
    fn the_union_of_overlapping_children_holds() {
        let sets = children();
        let union = union_of(&sets);
        assert_eq!(union.n_claims(), 7, "the shared key is one claim");
        assert_eq!(run(&sets, &fill(&sets, &union), Some(&union)), vec![]);
    }

    #[test]
    fn a_node_may_declare_less_or_nothing() {
        let sets = children();
        let one_group = SignerSet {
            xmss: vec![group(5, 1, &[1, 4])],
            sphincs: vec![],
        };
        for declared in [one_group, SignerSet::new()] {
            assert_eq!(run(&sets, &fill(&sets, &declared), Some(&declared)), vec![]);
        }
    }

    #[test]
    fn repeated_and_empty_children_hold() {
        let [a, _] = children();
        let sets = [a.clone(), SignerSet::new(), a.clone()];
        assert_eq!(run(&sets, &fill(&sets, &a), Some(&a)), vec![]);
    }

    #[test]
    fn a_shape_is_the_same_circuit() {
        let sets = children();
        let shape = UnionShape::new(CAPACITY, 2);
        let build = |fill: Option<&UnionFill>| {
            let mut b = Builder::new();
            let digests: Vec<Dw> = sets.iter().map(|s| b.free_d(s.digest())).collect();
            union_rows(&mut b, &shape, &SessionId([7; 32]), &digests, fill);
            b.finish().circuit
        };
        assert_eq!(build(None), build(Some(&fill(&sets, &union_of(&sets)))));
    }

    #[test]
    fn an_uncovered_claim_is_refused_by_the_prover() {
        let sets = children();
        let mut declared = union_of(&sets);
        declared.xmss[0].keys.push(key(99));
        let refs: Vec<&SignerSet> = sets.iter().collect();
        let shape = UnionShape::new(CAPACITY, 2);
        assert!(matches!(
            UnionFill::new(&shape, &refs, &declared),
            Err(FillError::NotCovered(c)) if c.key == key(99)
        ));
        // A key at another group of its own leaf index is another claim.
        let moved = SignerSet {
            xmss: vec![group(5, 2, &[2])],
            sphincs: vec![],
        };
        assert!(matches!(
            UnionFill::new(&shape, &refs, &moved),
            Err(FillError::NotCovered(_))
        ));
        // Children past the pool.
        let big = SignerSet {
            xmss: vec![group(1, 1, &(0..100).collect::<Vec<_>>())],
            sphincs: vec![],
        };
        assert_eq!(
            UnionFill::new(&shape, &[&big, &big], &SignerSet::new()).err(),
            Some(FillError::Children)
        );
    }

    /// The honest fill of the union, then forged.
    fn forged(forge: impl FnOnce(&mut UnionFill)) -> Vec<Unsatisfied> {
        let sets = children();
        let mut f = fill(&sets, &union_of(&sets));
        forge(&mut f);
        run(&sets, &f, None)
    }

    #[test]
    fn forged_coverage_is_refused() {
        let declared_key = |f: &mut UnionFill| {
            let i = (f.declared.items.iter()).position(|it| matches!(it.kind, ItemKind::Keys { .. }));
            i.expect("a block of keys")
        };
        let cases: Vec<(&str, Box<dyn FnOnce(&mut UnionFill)>)> = vec![
            (
                "a declared key changed",
                Box::new(move |f| {
                    let i = declared_key(f);
                    f.declared.items[i].block[0] ^= 1;
                }),
            ),
            (
                "a declared key changed, the digest with it",
                Box::new(|f| {
                    let mut set = union_of(&children());
                    set.xmss[0].keys[0][0] ^= 1;
                    let shape = UnionShape::new(CAPACITY, 2);
                    f.declared = PoolFill::new(shape.declared, &[&set]).expect("fits");
                    f.digest = set.digest();
                }),
            ),
            (
                "a declared claim at another group",
                Box::new(|f| {
                    let mut set = union_of(&children());
                    let k = set.xmss[0].keys.pop().expect("a key");
                    set.xmss[1].keys.push(k);
                    set.xmss[1].keys.sort_unstable();
                    let shape = UnionShape::new(CAPACITY, 2);
                    f.declared = PoolFill::new(shape.declared, &[&set]).expect("fits");
                    f.digest = set.digest();
                }),
            ),
            (
                "a claim declared twice, selected once",
                Box::new(|f| {
                    let mut set = union_of(&children());
                    let k = set.xmss[0].keys[0];
                    set.xmss[0].keys.push(k);
                    let shape = UnionShape::new(CAPACITY, 2);
                    f.declared = PoolFill::new(shape.declared, &[&set]).expect("fits");
                    f.digest = set.digest();
                }),
            ),
            (
                "a selected slot unselected",
                Box::new(|f| {
                    let it = (f.children.items.iter_mut())
                        .find(|it| it.select[0])
                        .expect("a selection");
                    it.select[0] = false;
                }),
            ),
            (
                "a padding slot backing a declared claim",
                Box::new(|f| {
                    // The half block of keys 3 at (5, 1) pads with a zero key: declare it, select the padding.
                    let mut set = union_of(&children());
                    set.xmss[0].keys.insert(0, [0; 4]);
                    let shape = UnionShape::new(CAPACITY, 2);
                    f.declared = PoolFill::new(shape.declared, &[&set]).expect("fits");
                    f.digest = set.digest();
                    let it = (f.children.items.iter_mut())
                        .find(|it| it.kind == ItemKind::Keys { pair: false })
                        .expect("a half block");
                    it.select[1] = true;
                }),
            ),
            (
                "a child's pair bit dropped",
                Box::new(|f| {
                    let it = (f.children.items.iter_mut())
                        .find(|it| it.kind == ItemKind::Keys { pair: true })
                        .expect("a full block");
                    it.kind = ItemKind::Keys { pair: false };
                    it.select[1] = false;
                }),
            ),
            (
                "a header read as keys",
                Box::new(|f| {
                    f.children.items[0].kind = ItemKind::Keys { pair: true };
                }),
            ),
            (
                "a run's end read as padding",
                Box::new(|f| {
                    let it = (f.children.items.iter_mut())
                        .find(|it| it.kind == ItemKind::End)
                        .expect("an end");
                    it.kind = ItemKind::Pad;
                }),
            ),
            (
                "a run begun mid-set",
                Box::new(|f| {
                    f.children.begins[1] = false;
                    f.children.begins[2] = true;
                }),
            ),
            (
                "a child's key changed",
                Box::new(|f| {
                    let it = (f.children.items.iter_mut())
                        .find(|it| matches!(it.kind, ItemKind::Keys { .. }))
                        .expect("keys");
                    it.block[1] ^= 4;
                }),
            ),
        ];
        for (name, forge) in cases {
            assert!(!forged(forge).is_empty(), "{name} holds");
        }
    }
}
