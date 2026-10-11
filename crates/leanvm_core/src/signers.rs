//! Signer sets: the signature claims a signer-set tree's proofs publish, their digest, and their canonical form.
//!
//! A claim says that a key signed a message: an XMSS key at a leaf index, or a SPHINCS key. A set is XMSS groups,
//! each the keys that signed one message at one leaf index, then SPHINCS claims; it is written as groups of claims
//! sharing their scheme, leaf index and message (the SPHINCS claims grouped by runs of equal messages), and its
//! digest is the chain of BLAKE2s compressions `leanvm_guest::signers` defines, which a guest computes as it
//! verifies and a recursion circuit recomputes in rows:
//!
//! ```text
//! header   scheme, leaf_index, message[0..4], 0, 0     t = START? | 0
//! keys     key_a[0..4], key_b[0..4] (zeros if absent)  t = START? | KEY | PAIR if key_b is a key
//! end      TAG, 0, 0, 0, 0, 0, 0, 0                    t = START? | END, the last block
//! ```
//!
//! A set in any order has a digest; a root's verifier accepts only the canonical one ([`SignerSet::check`]):
//! XMSS groups strictly increasing on `(leaf_index, message)`, each non-empty with strictly increasing keys, then
//! SPHINCS claims strictly increasing on `(message, key)`, words compared as integers, first word first. So a
//! canonical set holds each claim once, and its size counts distinct claims.

use crate::rec::circuit::{Compression, Limbs, PARAM_IV};
use thiserror::Error;

/// A public key of either scheme as four words: its Merkle root's two, then its public parameter's two.
pub type Key = [u64; 4];

/// A signed message.
pub type Message = [u64; 4];

/// The counter bits of an item, and the words the format fixes (`leanvm_guest::signers`).
pub(crate) mod code {
    /// The XMSS scheme's word in a header.
    pub(crate) const XMSS: u64 = 1;
    /// The SPHINCS scheme's word in a header.
    pub(crate) const SPHINCS: u64 = 2;
    /// The first item.
    pub(crate) const START: u64 = 1;
    /// A block of keys.
    pub(crate) const KEY: u64 = 2;
    /// The end item.
    pub(crate) const END: u64 = 4;
    /// A block of keys whose second key is one.
    pub(crate) const PAIR: u64 = 8;
    /// The end item's first word.
    pub(crate) const TAG: u64 = u64::from_le_bytes(*b"signers1");
}

/// The signature scheme of a claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Scheme {
    /// leanXMSS: a key signs one message at each leaf index.
    Xmss,
    /// leanSPHINCS: stateless, no leaf index.
    Sphincs,
}

/// One signature claim: `key` signed `message` under `scheme`, at `leaf_index` for XMSS (zero for SPHINCS).
///
/// Claims order as the canonical set lists them: by scheme, leaf index, message, then key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Claim {
    /// The scheme.
    pub scheme: Scheme,
    /// The XMSS leaf index, zero for SPHINCS.
    pub leaf_index: u32,
    /// The message.
    pub message: Message,
    /// The key.
    pub key: Key,
}

/// The XMSS keys that signed one message at one leaf index.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct XmssGroup {
    /// The leaf index.
    pub leaf_index: u32,
    /// The message.
    pub message: Message,
    /// The keys.
    pub keys: Vec<Key>,
}

/// A SPHINCS key and the message it signed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SphincsClaim {
    /// The key.
    pub key: Key,
    /// The message.
    pub message: Message,
}

/// A set of signature claims, as an aggregate publishes it.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct SignerSet {
    /// The XMSS groups.
    pub xmss: Vec<XmssGroup>,
    /// The SPHINCS claims.
    pub sphincs: Vec<SphincsClaim>,
}

/// The most a set may hold: fewer claims than `claims`, at most `groups` groups.
///
/// The groups count both schemes': each XMSS group, and each run of SPHINCS claims of one message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Capacity {
    /// The bound claims stay strictly below.
    pub claims: usize,
    /// The most groups.
    pub groups: usize,
}

/// Why a set is not one a root may publish.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum SignerSetError {
    /// Two XMSS groups out of order, or of one leaf index and message.
    #[error("the XMSS groups are not strictly increasing on (leaf index, message)")]
    UnsortedGroups,
    /// An XMSS group with no key.
    #[error("an XMSS group has no key")]
    EmptyGroup,
    /// An XMSS group whose keys are out of order or repeated.
    #[error("an XMSS group's keys are not strictly increasing")]
    UnsortedKeys,
    /// Two SPHINCS claims out of order or equal.
    #[error("the SPHINCS claims are not strictly increasing on (message, key)")]
    UnsortedSphincs,
    /// As many claims as the capacity's bound, or more.
    #[error("{got} claims, and a set holds fewer than {bound}")]
    TooManyClaims {
        /// The set's claims.
        got: usize,
        /// The exclusive bound.
        bound: usize,
    },
    /// More groups than the capacity.
    #[error("{got} groups, and a set holds at most {most}")]
    TooManyGroups {
        /// The set's groups.
        got: usize,
        /// The most.
        most: usize,
    },
}

/// One item of a set's written form: a block and its counter bits, `START` aside.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Item {
    /// The block.
    pub(crate) block: [u64; 8],
    /// Its counter bits but `START`, which only its place gives.
    pub(crate) code: u64,
}

/// A group as the written form has it: scheme, leaf index, message, then its keys.
struct GroupRef<'a> {
    scheme: Scheme,
    leaf_index: u32,
    message: Message,
    keys: KeysRef<'a>,
}

/// A group's keys: an XMSS group's own, or a run of SPHINCS claims.
enum KeysRef<'a> {
    Xmss(&'a [Key]),
    Sphincs(&'a [SphincsClaim]),
}

impl Scheme {
    /// Its word in a header.
    pub(crate) const fn word(self) -> u64 {
        match self {
            Self::Xmss => code::XMSS,
            Self::Sphincs => code::SPHINCS,
        }
    }
}

impl Capacity {
    /// leanVM `main`'s bounds: fewer than `2^16` claims, at most 1,024 groups.
    pub const MAIN: Self = Self {
        claims: 1 << 16,
        groups: 1024,
    };

    /// The most items a set within the capacity is written as: a header a group, a block per two keys, the end.
    ///
    /// Each group's keys take at most one half-empty block, so `(claims + groups) / 2` blocks hold them.
    #[must_use]
    pub const fn items(&self) -> usize {
        let claims = self.claims.saturating_sub(1);
        self.groups + (claims + self.groups).div_ceil(2) + 1
    }
}

impl KeysRef<'_> {
    const fn len(&self) -> usize {
        match self {
            Self::Xmss(k) => k.len(),
            Self::Sphincs(c) => c.len(),
        }
    }

    const fn get(&self, i: usize) -> Key {
        match self {
            Self::Xmss(k) => k[i],
            Self::Sphincs(c) => c[i].key,
        }
    }
}

impl SignerSet {
    /// The empty set.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            xmss: Vec::new(),
            sphincs: Vec::new(),
        }
    }

    /// The canonical set of these claims, each once.
    pub fn from_claims(claims: impl IntoIterator<Item = Claim>) -> Self {
        let mut claims: Vec<Claim> = claims.into_iter().collect();
        claims.sort_unstable();
        claims.dedup();
        let mut set = Self::new();
        for c in claims {
            match c.scheme {
                Scheme::Xmss => match set.xmss.last_mut() {
                    Some(g) if (g.leaf_index, g.message) == (c.leaf_index, c.message) => g.keys.push(c.key),
                    _ => set.xmss.push(XmssGroup {
                        leaf_index: c.leaf_index,
                        message: c.message,
                        keys: vec![c.key],
                    }),
                },
                Scheme::Sphincs => set.sphincs.push(SphincsClaim {
                    key: c.key,
                    message: c.message,
                }),
            }
        }
        set
    }

    /// The groups as written: the XMSS groups, then the runs of SPHINCS claims of one message.
    fn groups(&self) -> impl Iterator<Item = GroupRef<'_>> {
        let xmss = self.xmss.iter().map(|g| GroupRef {
            scheme: Scheme::Xmss,
            leaf_index: g.leaf_index,
            message: g.message,
            keys: KeysRef::Xmss(&g.keys),
        });
        let sphincs = (self.sphincs.chunk_by(|a, b| a.message == b.message)).map(|run| GroupRef {
            scheme: Scheme::Sphincs,
            leaf_index: 0,
            message: run[0].message,
            keys: KeysRef::Sphincs(run),
        });
        xmss.chain(sphincs)
    }

    /// Every claim, in the set's order.
    pub fn claims(&self) -> impl Iterator<Item = Claim> + '_ {
        self.groups().flat_map(|g| {
            (0..g.keys.len()).map(move |i| Claim {
                scheme: g.scheme,
                leaf_index: g.leaf_index,
                message: g.message,
                key: g.keys.get(i),
            })
        })
    }

    /// How many claims it holds, repeats included.
    #[must_use]
    pub fn n_claims(&self) -> usize {
        self.xmss.iter().map(|g| g.keys.len()).sum::<usize>() + self.sphincs.len()
    }

    /// How many groups it is written as.
    #[must_use]
    pub fn n_groups(&self) -> usize {
        self.groups().count()
    }

    /// Whether it holds no claim.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.xmss.is_empty() && self.sphincs.is_empty()
    }

    /// Its written form, item by item.
    pub(crate) fn items(&self) -> Vec<Item> {
        let mut items = Vec::new();
        for g in self.groups() {
            let [m0, m1, m2, m3] = g.message;
            items.push(Item {
                block: [g.scheme.word(), u64::from(g.leaf_index), m0, m1, m2, m3, 0, 0],
                code: 0,
            });
            for pair in (0..g.keys.len()).collect::<Vec<_>>().chunks(2) {
                let a = g.keys.get(pair[0]);
                let b = pair.get(1).map_or([0; 4], |&i| g.keys.get(i));
                items.push(Item {
                    block: [a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]],
                    code: code::KEY | if pair.len() == 2 { code::PAIR } else { 0 },
                });
            }
        }
        items.push(Item {
            block: [code::TAG, 0, 0, 0, 0, 0, 0, 0],
            code: code::END,
        });
        items
    }

    /// Its digest: the chain of its items' compressions.
    #[must_use]
    pub fn digest(&self) -> [u64; 4] {
        let items = self.items();
        let last = items.len() - 1;
        (items.iter().enumerate()).fold(PARAM_IV, |h: Limbs, (i, item)| {
            let t = item.code | if i == 0 { code::START } else { 0 };
            Compression::new(h, item.block, t, i == last).output()
        })
    }

    /// Check it is canonical and within a capacity: what a root's verifier asks of the set it publishes.
    ///
    /// # Errors
    ///
    /// The first rule it breaks.
    pub fn check(&self, capacity: Capacity) -> Result<(), SignerSetError> {
        if !self
            .xmss
            .windows(2)
            .all(|w| (w[0].leaf_index, w[0].message) < (w[1].leaf_index, w[1].message))
        {
            return Err(SignerSetError::UnsortedGroups);
        }
        if self.xmss.iter().any(|g| g.keys.is_empty()) {
            return Err(SignerSetError::EmptyGroup);
        }
        if !self.xmss.iter().all(|g| g.keys.windows(2).all(|w| w[0] < w[1])) {
            return Err(SignerSetError::UnsortedKeys);
        }
        if !self
            .sphincs
            .windows(2)
            .all(|w| (w[0].message, w[0].key) < (w[1].message, w[1].key))
        {
            return Err(SignerSetError::UnsortedSphincs);
        }
        let claims = self.n_claims();
        if claims >= capacity.claims {
            return Err(SignerSetError::TooManyClaims {
                got: claims,
                bound: capacity.claims,
            });
        }
        let groups = self.n_groups();
        if groups > capacity.groups {
            return Err(SignerSetError::TooManyGroups {
                got: groups,
                most: capacity.groups,
            });
        }
        Ok(())
    }

    /// Its bytes: little-endian throughout.
    ///
    /// ```text
    /// | n_xmss: u32 | per group: leaf_index: u32, message: 4 words, n_keys: u32, keys: 4 words each |
    /// | n_sphincs: u32 | per claim: key: 4 words, message: 4 words |
    /// ```
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let len = |n: usize| u32::try_from(n).expect("fewer than 2^32 entries").to_le_bytes();
        let words = |out: &mut Vec<u8>, w: &[u64; 4]| out.extend(w.iter().flat_map(|x| x.to_le_bytes()));
        let mut out = Vec::new();
        out.extend(len(self.xmss.len()));
        for g in &self.xmss {
            out.extend(g.leaf_index.to_le_bytes());
            words(&mut out, &g.message);
            out.extend(len(g.keys.len()));
            for k in &g.keys {
                words(&mut out, k);
            }
        }
        out.extend(len(self.sphincs.len()));
        for c in &self.sphincs {
            words(&mut out, &c.key);
            words(&mut out, &c.message);
        }
        out
    }

    /// The set these bytes encode, if they encode one and nothing more.
    #[must_use]
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut rest = bytes;
        // Lengths are read before what they count, so a length past the bytes left fails at the read, not at an
        // allocation.
        let n_xmss = take_u32(&mut rest)?;
        let mut set = Self::new();
        for _ in 0..n_xmss {
            let leaf_index = take_u32(&mut rest)?;
            let message = take_words(&mut rest)?;
            let n_keys = take_u32(&mut rest)?;
            let keys = (0..n_keys).map(|_| take_words(&mut rest)).collect::<Option<_>>()?;
            set.xmss.push(XmssGroup {
                leaf_index,
                message,
                keys,
            });
        }
        let n_sphincs = take_u32(&mut rest)?;
        for _ in 0..n_sphincs {
            let key = take_words(&mut rest)?;
            let message = take_words(&mut rest)?;
            set.sphincs.push(SphincsClaim { key, message });
        }
        rest.is_empty().then_some(set)
    }
}

/// The next little-endian `u32` of `rest`.
fn take_u32(rest: &mut &[u8]) -> Option<u32> {
    let (head, tail) = rest.split_first_chunk::<4>()?;
    *rest = tail;
    Some(u32::from_le_bytes(*head))
}

/// The next four little-endian words of `rest`.
fn take_words(rest: &mut &[u8]) -> Option<[u64; 4]> {
    let (head, tail) = rest.split_first_chunk::<32>()?;
    *rest = tail;
    Some(std::array::from_fn(|i| {
        u64::from_le_bytes(head[8 * i..8 * i + 8].try_into().expect("eight bytes"))
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanvm_guest::signers::SignerStream;

    fn key(i: u64) -> Key {
        [i, i ^ 0x5555, i.wrapping_mul(0x9e37_79b9), 7]
    }

    fn xmss(leaf_index: u32, message: u64, keys: &[u64]) -> XmssGroup {
        XmssGroup {
            leaf_index,
            message: [message, 0, 0, 1],
            keys: keys.iter().map(|&i| key(i)).collect(),
        }
    }

    fn sphincs(k: u64, message: u64) -> SphincsClaim {
        SphincsClaim {
            key: key(k),
            message: [message, 2, 0, 0],
        }
    }

    fn sample() -> SignerSet {
        SignerSet {
            xmss: vec![xmss(3, 1, &[1, 2, 3]), xmss(3, 2, &[1]), xmss(4, 1, &[2, 5])],
            sphincs: vec![sphincs(1, 1), sphincs(2, 1), sphincs(1, 4)],
        }
    }

    /// The digest as the guest's stream computes it.
    fn streamed(set: &SignerSet) -> [u64; 4] {
        let mut s = SignerStream::new();
        for g in &set.xmss {
            s.group(leanvm_guest::signers::XMSS, u64::from(g.leaf_index), &g.message);
            g.keys.iter().for_each(|k| s.key(k));
        }
        for run in set.sphincs.chunk_by(|a, b| a.message == b.message) {
            s.group(leanvm_guest::signers::SPHINCS, 0, &run[0].message);
            run.iter().for_each(|c| s.key(&c.key));
        }
        s.finish()
    }

    #[test]
    fn the_digest_is_the_guests() {
        use leanvm_guest::signers as g;
        assert_eq!(
            (
                code::XMSS,
                code::SPHINCS,
                code::START,
                code::KEY,
                code::END,
                code::PAIR,
                code::TAG
            ),
            (g::XMSS, g::SPHINCS, g::START, g::KEY, g::END, g::PAIR, g::TAG)
        );
        let set = sample();
        assert_eq!(set.digest(), streamed(&set));
        assert_eq!(SignerSet::new().digest(), streamed(&SignerSet::new()));
        // Out of order too: the digest is the order's.
        let mut shuffled = set.clone();
        shuffled.xmss.reverse();
        shuffled.sphincs.swap(0, 2);
        assert_eq!(shuffled.digest(), streamed(&shuffled));
        assert_ne!(shuffled.digest(), set.digest());
    }

    #[test]
    fn the_written_form_counts_its_claims() {
        let set = sample();
        assert_eq!((set.n_claims(), set.n_groups()), (9, 5));
        // Groups of 3, 1, 2, 2, 1 keys: 2, 1, 1, 1, 1 blocks of keys, five headers, the end.
        assert_eq!(set.items().len(), 5 + 6 + 1);
        assert!(set.items().len() <= Capacity { claims: 10, groups: 5 }.items());
        assert_eq!(SignerSet::new().items().len(), 1);
    }

    #[test]
    fn distinct_sets_have_distinct_digests() {
        // Neighbours of the sample: a key moved between groups, a group split, a key dropped, a scheme changed.
        let base = sample();
        let mut variants = vec![SignerSet::new()];
        let mut moved = base.clone();
        let k = moved.xmss[0].keys.pop().expect("a key");
        moved.xmss[1].keys.push(k);
        variants.push(moved);
        let mut split = base.clone();
        let tail = split.xmss[0].keys.split_off(2);
        split.xmss.insert(
            1,
            XmssGroup {
                keys: tail,
                ..split.xmss[0].clone()
            },
        );
        variants.push(split);
        let mut dropped = base.clone();
        dropped.sphincs.pop();
        variants.push(dropped);
        let mut scheme = base.clone();
        scheme.xmss.pop();
        scheme.sphincs.extend([sphincs(2, 1), sphincs(5, 1)]);
        variants.push(scheme);
        for (i, v) in variants.iter().enumerate() {
            assert_ne!(v.digest(), base.digest(), "variant {i}");
        }
    }

    #[test]
    fn from_claims_is_canonical() {
        let set = sample();
        let mut claims: Vec<Claim> = set.claims().collect();
        claims.extend(set.claims().take(4));
        claims.reverse();
        let canonical = SignerSet::from_claims(claims);
        assert_eq!(canonical.check(Capacity::MAIN), Ok(()));
        assert_eq!(canonical.n_claims(), 9);
        let mut a: Vec<Claim> = canonical.claims().collect();
        let mut b: Vec<Claim> = set.claims().collect();
        a.sort_unstable();
        b.sort_unstable();
        assert_eq!(a, b);
        assert_eq!(SignerSet::from_claims([]).check(Capacity::MAIN), Ok(()));
    }

    #[test]
    fn check_refuses_every_noncanonical_set() {
        let canonical = SignerSet::from_claims(sample().claims());
        let cap = Capacity::MAIN;
        let mut s = canonical.clone();
        s.xmss.swap(0, 1);
        assert_eq!(s.check(cap), Err(SignerSetError::UnsortedGroups));
        let mut s = canonical.clone();
        s.xmss.push(s.xmss[2].clone());
        assert_eq!(s.check(cap), Err(SignerSetError::UnsortedGroups));
        let mut s = canonical.clone();
        s.xmss[0].keys.clear();
        assert_eq!(s.check(cap), Err(SignerSetError::EmptyGroup));
        let mut s = canonical.clone();
        s.xmss[0].keys.swap(0, 1);
        assert_eq!(s.check(cap), Err(SignerSetError::UnsortedKeys));
        let mut s = canonical.clone();
        let k = s.xmss[0].keys[0];
        s.xmss[0].keys.insert(0, k);
        assert_eq!(s.check(cap), Err(SignerSetError::UnsortedKeys));
        let mut s = canonical.clone();
        s.sphincs.swap(0, 1);
        assert_eq!(s.check(cap), Err(SignerSetError::UnsortedSphincs));
        let mut s = canonical.clone();
        s.sphincs.push(s.sphincs[2]);
        assert_eq!(s.check(cap), Err(SignerSetError::UnsortedSphincs));
        assert_eq!(
            canonical.check(Capacity { claims: 9, groups: 8 }),
            Err(SignerSetError::TooManyClaims { got: 9, bound: 9 })
        );
        assert_eq!(
            canonical.check(Capacity { claims: 10, groups: 4 }),
            Err(SignerSetError::TooManyGroups { got: 5, most: 4 })
        );
        assert_eq!(canonical.check(Capacity { claims: 10, groups: 5 }), Ok(()));
    }

    #[test]
    fn bytes_round_trip_and_nothing_more() {
        let set = sample();
        let bytes = set.to_bytes();
        assert_eq!(SignerSet::from_bytes(&bytes), Some(set));
        assert_eq!(
            SignerSet::from_bytes(&SignerSet::new().to_bytes()),
            Some(SignerSet::new())
        );
        let mut longer = bytes.clone();
        longer.push(0);
        assert_eq!(SignerSet::from_bytes(&longer), None);
        assert_eq!(SignerSet::from_bytes(&bytes[..bytes.len() - 1]), None);
        // A length past the bytes left.
        assert_eq!(SignerSet::from_bytes(&[0xff, 0xff, 0xff, 0xff]), None);
    }
}
