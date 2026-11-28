//! The field the disassembler reads immediates in: the verifier's `K` and `E`, under the names the provers give them.

pub use verifier::{E as F128, K as F64};

/// The generator `g = x` of `K`, and one.
pub trait Base: Sized {
    const ONE: Self;
    const G: Self;
}

impl Base for F64 {
    const ONE: Self = F64(1);
    const G: Self = F64(2);
}

/// The base-field element a word is, or `None` when its `y` coefficient is nonzero.
pub fn as_base(word: F128) -> Option<F64> {
    (word.c1 == 0).then_some(F64(word.c0))
}
