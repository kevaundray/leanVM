//! The dispatches run one index at a time, in order: what the Lean extraction
//! (`--cfg aeneas`) reads in place of the pool, whose type-erased jobs, atomics and
//! raw pointers it cannot translate. Same signatures and results as the pool's:
//! `tests/pool.rs` passes on both (`RUSTFLAGS="--cfg aeneas" cargo test -p parallel`).

/// One: every dispatch runs on the caller alone.
pub fn num_threads() -> usize {
    1
}

pub fn for_each_chunk<F: Fn(usize, usize) + Sync>(n_tasks: usize, f: F) {
    if n_tasks > 0 {
        f(0, n_tasks);
    }
}

pub fn for_each<F: Fn(usize) + Sync>(n_tasks: usize, f: F) {
    for i in 0..n_tasks {
        f(i);
    }
}

pub fn chunks_mut<T: Send, F>(data: &mut [T], chunk: usize, f: F)
where
    F: Fn(usize, &mut [T]) + Sync,
{
    assert!(chunk > 0, "chunk width must be non-zero");
    let len = data.len();
    for i in 0..len.div_ceil(chunk) {
        let start = i * chunk;
        f(i, &mut data[start..len.min(start + chunk)]);
    }
}

pub fn chunks_mut2<A: Send, B: Send, F>(a: &mut [A], b: &mut [B], chunk: usize, f: F)
where
    F: Fn(usize, &mut [A], &mut [B]) + Sync,
{
    assert_eq!(a.len(), b.len(), "chunks_mut2: slices differ in length");
    assert!(chunk > 0, "chunk width must be non-zero");
    let len = a.len();
    for i in 0..len.div_ceil(chunk) {
        let start = i * chunk;
        let end = len.min(start + chunk);
        f(i, &mut a[start..end], &mut b[start..end]);
    }
}

pub fn chunks_mut_zip<T: Send, S: Sync, F>(dst: &mut [T], src: &[S], chunk: usize, f: F)
where
    F: Fn(usize, &mut [T], &[S]) + Sync,
{
    assert_eq!(dst.len(), src.len(), "chunks_mut_zip: slices differ in length");
    assert!(chunk > 0, "chunk width must be non-zero");
    let len = dst.len();
    for i in 0..len.div_ceil(chunk) {
        let start = i * chunk;
        let end = len.min(start + chunk);
        f(i, &mut dst[start..end], &src[start..end]);
    }
}

pub fn for_each_mut<T: Send, F>(data: &mut [T], f: F)
where
    F: Fn(usize, &mut T) + Sync,
{
    for i in 0..data.len() {
        f(i, &mut data[i]);
    }
}

pub fn fill<T: Send, F: Fn(usize) -> T + Sync>(dst: &mut [T], build: F) {
    for i in 0..dst.len() {
        dst[i] = build(i);
    }
}

pub fn map_collect<T: Send, F: Fn(usize) -> T + Sync>(n_tasks: usize, f: F) -> Vec<T> {
    let mut out = Vec::with_capacity(n_tasks);
    for i in 0..n_tasks {
        out.push(f(i));
    }
    out
}

pub fn find_first<P: Fn(usize) -> bool + Sync>(n_tasks: usize, pred: P) -> Option<usize> {
    let mut i = 0;
    while i < n_tasks && !pred(i) {
        i += 1;
    }
    (i < n_tasks).then_some(i)
}

pub fn map_reduce<T, ID, M, R>(n_tasks: usize, identity: ID, map: M, reduce: R) -> T
where
    T: Send,
    ID: Fn() -> T,
    M: Fn(usize) -> T + Sync,
    R: Fn(T, T) -> T + Sync,
{
    let mut acc = identity();
    for i in 0..n_tasks {
        acc = reduce(acc, map(i));
    }
    acc
}

pub fn fold_reduce<A, I, F, C>(n_tasks: usize, init: I, fold: F, _combine: C) -> A
where
    A: Send,
    I: Fn() -> A + Sync,
    F: Fn(&mut A, usize) + Sync,
    C: Fn(A, A) -> A,
{
    let mut acc = init();
    for i in 0..n_tasks {
        fold(&mut acc, i);
    }
    acc
}

pub fn map_reduce_with_state<S, A, IS, IA, F, C>(
    n_tasks: usize,
    init_state: IS,
    init_acc: IA,
    fold: F,
    _combine: C,
) -> A
where
    S: Send,
    A: Send,
    IS: Fn() -> S + Sync,
    IA: Fn() -> A + Sync,
    F: Fn(&mut S, &mut A, usize) + Sync,
    C: Fn(A, A) -> A,
{
    let mut state = init_state();
    let mut acc = init_acc();
    for i in 0..n_tasks {
        fold(&mut state, &mut acc, i);
    }
    acc
}
