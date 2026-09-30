#!/usr/bin/env bash
# Translate the extracted Rust to Lean: Charon reads each crate's MIR into LLBC, Aeneas
# turns the LLBC into `Extract/<Crate>/{Types,Funs}.lean`, which are generated and not
# checked in: change the Rust (or the start points below) and rerun this.
#
# Needs the `charon` and `aeneas` of the release below, on PATH or in $AENEAS_DIR (the
# release's tarball, unpacked), and the nightly Rust named in the release's
# `rust-toolchain`, with `rustc-dev`, `rust-src` and `miri` (Charon builds a standard
# library with full MIR through `cargo miri setup`).
set -euo pipefail

# Must be the release whose commit `lakefile.toml` requires.
AENEAS_RELEASE=nightly-2026.09.29-b08bf81

here="$(cd "$(dirname "$0")" && pwd)"
if [[ -n "${AENEAS_DIR:-}" ]]; then
  PATH="$AENEAS_DIR:$PATH"
fi
version="$(aeneas -version)"
if [[ "$version" != "aeneas $AENEAS_RELEASE" ]]; then
  echo "expected aeneas $AENEAS_RELEASE, found '$version'" >&2
  exit 1
fi

llbc="$(mktemp -d)"
trap 'rm -rf "$llbc"' EXIT

# `translate <Module> <crate> <directory> <cargo argument>... -- <item>...` runs Charon in
# the directory. An item is a start point, or a Charon option and its pattern (`--opaque X`,
# `--exclude=X`). The LLBC's file name is the Lean module prefix Aeneas imports under. A
# method is `crate::path::_::method`: Charon resolves `crate::path::Type::method` too, but
# then drops it and everything only it reaches.
translate() {
  local module=$1 crate=$2 dir=$3
  shift 3
  local cargo=()
  while [[ $1 != -- ]]; do
    cargo+=("$1")
    shift
  done
  shift
  local items=() starts=()
  while (($#)); do
    case $1 in
      --*=*)
        items+=("$1")
        shift
        ;;
      --*)
        items+=("$1" "$2")
        shift 2
        ;;
      *)
        items+=(--start-from "$1")
        starts+=("$1")
        shift
        ;;
    esac
  done
  (cd "$dir" && charon cargo --preset aeneas "${items[@]}" --dest-file "$llbc/$module.llbc" -- "${cargo[@]}")
  rm -rf "$here/Extract/$module"
  # `-filter-trait-methods`: an impl of a standard trait (`Iterator` for `Map`) keeps
  # only the methods the Lean library's model of the trait has.
  aeneas -backend lean -split-files -abort-on-error -no-progress-bar -filter-trait-methods \
    -dest "$here" -subdir "Extract/$module" "$llbc/$module.llbc"
  # Every start point must name something Aeneas wrote: each item's doc comment opens
  # with its Rust path, an impl's segment in braces. An `--opaque` one is declared in a
  # template.
  local s re
  for s in "${starts[@]}"; do
    re="$(sed -E 's/(^|::)_(::|$)/\1([^:{}]+|\\{[^}]*\\})\2/g' <<<"$crate${s#crate}")"
    if ! grep -qsE "^/-- \[$re(::|\])" "$here/Extract/$module/"{Types,Funs,FunsExternal_Template}.lean; then
      echo "start point '$s' of $module translated nothing" >&2
      exit 1
    fi
  done
  # What Aeneas does not model (standard-library functions it has no model of, items left
  # `--opaque`) its templates declare as axioms: they stand as the externals, so the
  # translation type-checks against their signatures, not their behaviour.
  local t
  for t in "$here/Extract/$module/"*External_Template.lean; do
    if [[ -e $t ]]; then mv "$t" "${t%_Template.lean}.lean"; fi
  done
}

# `extract <Module> <package> <item>...`: a crate of the root workspace. `--cfg aeneas`
# takes the portable arm where the Rust dispatches to assembly, and the baseline x86-64
# CPU the portable arm of every `target_feature` dispatch: those are the reference
# implementations the specialized arms are tested against.
extract() {
  local module=$1 package=$2
  shift 2
  local -x RUSTFLAGS="-C target-cpu=x86-64 --cfg aeneas"
  translate "$module" "${package//-/_}" "$here/.." -p "$package" --target x86_64-unknown-linux-gnu -- "$@"
}

# A guest is its own workspace, whose config builds for the VM. Its library is read for the
# host, where the SDK is portable Rust; a function of its binary only compiles for the VM.
# `extract_guest <Module> <program> lib|bin <item>...`
extract_guest() {
  local module=$1 program=$2 kind=$3
  shift 3
  local target=(--lib --target x86_64-unknown-linux-gnu)
  if [[ $kind == bin ]]; then target=(--bins --target riscv64im-unknown-none-elf); fi
  translate "$module" "$program" "$here/../programs/$program/guest" "${target[@]}" --target-dir "$here/../target" -- "$@"
}

# The `--exclude`s dropping a module's derived `Debug`, `Hash` and serde impls, which only
# print, hash into a `Hasher` or serialize. A `--start-from` naming a method translates
# nothing, so types are extracted through their modules.
no_derives() {
  echo "--exclude=$1::{impl core::fmt::Debug for _}"
  echo "--exclude=$1::{impl core::hash::Hash for _}"
  echo "--exclude=$1::_::{impl serde_core::ser::Serialize for _}"
  echo "--exclude=$1::_::{impl serde_core::de::Deserialize for _}"
}

# The fields and their arithmetic, BLAKE2s (compression, one-shot and streaming), and the
# multilinear helpers that need no thread pool or arena. Left out: the batched hash
# (SIMD lanes, `unsafe`), the bit transpose, and what folds a `map`ped iterator (whose
# `Iterator` impl the Aeneas library does not model).
mapfile -t primitives_derives < <(for m in gf2_64 gf2_8 gf2_64x3; do no_derives "crate::field::$m"; done)
extract Primitives primitives \
  "${primitives_derives[@]}" \
  '--exclude=crate::hash::batch' \
  '--exclude=crate::hash::x86' \
  '--exclude=crate::hash::Backend' \
  '--exclude=crate::hash::LANES' \
  '--exclude=crate::hash::BATCH' \
  '--exclude=crate::hash::hash_many' \
  '--exclude=crate::hash::hash_many_dyn' \
  '--exclude=crate::hash::hash_many_dyn_from_state' \
  '--exclude=crate::field::gf2_64::x86_64' \
  'crate::hash' \
  'crate::field::gf2_64' \
  'crate::field::gf2_8' \
  'crate::field::gf2_64x3' \
  'crate::field::phi8_tower' \
  'crate::field::mul_by_g' \
  'crate::field::mul_by_g_e' \
  'crate::field::G' \
  'crate::field::g_pow' \
  'crate::field::powers' \
  'crate::field::geometric' \
  'crate::field::index_mle' \
  'crate::field::int_index_mle' \
  'crate::field::powers_mle' \
  'crate::multilinear::interp' \
  'crate::multilinear::interp_k' \
  'crate::multilinear::eq_eval' \
  'crate::multilinear::poly_eval' \
  'crate::multilinear::window_denominator' \
  'crate::log2_strict_usize' \
  'crate::log2_ceil_usize'

# A crate's extraction declares again, in its own namespace, every `primitives` struct it
# touches, so it cannot call into `Extract.Primitives`: `--include=primitives` extracts
# the `primitives` code it calls into its own module too. Except the compression, which
# `Extract.Primitives` extracts: dependencies come as optimized MIR, where Aeneas fails on
# it, so it is opaque here.
uses_primitives=('--include=primitives' '--opaque=primitives::hash::compress')

# The Fiat-Shamir state, the verifier's transcript (`Receiver` for `VerifierState`, with the
# Merkle phase opening), digest encodings and Merkle path hashing. Left out: grinding
# (thread pool, batched hash), and so the prover's `Transmitter` impl, and pruning a phase
# (the prover's, a closure argument).
mapfile -t fiat_shamir_derives < <(no_derives crate::merkle; no_derives crate::transcript)
extract FiatShamir fiat_shamir \
  "${uses_primitives[@]}" \
  "${fiat_shamir_derives[@]}" \
  '--exclude=crate::_::grind_pow' \
  '--exclude=crate::merkle::_::prune' \
  '--exclude=crate::transcript::{impl crate::transcript::Transmitter for _}' \
  'crate'

# Gate-list circuits (building one, the verifier's forward walk and the prover's backward
# one), the u64 adder's and multiplier's gates, and the BLAKE2s circuit's reference
# compression, layout and verifier walk. Left out: witness generation (thread pool and
# arena; the gate walk's `||` comes out as a `Prop` and its `&mut`-taking closure
# mistyped), `Block` (the reduction, which `LeanvmCore` extracts with its verifier),
# and the marginal walks (slice `iter_mut`, whose `Iterator` impl the library does not
# model).
extract Flock flock \
  "${uses_primitives[@]}" \
  '--exclude=crate::circuit::_::block' \
  '--exclude=crate::circuit::_::witness_instance' \
  '--exclude=crate::circuit::_::generate_witness' \
  '--exclude=crate::circuit::_::generate_witness_with' \
  '--exclude=crate::arith::add::_::witness' \
  '--exclude=crate::arith::mul::_::witness' \
  'crate::circuit' \
  'crate::arith::add' \
  'crate::arith::mul' \
  'crate::hash::K' \
  'crate::hash::N_G' \
  'crate::hash::USEFUL_BITS' \
  'crate::hash::blake2s_compress' \
  'crate::hash::param_iv' \
  'crate::hash::pinned_compression' \
  'crate::hash::padding_block' \
  'crate::hash::R1CS_DIGEST' \
  'crate::hash::row_values_walk' \
  'crate::hash::bilinear_walk_pair' \
  'crate::hash::bilinear_walk'

# The RISC-V machine (decoding, what each class computes, the interpreter, the
# assembler's encoders, a few helpers of the ELF loader) and the whole SNARK verifier,
# `cpu::verify`: the bus, the table sumcheck, each class's flock reduction and the
# stacked WHIR opening. The crates the verifier calls are extracted into this module
# (`--include`), so it declares their types again in its own namespace. Opaque: the
# compression and the WHIR parameters, derived in `f64`, which Aeneas does not model.
extract LeanvmCore leanvm_core \
  "${uses_primitives[@]}" \
  '--include=fiat_shamir' \
  '--include=pcs' \
  '--include=flock' \
  '--include=parallel' \
  '--include=zk_alloc' \
  '--opaque=pcs::whir::supported_config' \
  'crate::cpu::verify' \
  'crate::rv::decode' \
  'crate::rv::semantics' \
  'crate::rv::legal_flags' \
  'crate::rv::_::is_well_formed' \
  'crate::rv::machine::compute' \
  'crate::rv::machine::compute_hash' \
  'crate::rv::machine::_::new' \
  'crate::rv::machine::_::pc_of' \
  'crate::rv::machine::_::index_of' \
  'crate::rv::machine::_::halt_pc' \
  'crate::rv::machine::_::dt_of' \
  'crate::rv::machine::_::target_of' \
  'crate::rv::machine::_::ram' \
  'crate::rv::machine::_::advice' \
  'crate::rv::machine::_::halted' \
  'crate::rv::machine::_::step' \
  'crate::rv::machine::_::run' \
  'crate::rv::asm::r_type' \
  'crate::rv::asm::i_type' \
  'crate::rv::asm::s_type' \
  'crate::rv::asm::b_type' \
  'crate::rv::asm::u_type' \
  'crate::rv::asm::j_type' \
  'crate::rv::elf::at' \
  'crate::rv::elf::place' \
  'crate::rv::circuits::or_run' \
  'crate::tables::block_slot'

# The witness packing layout, the ring switch's `K`/`E` tensor transpose, and the stacked
# WHIR opening verifier `leanvm_core::pcs::verify` runs, with the ring-switch, induce and
# Merkle checks under it. `supported_config` derives the WHIR parameters in `f64`, which
# Aeneas does not model, so it is opaque. Left out: the NTTs and Merkle tree (SIMD, `unsafe`,
# thread pool), the GF(2^8) NTT (`v[j] += v[i]` borrows `v` twice), and the provers.
extract Pcs pcs \
  "${uses_primitives[@]}" \
  '--include=fiat_shamir' \
  '--opaque=crate::whir::supported_config' \
  '--exclude=crate::pack::{impl core::fmt::Debug for _}' \
  'crate::pack' \
  'crate::tensor_algebra::DEGREE_E' \
  'crate::tensor_algebra::transpose_s_hat' \
  'crate::whir::supported_config' \
  'crate::whir_config::is_supported_log_inv_rate' \
  'crate::stack_open::verify_opening_batch_mixed_whir_stacked'

# The guest SDK off the VM: the hasher and the public values. `m_bytes` views the message
# words as bytes, which Aeneas cannot, so it is opaque; `commit` reads any `Words` type as its
# words through a raw pointer, which no Lean function of an arbitrary type can do.
extract LeanvmGuest leanvm_guest \
  'crate::blake2s' \
  'crate::io' \
  --opaque 'crate::blake2s::_::m_bytes' \
  --exclude 'crate::io::as_words_unchecked' \
  --exclude 'crate::io::assert_words' \
  --exclude 'crate::io::_::commit'

# Two guests whose functions are in their binary: `pow_mod` and `gcd`, and the BLAKE2s
# compression in plain Rust.
extract_guest Numbers numbers bin 'crate::pow_mod' 'crate::gcd'
extract_guest Blake2s blake2s bin 'crate::compress'

# leanXMSS: verification, and key generation and signing.
extract_guest Leanxmss leanxmss lib 'crate::verify' 'crate::sign'

# leanSPHINCS: verification, serialization, and key generation and signing.
extract_guest Leansphincs leansphincs lib 'crate::verify' 'crate::_::to_bytes' 'crate::sign'

# leanDA: the reduction, the Merkle root and the hashes. `weigh` makes Aeneas fail (an
# internal error), so `is_orthogonal` and `check` are left out, and `commit` too
# (Aeneas reaches an unreachable case on `fill` of a sub-slice).
extract_guest Leanda leanda lib 'crate::reduce' 'crate::merkle_root' 'crate::hash_pair' 'crate::dual_digest'
