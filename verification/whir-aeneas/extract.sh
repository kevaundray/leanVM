#!/usr/bin/env bash
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../.." && pwd)
tools="$here/.tools/aeneas"
"$here/bootstrap.sh"
generator="$here/.tools/aeneas-source/src/_build/default/main.exe"
frontend="$here/.tools/aeneas-source/charon/charon/target/release/charon"
if [[ ! -x "$generator" || ! -x "$frontend" || ! -f "$here/.tools/charon-build.sha256" ]] ||
    ! sha256sum -c "$here/.tools/charon-build.sha256" >/dev/null; then
    "$here/bootstrap-tool.sh"
fi
export PATH="$tools:$PATH"
export CARGO_BUILD_JOBS=2 LEAN_NUM_THREADS=2
export RUSTFLAGS='-C target-cpu=x86-64'
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$here/.tools/target}"
surface=${1:-statement}
aeneas_args=(-backend lean -namespace PcsSource -emit-json -no-progress-bar -abort-on-error)
crate="$root/crates/pcs"
llbc_name=pcs
case "$surface" in
    statement)
        dest="$here/llbc/statement"
        generated="$here"
        args=(--start-from pcs::stack::Statement::check --include primitives)
        cargo_args=(--lib --release)
        aeneas_args=(-backend lean -namespace StatementSource -no-progress-bar
                     -abort-on-error -all-computable -split-files -subdir WhirAeneas/Generated/Statement)
        ;;
    verifier)
        dest="$here/llbc/verifier"
        generated="$here"
        args=(--start-from pcs::whir::verify::verify_with_basis --include primitives --include fiat_shamir)
        cargo_args=(--lib --release)
        aeneas_args+=(-subdir WhirAeneas/Generated/Verifier -split-files -all-computable)
        ;;
    native)
        dest="$here/failures/native"
        generated="$dest/generated"
        args=(--start-from-if-exists pcs::stack::tests::verify_instance --include primitives --include fiat_shamir)
        cargo_args=(--lib --tests --release)
        ;;
    native-hash-interface|native-hash-interface-mono)
        dest="$here/failures/$surface"
        generated="$dest/generated"
        args=(--start-from-if-exists pcs::stack::tests::verify_instance --include primitives --include fiat_shamir
              --opaque primitives::hash::compress
              --opaque fiat_shamir::merkle::hash_pairs
              --opaque fiat_shamir::merkle::hash_packed_leaves
              --opaque 'fiat_shamir::merkle::{impl fiat_shamir::merkle::LeafHasher}::hash'
              --opaque primitives::hash::hash
              --opaque primitives::hash::hash_many
              --opaque primitives::hash::hash_many_dyn_from_state
              --opaque primitives::hash::hash_from_state
              --opaque primitives::hash::zero_prefix_state)
        if [[ "$surface" == native-hash-interface-mono ]]; then
            args+=(--monomorphize)
        fi
        cargo_args=(--lib --tests --release)
        ;;
    portable)
        crate="$root/crates/primitives"
        llbc_name=primitives
        dest="$here/llbc/portable"
        generated="$here/WhirAeneas/Generated/Portable"
        args=(--start-from primitives::hash::compress_portable)
        cargo_args=(--lib --release)
        aeneas_args=(-backend lean -namespace PortableSource -emit-json -no-progress-bar -all-computable)
        ;;
    *) printf 'unknown extraction surface: %s\n' "$surface" >&2; exit 2 ;;
esac
mkdir -p "$dest" "$generated"
cd "$crate"
flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 "$frontend" cargo --preset=aeneas "${args[@]}" --dest-file "$dest/$llbc_name.llbc" -- "${cargo_args[@]}"
if [[ "$surface" == native || "$surface" == native-hash-interface* ]]; then
    python3 "$here/toolchain/check-extracted-root.py" "$dest/$llbc_name.llbc" pcs::stack::tests::verify_instance
fi
if [[ "$surface" == statement ]]; then
    python3 "$here/toolchain/check-extracted-root.py" "$dest/$llbc_name.llbc" pcs::stack::Statement::check
fi
flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 "$generator" "${aeneas_args[@]}" -dest "$generated" "$dest/$llbc_name.llbc"
