#!/usr/bin/env bash
# Upload `bench.json` to Bencher: `bencher.sh <testbed> [threshold flags]`.
# On a branch PRs target (bench.yml's push branches) the flags replace the testbed's
# thresholds; a PR compares against its base's history and clones its thresholds, and
# any other branch does the same against riscv-exploration.
# ERROR_ON_ALERT=1 fails the job on an alert, rather than only reporting it.
set -euo pipefail

testbed=$1
shift
if [ "$GITHUB_EVENT_NAME" = pull_request ]; then
  args=(--branch "$GITHUB_HEAD_REF" --start-point "$GITHUB_BASE_REF" --start-point-hash "$BASE_SHA"
    --start-point-clone-thresholds --start-point-reset)
elif [ "$GITHUB_REF_NAME" = main ] || [ "$GITHUB_REF_NAME" = riscv-exploration ]; then
  args=(--branch "$GITHUB_REF_NAME" "$@" --thresholds-reset)
else
  args=(--branch "$GITHUB_REF_NAME" --start-point riscv-exploration --start-point-clone-thresholds --start-point-reset)
fi
if [ "${ERROR_ON_ALERT:-}" = 1 ]; then
  args+=(--error-on-alert)
fi

bencher run \
  --project "$BENCHER_PROJECT" \
  --key "$BENCHER_API_KEY" \
  --testbed "$testbed" \
  "${args[@]}" \
  --adapter json \
  --file bench.json \
  --github-actions "$GITHUB_TOKEN"
