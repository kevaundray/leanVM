# Shielded mobile benchmarks

This directory is a separate Cargo workspace for the `leanvm-mobile-bench` package and `leanvm_mobile_bench` library. It depends on the repository's public `leanvm` API and shielded host fixture through path dependencies. Its SDK dependencies and lockfile stay outside the production workspace. The native C ABI runner exports real proving benchmarks, not host timing estimates or emulator measurements.

## Workloads

| Registered function | Timed work | Untimed work |
| --- | --- | --- |
| `leanvm_mobile_bench::shielded_prove` | Prove one fixed one-spend shielded leaf | Construct deterministic advice and load the existing ELF; verify every output and proof after timing |
| `leanvm_mobile_bench::shielded_aggregate` | Aggregate two pre-proven copies of that one-spend leaf | Prove and verify both leaves, construct the aggregation tree, then verify every aggregate proof after timing |

Each shielded spend has two input notes, two output notes, and depth-20 membership paths. Leaves use `log_inv_rate = 2`; aggregation uses `log_inv_rate = 1`, first-level arity 2, and higher-level arity 2. Defaults are one warmup and three measured iterations. The benchmark initializes the existing parallel pool with exactly one thread and rejects an incompatible already-initialized pool. No guest ELF or proof protocol is changed. Proof buffers use the current API's ordinary global allocator; no historical arena API is assumed.

The SDK owns timing. Completed proofs are retained until teardown, where they are verified and dropped outside the timed interval. Raw reports include workload and verification counters. Peak process memory can include setup, retained proofs, and allocator residency; it is not solely the memory consumed by one timed operation. Median, p95, and individual samples are useful diagnostics, but three samples do not establish a precise tail distribution. Shared hosted devices can vary with scheduling, CPU frequency, and thermal state. Compare only the same workload, device model, OS, build flags, and toolchain. There is no performance-regression threshold gate.

## Toolchain and packaging

The workflow pins Rust 1.99.0, `cargo-ndk` 4.1.2, Android SDK 34, build-tools 34.0.0, NDK 26.1.10909125, Java 17, and Gradle 8.5. The CLI and SDK both use Worldcoin `mobile-bench-rs` revision `217cfd4f78db1284276a1a1da44e3bf473729f5c` (0.1.49). See the pinned [build guide](https://github.com/worldcoin/mobile-bench-rs/blob/217cfd4f78db1284276a1a1da44e3bf473729f5c/docs/guides/build.md) and [BrowserStack guide](https://github.com/worldcoin/mobile-bench-rs/blob/217cfd4f78db1284276a1a1da44e3bf473729f5c/docs/guides/browserstack-ci.md).

Use the standalone `mobench` executable. Source scanning can warn that there are no `#[benchmark]` attributes because these setup/teardown benchmarks register `BenchFunction` entries directly. Runtime registration is checked by the native smoke executable, not by source scanning.

Install host tools with neutral flags, rather than the repository's native CPU flags:

```sh
rustup toolchain install 1.99.0 --profile minimal --target aarch64-linux-android
RUSTFLAGS='' cargo +1.99.0 install cargo-ndk --version 4.1.2 --locked
RUSTFLAGS='' cargo +1.99.0 install mobench --git https://github.com/worldcoin/mobile-bench-rs --rev 217cfd4f78db1284276a1a1da44e3bf473729f5c --locked
```

With the pinned Android tools, Java, and Gradle installed, run from this directory:

```sh
export RUSTUP_TOOLCHAIN=1.99.0
export RUSTFLAGS='-C target-cpu=generic'
export CARGO_BUILD_JOBS=2
export ANDROID_NDK_HOME="$ANDROID_HOME/ndk/26.1.10909125"
python3 ../scripts/mobile-bench-package.py shielded_prove
python3 ../scripts/mobile-bench-package.py shielded_aggregate
```

`mobench.toml` is discovered as project configuration; do not pass it as `--config`, which accepts a different run-spec schema. `project.output_dir = "."` places generated Android files directly under this isolated workspace, so the pinned Gradle template finds the persisted `target/mobile-spec/android/bench_spec.json` after runner regeneration. The generated `android/` directory is ignored. `mobench run` without devices packages the real shielded specification without contacting BrowserStack; its package-check report is not a performance result. The app/test APKs are under `android/app/build/outputs/apk/`. The benchmark library is built only for `arm64-v8a`; the upstream JNA dependency also bundles its own support libraries for other ABIs. Explicit `RUSTFLAGS` overrides the repository's `target-cpu=native` setting. The generic ARM64 package includes baseline NEON support without assuming optional AES/PMULL or SHA3 instructions. CI separately checks compilation of those optional crypto kernels with `-C target-feature=+aes,+sha3`; that build is not the device package.

The package script uses the supported `mobench run` command without `--devices`, then `mobench verify`, and checks both APKs' embedded function, warmup and iteration count. It also checks the app contains the ARM64 benchmark library. Checked app/test APK pairs for both workloads are retained under `target/mobile-bench-packages/`; this is the same credential-free path CI executes.

A host-only correctness smoke, not a mobile measurement, is available from this directory with `RUSTFLAGS='-C target-cpu=generic' cargo +1.99.0 run --release --locked --bin mobile-bench-smoke`.

## BrowserStack execution

BrowserStack **App Automate real-device** access is required. A generic BrowserStack account or browser-automation entitlement alone does not establish access. The two credential names are `BROWSERSTACK_USERNAME` and `BROWSERSTACK_ACCESS_KEY`. They must already be available to the trusted workflow or exported privately for a local run. No source file contains credentials, and this integration does not change repository settings, create secrets, purchase access, or require manually creating an app in the dashboard. `mobench ci run` builds and uploads the app and instrumentation package automatically.

An authorized administrator should add those two **repository Actions secrets** in the repository that will execute the workflow, under Settings > Secrets and variables > Actions > New repository secret. For this fork, that repository is `kevaundray/leanVM`; upstream secrets are not inherited. Obtain the values from the existing BrowserStack account's access-key page, with App Automate access already enabled. Do not paste values into workflow files, issue comments, or command arguments, and do not change billing or permissions to bypass an entitlement failure.

After the secrets are available in the fork, request the trusted branch run:

```sh
gh workflow run mobile-bench.yml --repo kevaundray/leanVM --ref kw/mobile-bench-browserstack
```

The fixed initial candidate is `Google Pixel 7-13.0`. It is not assumed available: the runner first queries the authenticated Android catalog, records only the matching model/OS/availability fields, and validates the identifier before submission. Missing credentials, missing device availability, or provider entitlement errors fail the run instead of falling back to a different phone or emulator. Catalog validation is not proof of a completed hardware run; successful device reports are required for that.

From this directory, after providing both credentials privately, run `python3 ../scripts/mobile-bench-run.py`. It requests both fully qualified functions through the supported `mobench ci run --functions` option, release mode, one warmup, three samples, and artifact fetching. The pinned CLI executes functions sequentially, so this is two serial device sessions with one concurrent session, not two parallel devices. The harness watchdog is 1200 seconds and fetching is bounded at 1500 seconds. The output directory must not already exist, preventing stale results from being mistaken for a new run; move an earlier `target/mobile-bench-results` directory aside before running again.

## CI trust boundary and artifacts

`.github/workflows/mobile-bench.yml` runs credential-free Android ARM64 release packaging on pull requests, including fork PRs. It never uses `pull_request_target`, downloads a PR package into a credential-bearing job, or accepts a caller-supplied revision. The workflow has only `contents: read`, disables persisted checkout credentials, pins third-party actions by commit, and does not share build caches between PR and trusted runs.

Trusted device execution is limited to `leanEthereum/leanVM` and `kevaundray/leanVM`. Nightly workflows running on `main` or `riscv-exploration` always check out the fixed `riscv-exploration` branch and record the actual resolved commit. GitHub runs schedules only when the workflow is on the default branch. Manual dispatch accepts only `riscv-exploration` or `kw/mobile-bench-browserstack` and checks out the triggering immutable SHA. Pushes to the integration branch run credential-free package checks only. A workflow that has not reached the default branch may not be available for manual dispatch. Secrets are repository-scoped: credentials configured in upstream do not become available to a fork, and must be provisioned by an authorized administrator in the repository that runs the trusted workflow.

The credential-bearing step alone receives the two BrowserStack secrets. All trusted runs share a non-cancelling concurrency group, and the workflow uses no device matrix. The job timeout is 120 minutes; device execution is additionally limited to 65 minutes. Build failures and provider or benchmark failures fail the job, but timing differences do not.

The package artifact retains release app/test APKs for seven days. The result artifact retains `summary.json`, `summary.md`, `results.csv`, per-function reports, `raw-results.json` containing unaggregated benchmark samples, and `metadata.json` for 30 days. Metadata records the actual source SHA, trigger, Rust/compiler options, SDK/NDK pins, fixed workload, authenticated candidate match, and completion state. Unknown SoC and thermal data remain null rather than being inferred from a product name; any metrics present in raw device reports are retained.

Provider logs, complete session metadata, video files, and signed download URLs are not uploaded. The wrapper uses private temporary storage, strips URL-bearing and credential-bearing JSON fields, and redacts URLs and credential values from exported reports. On command failure it exports a bounded, redacted diagnostic excerpt to `diagnostics.txt` so entitlement or device errors remain actionable without publishing broad provider logs. Missing credentials still produce failure metadata, not benchmark results. No hardware result should be inferred from successful cross-compilation alone.
