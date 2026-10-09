# Shielded mobile benchmarks

This directory is a separate Cargo workspace for the `leanvm-mobile-bench` package and `leanvm_mobile_bench` library. It depends on the repository's public `leanvm` API and shielded host fixture through path dependencies. Its SDK dependencies and lockfile stay outside the production workspace. The native C ABI runner exports real proving benchmarks, not host timing estimates or emulator measurements.

## Workloads

| Registered function | Timed work | Untimed work |
| --- | --- | --- |
| `leanvm_mobile_bench::shielded_prove` | Prove one fixed two-spend shielded execution | Construct deterministic advice and load the existing ELF; verify every output and proof after timing |
| `leanvm_mobile_bench::shielded_aggregate` | Prove one 2-to-1 aggregation of two two-spend leaves, four spends total | Generate and verify both independent leaves and construct the tree once; verify every returned root after timing |

Each leaf input is exactly `shielded_host::spends(2)`: one private transfer followed by one withdrawal, proved together in one VM execution. Each spend consumes two input notes with depth-20 membership paths, so standalone proving covers four input notes and aggregation covers eight; the withdrawal has one empty output slot. Leaf proofs use `log_inv_rate = 2`; aggregation uses `log_inv_rate = 1`. Aggregation generates its two leaves on the device once per invocation, without prebuilt fixtures, and reuses those verified leaves and one tree for one warmup and three measured root proofs. Standalone proving retains the same workload and sample counts.

The benchmark queries Rust's `available_parallelism` once per device process and configures exactly that many total pool threads, including the dispatcher, without adding an extra worker. The count is reused across warmup, samples, and repeated invocations. Raw metrics record detected parallelism and actual pool count; OS resource limits can make this smaller than the phone's physical core count. An incompatible already-initialized pool is rejected. No guest ELF or proof protocol is changed. Proof buffers use the current API's ordinary global allocator.

The SDK owns timing. Completed proofs are retained until teardown, where they are verified and dropped outside the timed interval. Raw reports include workload and verification counters. Peak process memory can include setup, retained proofs, and allocator residency; it is not solely the memory consumed by one timed operation. Median, p95, and individual samples are useful diagnostics, but three samples do not establish a precise tail distribution. Shared hosted devices can vary with scheduling, CPU frequency, and thermal state. Compare only the same workload, device model, OS, actual thread count, build flags, and toolchain; never pool sessions with different thread counts. There is no performance-regression threshold gate.

## Toolchain and packaging

The workflow pins Rust 1.99.0, `cargo-ndk` 4.1.2, Android SDK 34, build-tools 34.0.0, NDK 26.1.10909125, Java 17, and Gradle 8.5. The CLI and SDK both use Worldcoin `mobile-bench-rs` revision `217cfd4f78db1284276a1a1da44e3bf473729f5c` (0.1.49). See the pinned [build guide](https://github.com/worldcoin/mobile-bench-rs/blob/217cfd4f78db1284276a1a1da44e3bf473729f5c/docs/guides/build.md) and [BrowserStack guide](https://github.com/worldcoin/mobile-bench-rs/blob/217cfd4f78db1284276a1a1da44e3bf473729f5c/docs/guides/browserstack-ci.md).

iOS packaging runs on the macOS 15 image with Xcode 16.4 (iPhoneOS SDK 18.5), XcodeGen 2.44.1 by checksum, and Rust targets `aarch64-apple-ios`, `aarch64-apple-ios-sim` and `x86_64-apple-ios`. The physical workload targets iOS 16.0; the build SDK version is not the phone's OS version. `ios.xcconfig` sets Swift language mode 5 through `XCODE_XCCONFIG_FILE`, because the pinned toolkit template uses the compiler version `5.9` where Xcode expects a language mode. No Apple developer credentials or provisioning profile are configured; the toolkit packages for BrowserStack ad-hoc re-signing.

The isolated lockfile retains libc 0.2.189 for the pinned mobench SDK's iOS resource sampler. libc 0.2.190 restricts its `mach_task_self` binding to macOS, while mobench 0.1.49 calls it on iOS too. The iPhoneOS 18.5 SDK still declares and exports the underlying `mach_task_self_` API; this compatibility pin preserves the real `task_info` memory measurement rather than disabling it. Revisit the pin when upgrading mobench.

The library emits a `staticlib` for the iOS XCFramework, a `cdylib` for Android and an `rlib` for the native correctness smoke.

ARM64 mobile packages use `-C target-cpu=generic` with platform-specific extensions: Android uses `-C target-feature=+aes,-sha3` for PMULL field multiplication, while iOS uses `-C target-feature=+aes,+sha3` for PMULL and EOR3 XORs. The Pixel 7 benchmark worker trapped with an illegal instruction when both extensions were enabled, so its build explicitly excludes SHA3. These builds require their enabled extensions on the device; they do not select a fallback at runtime. Flags are scoped to Cargo target triples, including the ARM64 iOS simulator; the x86 iOS simulator stays generic and host tools receive no mobile flags. The repository's native CPU setting excludes iOS and Android. Do not set global `RUSTFLAGS` or `CARGO_ENCODED_RUSTFLAGS` when packaging: they override the target-specific flags. Device result metadata records the target's compiler flags.

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
unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS
export CARGO_TARGET_AARCH64_LINUX_ANDROID_RUSTFLAGS='-C target-cpu=generic -C target-feature=+aes,-sha3'
export CARGO_BUILD_JOBS=2
export ANDROID_NDK_HOME="$ANDROID_HOME/ndk/26.1.10909125"
python3 ../scripts/mobile-bench-package.py --platform android shielded_prove
python3 ../scripts/mobile-bench-package.py --platform android shielded_aggregate
```

`mobench.toml` is discovered as project configuration; do not pass it as `--config`, which accepts a different run-spec schema. `project.output_dir = "."` places generated Android files directly under this isolated workspace, so the pinned Gradle template finds the persisted `target/mobile-spec/android/bench_spec.json` after runner regeneration. The generated `android/` directory is ignored. `mobench run` without devices packages the real shielded specification without contacting BrowserStack; its package-check report is not a performance result. The app/test APKs are under `android/app/build/outputs/apk/`. The benchmark library is built only for `arm64-v8a`; the upstream JNA dependency also bundles its own support libraries for other ABIs.

The Android package path uses the supported `mobench run` command without `--devices`, then `mobench verify`, and checks both APKs' embedded function, warmup and iteration count. It also checks the app contains the ARM64 benchmark library. Checked artifacts are retained separately under `target/mobile-bench-packages/android/<function>/`.

A host-only correctness smoke, not a mobile measurement, is available from this directory with `RUSTFLAGS='-C target-cpu=generic' cargo +1.99.0 run --release --locked --bin mobile-bench-smoke`.

On a Mac with the pinned Xcode and XcodeGen, install the same mobench revision and the three iOS Rust targets. Unset `RUSTFLAGS` and `CARGO_ENCODED_RUSTFLAGS`, export `CARGO_TARGET_AARCH64_APPLE_IOS_RUSTFLAGS` and `CARGO_TARGET_AARCH64_APPLE_IOS_SIM_RUSTFLAGS` as `-C target-cpu=generic -C target-feature=+aes,+sha3`, and export `CARGO_TARGET_X86_64_APPLE_IOS_RUSTFLAGS` as `-C target-cpu=generic`. Then run `RUSTUP_TOOLCHAIN=1.99.0 python3 ../scripts/mobile-bench-package.py --platform ios <function>` for each of `shielded_prove` and `shielded_aggregate`. The credential-free path builds the native C ABI XCFramework and packages the device IPA and XCUITest bundle using `mobench package-ipa` and `mobench package-xcuitest`. It checks the app's embedded benchmark specification, device platform, deployment target and ARM64 binaries, including the test runner. Upload packages are retained separately under `target/mobile-bench-packages/ios/<function>/`. Generated `ios/` files are ignored.

## BrowserStack execution

BrowserStack **App Automate real-device** access is required. A generic BrowserStack account or browser-automation entitlement alone does not establish access. The two credential names are `BROWSERSTACK_USERNAME` and `BROWSERSTACK_ACCESS_KEY`. They must already be available to the trusted workflow or exported privately for a local run. No source file contains credentials, and this integration does not change repository settings, create secrets, purchase access, or require manually creating an app in the dashboard. `mobench ci run` builds and uploads the app and instrumentation package automatically.

An authorized administrator should add those two **repository Actions secrets** in the repository that will execute the workflow, under Settings > Secrets and variables > Actions > New repository secret. For this fork, that repository is `kevaundray/leanVM`; upstream secrets are not inherited. Obtain the values from the existing BrowserStack account's access-key page, with App Automate access already enabled. Do not paste values into workflow files, issue comments, or command arguments, and do not change billing or permissions to bypass an entitlement failure.

After the secrets are available in the fork, request the trusted branch run:

```sh
gh workflow run mobile-bench.yml --repo kevaundray/leanVM --ref kw/mobile-bench-browserstack
```

The fixed candidates are `Google Pixel 7-13.0` for Android and `iPhone 14-16` for iOS. Neither is assumed available: the runner first queries that platform's authenticated catalog, records only the matching model/OS/availability fields, and validates the identifier before submission. Missing credentials, missing device availability, or provider entitlement errors fail the run instead of falling back to a different phone or emulator. Catalog validation is not proof of a completed hardware run; successful device reports are required for that.

From this directory, after providing both credentials privately, run `python3 ../scripts/mobile-bench-run.py --platform android`, or `--platform ios` on the configured Mac. Each requests both registered functions through one supported `mobench ci run --functions` invocation, release mode, one warmup and three samples per function, and artifact fetching. The pinned toolkit runs one device session per function sequentially on the same requested model and OS. The benchmark/completion watchdog is 1200 seconds and fetching is bounded at 1500 seconds. The platform's `target/mobile-bench-results/<platform>` output directory must not already exist, preventing stale results from being mistaken for a new run.

## CI trust boundary and artifacts

`.github/workflows/mobile-bench.yml` runs credential-free Android and iOS ARM64 release packaging on pull requests, including fork PRs. It never uses `pull_request_target`, downloads a PR package into a credential-bearing job, or accepts a caller-supplied revision. Build/device jobs have only `contents: read`; the separate reporting job can write PR comments. Checkout credentials are not persisted, third-party actions are pinned by commit, and PR/trusted runs do not share build caches.

Trusted device execution is limited to `leanEthereum/leanVM` and `kevaundray/leanVM`. Nightly workflows running on `main` or `riscv-exploration` always check out the fixed `riscv-exploration` branch and record the actual resolved commit. GitHub runs schedules only when the workflow is on the default branch. Manual dispatch accepts only `riscv-exploration` or `kw/mobile-bench-browserstack` and checks out the triggering immutable SHA. Pushes to the integration branch run credential-free package checks only. A workflow that has not reached the default branch may not be available for manual dispatch. Secrets are repository-scoped: credentials configured in upstream do not become available to a fork, and must be provisioned by an authorized administrator in the repository that runs the trusted workflow.

The credential-bearing step alone receives the two BrowserStack secrets. All trusted runs share a non-cancelling concurrency group. The iPhone build and device run execute first; Android follows using the same resolved source SHA, so the account runs at most one device session at a time. Android's job timeout is 120 minutes and iOS's is 150 minutes; each device step is additionally limited to 65 minutes. Build failures and provider or benchmark failures fail the job, but timing differences do not.

The package artifact retains release app/test packages for seven days. The result artifact retains `summary.json`, `summary.md`, `results.csv`, per-function reports, `raw-results.json` containing unaggregated benchmark samples, `sessions.json` containing session IDs and whitelisted device/OS/status fields, and `metadata.json` for 30 days. Metadata records the actual source SHA, trigger, Rust/compiler options, SDK/NDK pins, authenticated candidate match, and completion state. Its `benchmarks` object is keyed by full registered function and records observed threads, workload, rates and verification counts; shared thread fields are present only when both functions agree. Completion requires both functions, three samples and four verified output proofs each, plus two verified input leaves for aggregation. The requested model/OS identifier is checked separately from BrowserStack's model-only summary name. Root-embedded and per-function report copies must agree; duplicates, missing functions or conflicting samples fail validation. Unknown SoC and thermal data remain null; raw device metrics are retained.

Trusted device runs also put a validated results table directly in the Actions job summary: workload, model/OS, actual threads, median, sample range and proof-verification count, followed by the raw timing samples. The same concise report is retained as `ci-summary.md`. An incomplete run publishes a failure summary, never a latency result. The renderer recomputes statistics from the raw samples and checks their workload, thread counts and provenance against the run metadata.

Artifacts are named `mobile-bench-android-packages/results` and `mobile-bench-ios-packages/results`. The iOS package artifact contains the IPA and XCUITest ZIP rather than APKs; its metadata records the observed Xcode/SDK versions rather than Android tool versions. The reporting job combines both platform sections into one PR comment. A failed platform contributes no latency row and does not erase the other platform's successful results.

A separate reporting job has `pull-requests: write` but no BrowserStack credentials. It creates or updates one `leanvm-mobile-bench` comment on an open PR in the executing repository only when GitHub confirms that PR's current head is the measured source commit from that repository. Stale results are not attached to a newer head. A fork's token cannot publish upstream comments; the upstream trusted workflow publishes upstream results after integration. Nightly results without a matching open PR remain in the Actions summary and artifacts. Unlike desktop CI's paired base/PR measurements, these are absolute device timings with no comparison or regression threshold. PR packaging alone does not produce phone timings.

Provider logs, complete session metadata, video files, and signed download URLs are not uploaded. The wrapper uses private temporary storage, strips URL-bearing and credential-bearing JSON fields, and redacts URLs and credential values from exported reports. On command failure it exports a bounded, redacted diagnostic excerpt to `diagnostics.txt` so entitlement or device errors remain actionable without publishing broad provider logs. Missing credentials still produce failure metadata, not benchmark results. No hardware result should be inferred from successful cross-compilation alone.
