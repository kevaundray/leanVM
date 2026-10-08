use leanvm_mobile_bench::{
    AGGREGATE_BENCHMARK, AGGREGATION_LEAVES, AGGREGATION_LOG_INV_RATE, DEFAULT_ITERATIONS, DEFAULT_WARMUP,
    LEAF_LOG_INV_RATE, PROVE_BENCHMARK, SPENDS_PER_LEAF,
};
use mobench_sdk::{BenchSpec, MobenchBuf};
use serde_json::Value;
use std::error::Error;
use std::ffi::CStr;

fn run(name: &str) -> Result<Value, Box<dyn Error>> {
    let spec = BenchSpec::new(name, DEFAULT_ITERATIONS, DEFAULT_WARMUP)?;
    let input = serde_json::to_vec(&spec)?;
    let mut output = MobenchBuf::default();
    // SAFETY: the serialized input and writable output live through the synchronous call.
    let status =
        unsafe { leanvm_mobile_bench::mobench_run_benchmark_json(input.as_ptr(), input.len(), &raw mut output) };
    if status != 0 {
        // SAFETY: the SDK returns a live thread-local, nul-terminated error string.
        let error = unsafe { CStr::from_ptr(leanvm_mobile_bench::mobench_last_error_message()) };
        return Err(format!("{name}: {}", error.to_string_lossy()).into());
    }
    // SAFETY: a successful SDK call transfers one live byte buffer, freed once after parsing.
    let report = unsafe {
        let bytes = std::slice::from_raw_parts(output.ptr, output.len);
        let parsed = serde_json::from_slice::<Value>(bytes);
        leanvm_mobile_bench::mobench_free_buf(&raw mut output);
        parsed
    }?;
    assert_eq!(report["spec"]["name"], name);
    assert_eq!(
        report["samples"].as_array().expect("SDK samples").len(),
        DEFAULT_ITERATIONS as usize
    );
    let metrics = &report["custom_metrics"]["run_u64"];
    assert_eq!(metrics["threads"], std::thread::available_parallelism()?.get() as u64);
    assert_eq!(metrics["available_parallelism"], metrics["threads"]);
    assert_eq!(metrics["spends_per_leaf"], SPENDS_PER_LEAF as u64);
    assert_eq!(metrics["leaf_log_inv_rate"], u64::from(LEAF_LOG_INV_RATE));
    assert_eq!(
        metrics["verified_proofs"],
        u64::from(DEFAULT_WARMUP + DEFAULT_ITERATIONS)
    );
    if name == AGGREGATE_BENCHMARK {
        assert_eq!(metrics["aggregation_leaves"], AGGREGATION_LEAVES as u64);
        assert_eq!(metrics["aggregation_log_inv_rate"], u64::from(AGGREGATION_LOG_INV_RATE));
        assert_eq!(metrics["verified_leaves"], AGGREGATION_LEAVES as u64);
    } else {
        assert!(metrics.get("aggregation_leaves").is_none());
        assert!(metrics.get("aggregation_log_inv_rate").is_none());
        assert!(metrics.get("verified_leaves").is_none());
    }
    Ok(report)
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut names = mobench_sdk::registry::list_benchmark_names();
    names.sort_unstable();
    assert_eq!(names, [AGGREGATE_BENCHMARK, PROVE_BENCHMARK]);
    for pass in 1..=2 {
        for name in [PROVE_BENCHMARK, AGGREGATE_BENCHMARK] {
            let report = run(name)?;
            println!("{}", serde_json::json!({ "smoke_pass": pass, "report": report }));
        }
    }
    Ok(())
}
