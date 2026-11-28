//! Helpers shared by the integration tests, reached as `crate::common::…`.

/// `tests/compiled/<name>.txt`: a program as the Lean back end compiled it (`lake exe guest-backend export programs`).
pub fn compiled(name: &str) -> isa::Program {
    let path = format!("{}/tests/compiled/{name}.txt", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    isa::Program::__from_text(&text).unwrap_or_else(|e| panic!("{path}: {e}"))
}
