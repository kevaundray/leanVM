import Lake
open Lake DSL

package «clean-spark-export» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require Clean from git "https://github.com/Verified-zkEVM/clean.git" @
  "1a6c28426372bb99af79e533aa7b9a0788eff0d7"

@[default_target]
lean_exe clean_export where
  root := `Main
