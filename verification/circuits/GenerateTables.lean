import LeanVMCircuits.ExtensionEmit

def main (args : List String) : IO Unit := do
  let [destination] := args | throw (IO.userError "usage: lake env lean --run GenerateTables.lean <destination.rs>")
  let generated ← match LeanVMCircuits.ExtensionProduct.Emit.emit with
    | .ok generated => pure generated
    | .error reason => throw (IO.userError reason)
  IO.FS.writeFile destination generated
  let format ← IO.Process.output {
    cmd := "rustfmt", args := #["--config-path", "../../rustfmt.toml", destination] }
  if format.exitCode != 0 then throw (IO.userError format.stderr)
