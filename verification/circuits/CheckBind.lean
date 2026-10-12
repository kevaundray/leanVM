import LeanVMCircuits.Rec.Dump
import LeanVMCircuits.Rec.Bind

/-!
`lake exe checkbind <dump>...`: replay each dump's builder calls through the model and check transcript binding
(`LeanVMCircuits.Rec.Bind`): every test reading a challenge reads only wires some transcript binds. The verdict is
`Bind.Cert.accepts` of the certificate the analysis records, which `Bind.checkbind_sound` proves sound.

`--expect-unbound <dump>` checks a dump fails, the regression fixture of a circuit that did not bind.
-/

open LeanVMCircuits.Rec

def replay (path : System.FilePath) : IO (Option (Bind.Replay × Array String)) := do
  let text ← IO.FS.readFile path
  let (calls, _, _) ← match Dump.sections text with
    | .ok r => pure r
    | .error e => do IO.eprintln s!"{path}: {e}"; return none
  let mut rp : Bind.Replay := {}
  -- Each call's line, for messages: marks are lines but not calls.
  let mut callLines : Array String := #[]
  for line in calls do
    match Dump.parseLine line with
    | .ok (.call call) =>
      unless call.args.all (· < rp.state.next) && call.ok do
        IO.eprintln s!"{path}: a call names a wire not yet made or has the wrong size: {line}"; return none
      rp := rp.step call
      callLines := callLines.push line
    | .ok mark =>
      match rp.mark mark with
      | .ok r => rp := r
      | .error e => IO.eprintln s!"{path}: {e}"; return none
    | .error e => IO.eprintln s!"{path}: {e}"; return none
  if rp.pending.isSome then
    IO.eprintln s!"{path}: a marked block without its end"; return none
  return some (rp, callLines)

/-- Check one dump; `true` when it binds. -/
def check (path : System.FilePath) : IO (Option Bool) := do
  let some (rp, lines) ← replay path | return none
  let probe := ((← IO.getEnv "CHECKBIND_PROBE").getD "").splitOn "," |>.filterMap String.toNat?
  let r := Bind.analyse rp probe
  for (w, ts) in r.probes do
    IO.println s!"  probe {w} (made at call {rp.maker.getD w 0 + 1}): {repr ts}"
  let line := fun (i : ℕ) => s!"call {i + 1}: {(lines.getD i "").take 120}"
  IO.println s!"{path}: {if r.accepted then "accepted" else "rejected"}: {r.transcripts} transcripts, {r.squeezes} squeezes, {r.products} union products, \
    {r.tests} tests reading a challenge, \
    {r.unbound.size} unbound, {r.late.size} bound only after their latest challenge, \
    {r.deferred.size} bound only with the statement's claims; \
    {r.exposed} statement words read a challenge, {r.exposedUnbound.size} unbound; \
    {r.sumchecks} tests close a certified sumcheck ({r.rounds} rounds), \
    {r.powTests} are the bits of {r.pows} certified proof-of-work checks"
  for f in r.unbound.toList.take 10 do
    IO.println s!"  unbound test at {line f.call}, per transcript {repr f.perTranscript}"
    for h in f.hints.eraseDups do
      IO.println s!"    hinted at {line h}"
  for i in r.others do
    IO.println s!"  other eq_e test at {line i}"
  for f in r.deferred do
    IO.println s!"  test bound only with the statement at {line f.call}"
  for f in r.late.toList.take 5 do
    IO.println s!"  late test at {line f.call}: bound at call {f.hints.headD 0 + 1}, latest challenge at call \
      {f.hints.getD 1 0 + 1}"
  if r.accepted != r.unbound.isEmpty then
    IO.println s!"  the certificate's verdict differs from the worklist's"
  return some r.accepted

def main (args : List String) : IO UInt32 := do
  let mut ok := true
  let mut expectUnbound := false
  for a in args do
    if a = "--expect-unbound" then expectUnbound := true
    else
      match ← check a with
      | none => ok := false
      | some binds =>
        if binds = expectUnbound then
          IO.eprintln s!"{a}: expected {if expectUnbound then "an unbound test" else "every test bound"}"
          ok := false
      expectUnbound := false
  return if ok then 0 else 1
