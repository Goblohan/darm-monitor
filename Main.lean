import DarmMonitor
import DarmMonitor.Fixed64Native

/-
  Main — the demo executable.

  Runs two things a compiled binary can show that the interpreter cannot:

  1. The discrete monitor, executing. `bash_canRun_false` is a theorem about
     this code, not about a paper object.

  2. Differential tests from `Fixed64Native`, comparing the native C widening
     multiply against the verified Lean implementation.

  A failing differential test means the C implementation diverges from the
  verified Lean implementation.
-/

open DARM

def main : IO Unit := do
  IO.println "=== DARM demo ==="
  IO.println "-- discrete monitor --"
  IO.println "grant: fsRead, network"

  for line in Runtime.report Runtime.initialState do
    IO.println line

  IO.println ""
  IO.println "-- native multiply, differential tests --"

  let pairs := Fixed64Native.largeTestPairs

  let okUp :=
    (pairs.filter (fun p => DARM.Fixed64Native.agreeUp p.1 p.2)).length

  let okDown :=
    (pairs.filter (fun p => DARM.Fixed64Native.agreeDown p.1 p.2)).length

  IO.println s!"pairs tested        : {pairs.length}"
  IO.println s!"mulUp   agreements  : {okUp}"
  IO.println s!"mulDown agreements  : {okDown}"

  let start ← IO.monoMsNow

  let mut total := 0
  for _ in [0:100000] do
    total := total +
      (pairs.filter (fun p => DARM.Fixed64Native.agreeUp p.1 p.2)).length

  let finish ← IO.monoMsNow

  IO.println s!"benchmark (100000 × {pairs.length} pairs): {finish - start} ms"
  IO.println s!"benchmark checksum: {total}"

  if okUp == pairs.length && okDown == pairs.length then
    IO.println "RESULT: native matches the verified implementation on all pairs."
  else
    IO.println "RESULT: DIVERGENCE. The C is wrong; the Lean side is proved."
    IO.Process.exit 1