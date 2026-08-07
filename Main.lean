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

  ON THE BENCHMARK. An earlier version reported "0 ms" for 100000 iterations.
  That was an artifact, not a result: the loop body called
  `pairs.filter (fun p => agreeUp ...)`, which does not depend on the loop
  variable, so the compiler hoisted it out and ran it once. The checksum gave
  it away — exactly `50012 * 100000`, i.e. one filter result added repeatedly.

  Two corrections. The accumulator now depends on the loop index, so nothing
  is loop-invariant and nothing hoists. And it calls `mulUpNative` directly
  rather than `agreeUp`, which had been measuring the COMPARISON of native
  against Lean rather than the native multiply itself.

  The iteration count is deliberately small. Scale it up only after seeing what
  one round costs.
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
  IO.println ""
  IO.println "-- native multiply, throughput --"
  let rounds := 10
  let start ← IO.monoMsNow
  let mut total : Int := 0
  for i in [0:rounds] do
    for p in pairs do
      total := total + (Fixed64Native.mulUpNative p.1 p.2).raw.toInt + i
  let finish ← IO.monoMsNow
  let ops := rounds * pairs.length
  IO.println s!"multiplies          : {ops}"
  IO.println s!"elapsed             : {finish - start} ms"
  IO.println s!"checksum            : {total}"
  IO.println "(a round checksum would mean the loop was hoisted; it should not be)"
  IO.println ""
  if okUp == pairs.length && okDown == pairs.length then
    IO.println "RESULT: native matches the verified implementation on all pairs."
  else
    IO.println "RESULT: DIVERGENCE. The C is wrong; the Lean side is proved."
    IO.Process.exit 1
