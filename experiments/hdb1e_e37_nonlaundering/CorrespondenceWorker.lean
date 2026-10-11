import E38OperationalCore
open Lean

/-! Experimental persistent oracle: same E38.Operational.admitRel definition as the
    single-shot conformance oracle. Lines carry an unpredictable correlation
    token; no security property is claimed for the transport outside the
    calling process or for the integrity of the Lean toolchain. -/

structure E38WorkerVector where
  facts : List String
  obligations : List (List String)
  checks : List Bool
  deriving FromJson

structure E38WorkerRequest where
  token : String
  cases : List E38WorkerVector
  deriving FromJson

def e38WorkerResponse (req : E38WorkerRequest) : Json :=
  Json.mkObj [
    ("token", toJson req.token),
    ("answers", toJson (req.cases.map fun c =>
      DARM.E38.Operational.admitRel c.facts c.obligations c.checks))
  ]

partial def e38WorkerServe (input output : IO.FS.Stream) : IO Unit := do
  let raw ← input.getLine
  if raw.isEmpty then
    return
  let parsed := do
    let value ← Json.parse raw
    fromJson? value (α := E38WorkerRequest)
  match parsed with
  | .error _ =>
    output.putStrLn ((Json.mkObj [("error", toJson ("invalid-request" : String))]).compress)
  | .ok req =>
    output.putStrLn ((e38WorkerResponse req).compress)
  output.flush
  e38WorkerServe input output

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  output.putStrLn ((Json.mkObj [("ready", toJson ("e38-lean-worker-v1" : String))]).compress)
  output.flush
  e38WorkerServe input output
