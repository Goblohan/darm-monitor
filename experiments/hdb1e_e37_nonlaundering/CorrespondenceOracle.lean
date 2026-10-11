import E38OperationalCore
open Lean

structure E38OracleVector where
  facts : List String
  obligations : List (List String)
  checks : List Bool
  deriving FromJson

def main : IO Unit := do
  let raw ← (← IO.getStdin).getLine
  let parsed := do
    let json ← Json.parse raw
    fromJson? json (α := List E38OracleVector)
  match parsed with
  | .error msg => throw (IO.userError msg)
  | .ok cases =>
    let answers := cases.map fun c =>
      DARM.E38.Operational.admitRel c.facts c.obligations c.checks
    (← IO.getStdout).putStrLn ((toJson answers).compress)
