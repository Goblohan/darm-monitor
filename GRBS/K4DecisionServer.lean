/-
  K4 DECISION SERVER (kernel-v0.2.0)

  Same protocol as K2, backed by the K4 role-aware kernel. A rule without
  a "payload" field is a selector (the strict default), so every K1-style
  request is decided exactly as K1 would decide it (k4_conservative_extension).

  Trusted computing base (NOT proved): Lean's JSON parser, the FromJson
  instances below, this I/O loop, and the Lean compiler/runtime.
  Fail closed: malformed input yields {"decision":"reject",...}.
-/
import Lean
import K4RoleKernel

open Lean

deriving instance FromJson for DARM.Kernel.Provenance
deriving instance FromJson for DARM.Kernel.Arg
deriving instance FromJson for DARM.Kernel.Invocation
deriving instance FromJson for DARM.Kernel.Credential

/-- A missing or non-boolean "payload" field means selector (strict default). -/
instance : FromJson DARM.Kernel4.RoleRule where
  fromJson? j := do
    let key ← j.getObjValAs? String "key"
    let allowedValues ← j.getObjValAs? (List String) "allowedValues"
    let allowedPrefixes ← j.getObjValAs? (List String) "allowedPrefixes"
    let payload := (j.getObjValAs? Bool "payload").toOption.getD false
    return { key, allowedValues, allowedPrefixes, payload }

deriving instance FromJson for DARM.Kernel4.ToolPolicy
deriving instance FromJson for DARM.Kernel4.Policy

structure KernelRequest4 where
  policy : DARM.Kernel4.Policy
  credential : DARM.Kernel.Credential
  invocation : DARM.Kernel.Invocation
  deriving FromJson

def failureName4 : DARM.Kernel.Failure → String
  | .temporal => "temporal"
  | .observation => "observation"
  | .authority => "authority"
  | .semantic => "semantic"
  | .provenance => "provenance"

def decisionJson4 : DARM.Kernel.Decision → Json
  | .admit => Json.mkObj [("decision", Json.str "admit")]
  | .reject f => Json.mkObj [("decision", Json.str "reject"),
                             ("failure", Json.str (failureName4 f))]

def handleLine4 (line : String) : Json :=
  match (Json.parse line >>= fromJson? : Except String KernelRequest4) with
  | .ok req =>
      decisionJson4 (DARM.Kernel4.kernelDecide req.policy req.credential req.invocation)
  | .error e =>
      Json.mkObj [("decision", Json.str "reject"), ("error", Json.str e)]

partial def serveLoop4 (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let t := line.trim
  unless t.isEmpty do
    stdout.putStrLn (handleLine4 t).compress
    stdout.flush
  serveLoop4 stdin stdout

def main : IO Unit := do
  serveLoop4 (← IO.getStdin) (← IO.getStdout)
