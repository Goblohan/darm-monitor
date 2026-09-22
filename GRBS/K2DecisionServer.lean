/-
  K2 — DARM DECISION SERVER

  Wraps the K1 kernel as an executable: one JSON request per line on
  stdin, one JSON decision per line on stdout. The decision itself is
  computed by K1's kernelDecide.

  Trusted computing base (NOT proved): Lean's JSON parser, the derived
  FromJson instances, this I/O loop, and the Lean compiler/runtime.

  Fail closed: malformed input yields {"decision":"reject",...}.
  Callers must treat anything other than {"decision":"admit"} as reject.
-/
import Lean
import K1DecisionKernel

open Lean

deriving instance FromJson for DARM.Kernel.Provenance
deriving instance FromJson for DARM.Kernel.Arg
deriving instance FromJson for DARM.Kernel.Invocation
deriving instance FromJson for DARM.Kernel.ArgRule
deriving instance FromJson for DARM.Kernel.ToolPolicy
deriving instance FromJson for DARM.Kernel.Policy
deriving instance FromJson for DARM.Kernel.Credential

structure KernelRequest where
  policy : DARM.Kernel.Policy
  credential : DARM.Kernel.Credential
  invocation : DARM.Kernel.Invocation
  deriving FromJson

def failureName : DARM.Kernel.Failure → String
  | .temporal => "temporal"
  | .observation => "observation"
  | .authority => "authority"
  | .semantic => "semantic"
  | .provenance => "provenance"

def decisionJson : DARM.Kernel.Decision → Json
  | .admit => Json.mkObj [("decision", Json.str "admit")]
  | .reject f => Json.mkObj [("decision", Json.str "reject"),
                             ("failure", Json.str (failureName f))]

def handleLine (line : String) : Json :=
  match (Json.parse line >>= fromJson? : Except String KernelRequest) with
  | .ok req =>
      decisionJson (DARM.Kernel.kernelDecide req.policy req.credential req.invocation)
  | .error e =>
      Json.mkObj [("decision", Json.str "reject"), ("error", Json.str e)]

partial def serveLoop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let t := line.trim
  unless t.isEmpty do
    stdout.putStrLn (handleLine t).compress
    stdout.flush
  serveLoop stdin stdout

def main : IO Unit := do
  serveLoop (← IO.getStdin) (← IO.getStdout)
