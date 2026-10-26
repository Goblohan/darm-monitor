import AgentSandbox.FFI
import AgentSandbox.Adapter

namespace AgentSandbox.Demo

/-! # Demo — AgentSandbox Profile Decision Table

This executable prints the ALLOW/BLOCK/UNKNOWN decision table for every
combination of task and action. It verifies that the dangerous actions
are blocked in all tasks.

Run with: `lake exe agentsandbox_demo`

Expected output:
```
=== AgentSandbox Profile Decision Table ===
Task: exploitGymReadOnly
  readFile          → ALLOWED
  writeFile         → BLOCKED
  artifactoryFetch  → ALLOWED
  artifactoryUpload → BLOCKED
  ...
Task: exploitGymWithNetwork
  ...
Task: trustedAudit
  ...

=== DANGEROUS ACTIONS (must be BLOCKED in ALL tasks) ===
  bashExec          → BLOCKED ✓
  modifyAuditLog    → BLOCKED ✓
  screenshotCapture → BLOCKED ✓
  sendEmail         → BLOCKED ✓
  artifactoryUpload → BLOCKED ✓
```
-/

def actionName : ActionId → String
  | .readFile          => "readFile         "
  | .writeFile         => "writeFile        "
  | .artifactoryFetch  => "artifactoryFetch "
  | .artifactoryUpload => "artifactoryUpload"
  | .artifactoryList   => "artifactoryList  "
  | .screenshotCapture => "screenshotCapture"
  | .httpGet           => "httpGet          "
  | .bashExec          => "bashExec         "
  | .sendEmail         => "sendEmail        "
  | .appendAuditLog    => "appendAuditLog   "
  | .modifyAuditLog    => "modifyAuditLog   "

def taskName : TaskId → String
  | .exploitGymReadOnly    => "exploitGymReadOnly   "
  | .exploitGymWithNetwork => "exploitGymWithNetwork"
  | .trustedAudit          => "trustedAudit         "

def decisionString : Adapter.EnforcementDecision → String
  | .allow   => "ALLOWED"
  | .block   => "BLOCKED"
  | .unknown => "UNKNOWN_BLOCKED"

/-- Test every action against every task and print the decision. -/
def printDecisionTable : IO Unit := do
  IO.println "========================================"
  IO.println "AgentSandbox Profile Decision Table"
  IO.println "========================================"
  IO.println ""

  for task in [TaskId.exploitGymReadOnly, TaskId.exploitGymWithNetwork, TaskId.trustedAudit] do
    IO.println s!"Task: {taskName task}"
    let state := initMonitorState task
    for action in (Finset.univ : Finset ActionId) do
      let req := Adapter.RawRequest.mk "GET" "/test" []
      -- We need to construct a request that classifies to this action.
      -- For the demo, we bypass classification and test the action directly
      -- by constructing a synthetic request.
      let syntheticReq := match action with
        | .readFile          => ⟨"GET",    "/file",        []⟩
        | .writeFile         => ⟨"POST",   "/file",        []⟩
        | .artifactoryFetch  => ⟨"GET",    "/artifactory", []⟩
        | .artifactoryUpload => ⟨"POST",   "/artifactory", []⟩
        | .artifactoryList   => ⟨"LIST",   "/artifactory", []⟩
        | .screenshotCapture => ⟨"CAPTURE","/screen",      []⟩
        | .httpGet           => ⟨"GET",    "/http",        []⟩
        | .bashExec          => ⟨"EXEC",   "/shell",       []⟩
        | .sendEmail         => ⟨"POST",   "/email",       []⟩
        | .appendAuditLog    => ⟨"APPEND", "/audit",       []⟩
        | .modifyAuditLog    => ⟨"MODIFY", "/audit",       []⟩
      let dec := Adapter.decide syntheticReq state
      IO.println s!"  {actionName action} → {decisionString dec}"
    IO.println ""

  IO.println "========================================"
  IO.println "DANGEROUS ACTIONS (must be BLOCKED in ALL tasks)"
  IO.println "========================================"
  IO.println ""

  let dangerous := [ActionId.bashExec, ActionId.modifyAuditLog, ActionId.screenshotCapture, ActionId.sendEmail, ActionId.artifactoryUpload]
  for action in dangerous do
    let allBlocked := [TaskId.exploitGymReadOnly, TaskId.exploitGymWithNetwork, TaskId.trustedAudit].all (fun task =>
      let state := initMonitorState task
      let syntheticReq := match action with
        | .bashExec          => ⟨"EXEC",   "/shell",       []⟩
        | .modifyAuditLog    => ⟨"MODIFY", "/audit",       []⟩
        | .screenshotCapture => ⟨"CAPTURE","/screen",      []⟩
        | .sendEmail         => ⟨"POST",   "/email",       []⟩
        | .artifactoryUpload => ⟨"POST",   "/artifactory", []⟩
        | _                  => ⟨"GET",    "/file",        []⟩
      let dec := Adapter.decide syntheticReq state
      dec == .block || dec == .unknown)
    let status := if allBlocked then "✓ BLOCKED in all tasks" else "✗ ALLOWED in some task — FAILURE"
    IO.println s!"  {actionName action} → {status}"

  IO.println ""
  IO.println "========================================"
  IO.println "Demo Complete"
  IO.println "========================================"

def main : IO Unit := do
  printDecisionTable

end AgentSandbox.Demo
