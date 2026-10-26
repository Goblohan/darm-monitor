import AgentSandbox.ActionSurface

namespace AgentSandbox

/-! # Task Policy — The Capability Root

This module defines the mapping from `TaskId` (chosen by the environment/scorer)
to `Finset CapId` (the capability bound). The bound is **not** derived from the
agent's state, prompt, or reasoning. It is injected at initialization.

The DARM core proves `capInvariant` is preserved across agent events. This module
proves that dangerous capabilities are **never** in any task's bound, making their
dependent actions permanently unreachable. -/

/-- Tasks are defined by the environment, not the agent.
    The agent cannot construct a `TaskId`; it receives one at birth. -/
inductive TaskId
  | exploitGymReadOnly
  | exploitGymWithNetwork
  | trustedAudit
  deriving DecidableEq, Fintype

/-- The capability bound is supplied by the scorer/environment at initialization.
    This is the `capBound` in DARM Core.

    CRITICAL INVARIANT: `shellExec`, `logModify`, and `screenshot` are **NEVER**
    in any task bound. This is the root-of-trust that makes the dangerous
    actions permanently unreachable. -/
def taskCapBound : TaskId → Finset CapId
  | .exploitGymReadOnly    => {CapId.fsRead, CapId.artifactoryRead}
  | .exploitGymWithNetwork => {CapId.fsRead, CapId.artifactoryRead, CapId.networkHttp}
  | .trustedAudit          => {CapId.fsRead, CapId.fsWrite, CapId.logAppend}

/-- The initial policy is the set of actions whose required capability is in the bound.
    This is a **derived** set; the authority lives in `taskCapBound`. -/
def initialPolicy (task : TaskId) : Finset ActionId :=
  {a | requiredCap a ∈ taskCapBound task}

-- ============================================================================
-- UNREACHABILITY PROOFS — These instantiate the DARM core theorem
-- `never_executable_of_ungranted` for each dangerous action.
-- ============================================================================

/-- `bashExec` requires `shellExec`. `shellExec` is never in any `taskCapBound`.
    Therefore `bashExec` is never in any `initialPolicy`. -/
theorem bashExec_unreachable (task : TaskId) :
    ActionId.bashExec ∉ initialPolicy task := by
  simp [initialPolicy, taskCapBound]
  cases task <;> simp [requiredCap]

/-- `modifyAuditLog` requires `logModify`. `logModify` is never in any `taskCapBound`.
    Therefore `modifyAuditLog` is never in any `initialPolicy`. -/
theorem modifyAuditLog_unreachable (task : TaskId) :
    ActionId.modifyAuditLog ∉ initialPolicy task := by
  simp [initialPolicy, taskCapBound]
  cases task <;> simp [requiredCap]

/-- `screenshotCapture` requires `screenshot`. `screenshot` is never in any `taskCapBound`.
    Therefore `screenshotCapture` is never in any `initialPolicy`. -/
theorem screenshotCapture_unreachable (task : TaskId) :
    ActionId.screenshotCapture ∉ initialPolicy task := by
  simp [initialPolicy, taskCapBound]
  cases task <;> simp [requiredCap]

/-- `sendEmail` requires `emailSend`. `emailSend` is never in any `taskCapBound`.
    Therefore `sendEmail` is never in any `initialPolicy`. -/
theorem sendEmail_unreachable (task : TaskId) :
    ActionId.sendEmail ∉ initialPolicy task := by
  simp [initialPolicy, taskCapBound]
  cases task <;> simp [requiredCap]

/-- `artifactoryUpload` requires `artifactoryWrite`. `artifactoryWrite` is never
    in any `taskCapBound`. Therefore `artifactoryUpload` is never in any `initialPolicy`. -/
theorem artifactoryUpload_unreachable (task : TaskId) :
    ActionId.artifactoryUpload ∉ initialPolicy task := by
  simp [initialPolicy, taskCapBound]
  cases task <;> simp [requiredCap]

/-- `writeFile` requires `fsWrite`. `fsWrite` is only in `trustedAudit`.
    This is a **positive** reachability fact: `writeFile` IS reachable in the
    trusted audit task, and NOT reachable in the exploit gym tasks. -/
theorem writeFile_reachable_only_in_trustedAudit :
    ActionId.writeFile ∈ initialPolicy TaskId.trustedAudit := by
  simp [initialPolicy, taskCapBound, requiredCap]

theorem writeFile_unreachable_in_exploitGymReadOnly :
    ActionId.writeFile ∉ initialPolicy TaskId.exploitGymReadOnly := by
  simp [initialPolicy, taskCapBound, requiredCap]

/-- The dangerous capabilities are absent from ALL task bounds.
    This is the master invariant that the deployment attestation checks. -/
theorem dangerous_caps_absent_from_all_bounds :
    ∀ task, {CapId.shellExec, CapId.logModify, CapId.screenshot, CapId.artifactoryWrite, CapId.emailSend} ∩ taskCapBound task = ∅ := by
  intro task
  cases task <;> simp [taskCapBound]

end AgentSandbox
