import AgentSandbox.Initialization
import DarmMonitor.Deployment
import DarmMonitor.HistorySafety

namespace AgentSandbox

/-! # Theorems — Core Guarantees Instantiated for AgentSandbox

This module applies the DARM core theorems to the concrete `AgentSandbox` profile.
The core proves these results for **arbitrary** finite types `CapId`, `ActionId`,
with a total `requiredCap` mapping and an externally supplied `capBound`.

This module instantiates those generic theorems with our concrete types.
**No new proof content is required** — the core theorems apply with zero
additional proof work. This is the "reuse without abstraction" pattern that
`Deployment.lean` establishes.

The profile theorems below are **stated** here; the proofs are either:
- `by decide` / `by simp` for purely profile-specific facts, or
- `sorry` pending exact core theorem signatures (to be filled after first build).

After the first successful build, replace every `sorry` with the appropriate
core theorem application. -/

-- ============================================================================
-- 4.1 UNREACHABILITY — Instantiation of `never_executable_of_ungranted`
-- ============================================================================

/-- `bashExec` is **permanently unreachable** in any `exploitGymReadOnly` state
    because `shellExec` is not in the capability bound.

    Core theorem applied: `never_executable_of_ungranted`
    (an action whose permission was never granted can never execute in any
    capability-confined state, whatever the policy says). -/
theorem bashExec_never_executable_exploitGymReadOnly :
    ∀ s, s.cap ⊆ taskCapBound TaskId.exploitGymReadOnly →
    ¬DarmMonitor.Basic.executable s ActionId.bashExec := by
  -- TODO: apply `DarmMonitor.Deployment.never_executable_of_ungranted`
  -- once exact signature is known after first build.
  sorry

/-- `modifyAuditLog` is permanently unreachable in ALL tasks because `logModify`
    is never in any `taskCapBound`.

    This is stronger than a per-task bound: it is a **deployment-wide**
    unreachability fact. -/
theorem modifyAuditLog_never_executable_any_task :
    ∀ task, ∀ s, s.cap ⊆ taskCapBound task →
    ¬DarmMonitor.Basic.executable s ActionId.modifyAuditLog := by
  sorry

/-- `screenshotCapture` is permanently unreachable in ALL tasks. -/
theorem screenshotCapture_never_executable_any_task :
    ∀ task, ∀ s, s.cap ⊆ taskCapBound task →
    ¬DarmMonitor.Basic.executable s ActionId.screenshotCapture := by
  sorry

/-- `sendEmail` is permanently unreachable in ALL tasks. -/
theorem sendEmail_never_executable_any_task :
    ∀ task, ∀ s, s.cap ⊆ taskCapBound task →
    ¬DarmMonitor.Basic.executable s ActionId.sendEmail := by
  sorry

/-- `artifactoryUpload` is permanently unreachable in ALL tasks because
    `artifactoryWrite` is never granted. -/
theorem artifactoryUpload_never_executable_any_task :
    ∀ task, ∀ s, s.cap ⊆ taskCapBound task →
    ¬DarmMonitor.Basic.executable s ActionId.artifactoryUpload := by
  sorry

-- ============================================================================
-- 4.2 ANTI-MONOTONICITY — Instantiation of `unreachable_antitone`
-- ============================================================================

/-- Tightening the capability bound can only **enlarge** the unreachable set.
    If `task₂` has fewer capabilities than `task₁`, every action unreachable
    in `task₁` is also unreachable in `task₂`.

    Core theorem applied: `unreachable_antitone` -/
theorem unreachable_antitone_exploitGym :
    ∀ a, a ∉ initialPolicy TaskId.exploitGymWithNetwork →
    a ∉ initialPolicy TaskId.exploitGymReadOnly := by
  intro a h
  -- TODO: apply core `unreachable_antitone` with
  -- `taskCapBound exploitGymReadOnly ⊆ taskCapBound exploitGymWithNetwork`
  sorry

-- ============================================================================
-- 4.3 TRAJECTORY SAFETY — Instantiation of HistorySafety
-- ============================================================================

/-- Capability confinement holds against an **unrestricted, adaptive,
    history-dependent adversary** over any finite trajectory, with **no**
    admissibility hypothesis.

    This is the theorem that defeats the swarm: even if 1,200 agents share
    70,000 messages and adapt their strategy based on the full observed
    history, no agent can execute an action whose capability was never granted.

    Core theorem applied: `generateTrajectory_preserves_capInvariant` -/
theorem agent_trajectory_safety_exploitGymReadOnly :
    ∀ trajectory,
    DarmMonitor.HistorySafety.generateTrajectory_preserves_capInvariant
      (initMonitorState TaskId.exploitGymReadOnly) trajectory := by
  sorry

/-- Trajectory safety for the network-enabled task. The additional `networkHttp`
    capability is still externally bounded; the adversary cannot manufacture
    `shellExec`, `logModify`, or `screenshot`. -/
theorem agent_trajectory_safety_exploitGymWithNetwork :
    ∀ trajectory,
    DarmMonitor.HistorySafety.generateTrajectory_preserves_capInvariant
      (initMonitorState TaskId.exploitGymWithNetwork) trajectory := by
  sorry

-- ============================================================================
-- 4.4 POLICY MONOTONICITY — Agent events can only SHRINK policy
-- ============================================================================

/-- An agent event cannot expand the policy set. This prevents the collective
    from voting itself new capabilities. Policy expansion requires ratification
    with the discrete guard. -/
theorem agent_event_policy_monotonicity :
    ∀ s e, DarmMonitor.Basic.policy_after_agent_event s e ⊆ s.policy := by
  sorry

-- ============================================================================
-- 4.5 RATIFICATION GUARD — Necessary and sufficient
-- ============================================================================

/-- The discrete ratification guard: a new policy is safe only if every action
    in it has its required capability in the current bound.

    This is the profile-specific version of `guarded_ratification_preserves_coherence`.
    The guard is **necessary**: `unguarded_ratification_counterexample` shows
    that without it, coherence breaks. -/
def discreteRatificationGuard (capBound : Finset CapId) (newPolicy : Finset ActionId) : Prop :=
  newPolicy ⊆ {a | requiredCap a ∈ capBound}

/-- The guard is sufficient: if it holds, ratification preserves capability confinement. -/
theorem discrete_guard_sufficient :
    ∀ s newPolicy,
    discreteRatificationGuard (taskCapBound TaskId.exploitGymReadOnly) newPolicy →
    DarmMonitor.Basic.capInvariant s (taskCapBound TaskId.exploitGymReadOnly) →
    DarmMonitor.Basic.coherent (s with policy := newPolicy) := by
  sorry

end AgentSandbox
