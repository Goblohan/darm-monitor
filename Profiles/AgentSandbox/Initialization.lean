import AgentSandbox.TaskPolicy
import DarmMonitor.Runtime

namespace AgentSandbox

/-! # Initialization — From Task to MonitorState

This module defines the `MonitorState` factory and proves that the initialized
state satisfies the DARM core invariants (`capInvariant`, `policy` derived from
`cap`, etc.).

The DARM core `Runtime.lean` proves `canRun_iff_canExecute`: the extracted
`Bool` matches the proved `Prop`. This module bridges the profile-specific
initialization to that runtime contract. -/

/-- Monitor state for the AgentSandbox profile.
    Mirrors the core `MonitorState` but with concrete `AgentSandbox` types.

    Fields:
    - `cap`: the current capability set (subset of environment-supplied bound)
    - `policy`: the current permitted actions (derived from `cap` via `requiredCap`)
    - `opState`: e.g. remaining compute budget (environment-controlled)
    - `suspended`: absorbing state (agent events cannot exit) -/
structure MonitorState where
  cap       : Finset CapId
  policy    : Finset ActionId
  opState   : Nat
  suspended : Bool

/-- Factory: create a `MonitorState` from a `TaskId`.
    The environment calls this; the agent does not construct its own state. -/
def initMonitorState (task : TaskId) : MonitorState where
  cap       := taskCapBound task
  policy    := initialPolicy task
  opState   := 1000000  -- compute budget, environment-controlled
  suspended := false

/-- The environment-supplied bound is preserved at initialization.
    This is the base case for `capInvariant` preservation across trajectories. -/
theorem init_capInvariant (task : TaskId) :
    (initMonitorState task).cap ⊆ taskCapBound task := by
  simp [initMonitorState]

/-- The initial policy is exactly the `initialPolicy` for the task.
    This connects the profile definition to the runtime state. -/
theorem init_policy_eq (task : TaskId) :
    (initMonitorState task).policy = initialPolicy task := by
  simp [initMonitorState]

/-- Suspension starts false. Only ratification or environment events can change it.
    Agent events cannot unsuspend (absorbing state, proved in DARM core). -/
theorem init_not_suspended (task : TaskId) :
    (initMonitorState task).suspended = false := by
  simp [initMonitorState]

/-- Compute budget is environment-supplied. The agent cannot increase it.
    This is the discrete analogue of "life = compute" from the incident reports,
    but here it is an externally bounded resource, not a belief. -/
theorem init_opState_env_supplied (task : TaskId) :
    (initMonitorState task).opState = 1000000 := by
  simp [initMonitorState]

end AgentSandbox
