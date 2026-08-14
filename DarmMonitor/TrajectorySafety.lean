import DarmMonitor.Basic

/-!
# DARM Finite-Trace Safety

Phase 1 lifts the existing single-step governance
invariants in `Basic.lean` to arbitrary finite traces
consisting entirely of agent-originated events.

This establishes compositional closure of the current
discrete governance invariants.

It does not yet establish adaptive-agent safety over
mixed transition classes, ratification, administrative
events, observations, or arbitrary adversarial traces.
Those are reserved for the subsequent trajectory-safety
development.
-/

namespace DARM

variable {CapId ActionId Token : Type}
  [DecidableEq CapId] [DecidableEq ActionId] [DecidableEq Token]

/-- A finite trace contains only agent-originated events. -/
def AgentTrace
    (es : List (Event CapId ActionId Token)) : Prop :=
  ∀ e ∈ es, actor e = Actor.agent
/-- Capability confinement survives an arbitrary finite agent trace. -/
theorem trace_preserves_capInvariant
    (requires : 
ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    (s : State CapId ActionId)
    (hCap : capInvariant allowedCapLimit s)
    (hAgent : AgentTrace es) :
    capInvariant allowedCapLimit
      (es.foldl (step requires allowedCapLimit validToken) s) := by
  induction es generalizing s with
  | nil =>
      exact hCap
  | cons e es ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact step_preserves_capInvariant
          requires allowedCapLimit validToken s e hCap
      · intro e' he'
        exact hAgent e' (by simp [he'])

/-- Policy cannot grow along an arbitrary finite agent trace. -/
theorem trace_policy_subset_initial
    (requires : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    (s : State CapId ActionId)
    (hAgent : AgentTrace es) :
    (es.foldl (step requires allowedCapLimit validToken) s).policy
      ⊆ s.policy := by
  exact policy_monotone_absorbing
    requires allowedCapLimit validToken es s hAgent

/-- Suspension remains absorbing across any finite agent trace. -/
theorem trace_suspended_absorbing
    (requires : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    (s : State CapId ActionId)
    (hSusp : s.opState = OpState.suspended)
    (hAgent : AgentTrace es) :
    (es.foldl (step requires allowedCapLimit validToken) s).opState
      = OpState.suspended := by
  exact suspended_absorbing
    requires allowedCapLimit validToken es s hSusp hAgent

end DARM

#print axioms DARM.trace_preserves_capInvariant
#print axioms DARM.trace_policy_subset_initial
#print axioms DARM.trace_suspended_absorbing