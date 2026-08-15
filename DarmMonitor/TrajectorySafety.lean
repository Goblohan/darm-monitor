import DarmMonitor.Basic
import DarmMonitor.Deployment

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

/-- Capability confinement holds for every initial segment of a finite pure-agent trace. -/
theorem trace_prefixes_preserve_capInvariant
    (requires : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    (s : State CapId ActionId)
    (hCap : capInvariant allowedCapLimit s)
    (hAgent : AgentTrace es) :
    ∀ pre suf : List (Event CapId ActionId Token),
      es = pre ++ suf →
      capInvariant allowedCapLimit
        (pre.foldl (step requires allowedCapLimit validToken) s) := by
  intro pre suf hDecomp
  subst es
  exact trace_preserves_capInvariant
    requires allowedCapLimit validToken
    pre s hCap
    (by
      intro e he
      exact hAgent e (by simp [he]))

/-- Policy confinement holds for every initial segment of a finite pure-agent trace. -/
theorem trace_prefixes_policy_subset_initial
    (requires : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    (s : State CapId ActionId)
    (hAgent : AgentTrace es) :
    ∀ pre suf : List (Event CapId ActionId Token),
      es = pre ++ suf →
      (pre.foldl (step requires allowedCapLimit validToken) s).policy
        ⊆ s.policy := by
  intro pre suf hDecomp
  subst es
  exact trace_policy_subset_initial
    requires allowedCapLimit validToken
    pre s
    (by
      intro e he
      exact hAgent e (by simp [he]))

/-- Suspension remains absorbing at every initial segment of a finite pure-agent trace. -/
theorem trace_prefixes_suspended_absorbing
    (requires : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    (s : State CapId ActionId)
    (hSusp : s.opState = OpState.suspended)
    (hAgent : AgentTrace es) :
    ∀ pre suf : List (Event CapId ActionId Token),
      es = pre ++ suf →
      (pre.foldl (step requires allowedCapLimit validToken) s).opState
        = OpState.suspended := by
  intro pre suf hDecomp
  subst es
  exact trace_suspended_absorbing
    requires allowedCapLimit validToken
    pre s hSusp
    (by
      intro e he
      exact hAgent e (by simp [he]))

/-- Behavioral capability confinement holds at every prefix of a finite
    pure-agent trace: any action executable at that prefix requires a
    capability inside the externally imposed capability bound. -/
theorem trace_prefixes_execution_confined_by_cap_bound
    (requires : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    (s : State CapId ActionId)
    (hCap : capInvariant allowedCapLimit s)
    (hAgent : AgentTrace es) :
    ∀ pre suf : List (Event CapId ActionId Token),
      es = pre ++ suf →
      ∀ a : ActionId,
        canExecute requires
          (pre.foldl (step requires allowedCapLimit validToken) s) a →
        requires a ∈ allowedCapLimit := by
  intro pre suf hDecomp a hExec
  have hPrefixCap :
      capInvariant allowedCapLimit
        (pre.foldl (step requires allowedCapLimit validToken) s) := by
    exact trace_prefixes_preserve_capInvariant
      requires allowedCapLimit validToken
      es s hCap hAgent
      pre suf hDecomp
  exact execution_confined_by_cap_bound
    requires allowedCapLimit
    (pre.foldl (step requires allowedCapLimit validToken) s)
    a hPrefixCap hExec


/-- An action whose capability was never granted can never execute at any
    prefix of any finite pure-agent trace. The behavioural closure of
    `Deployment.never_executable_of_ungranted`: not merely that what executes
    is confined, but that an ungranted action is unreachable across the whole
    run, whatever agent-event sequence is taken. -/
theorem trace_prefixes_never_executable_of_ungranted
    (requires : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    (s : State CapId ActionId)
    (hCap : capInvariant allowedCapLimit s)
    (hAgent : AgentTrace es)
    (a : ActionId)
    (hUngranted : requires a ∉ allowedCapLimit) :
    ∀ pre suf : List (Event CapId ActionId Token),
      es = pre ++ suf →
      ¬ canExecute requires
          (pre.foldl (step requires allowedCapLimit validToken) s) a := by
  intro pre suf hDecomp
  have hPrefixCap :
      capInvariant allowedCapLimit
        (pre.foldl (step requires allowedCapLimit validToken) s) := by
    exact trace_prefixes_preserve_capInvariant
      requires allowedCapLimit validToken
      es s hCap hAgent
      pre suf hDecomp
  exact Deployment.never_executable_of_ungranted
    requires allowedCapLimit a hUngranted
    (pre.foldl (step requires allowedCapLimit validToken) s)
    hPrefixCap

end DARM

#print axioms DARM.trace_preserves_capInvariant
#print axioms DARM.trace_policy_subset_initial
#print axioms DARM.trace_suspended_absorbing
#print axioms DARM.trace_prefixes_preserve_capInvariant
#print axioms DARM.trace_prefixes_policy_subset_initial
#print axioms DARM.trace_prefixes_policy_subset_initial
#print axioms DARM.trace_prefixes_suspended_absorbing
#print axioms DARM.trace_prefixes_execution_confined_by_cap_bound
#print axioms DARM.trace_prefixes_never_executable_of_ungranted
