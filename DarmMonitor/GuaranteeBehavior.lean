import DarmMonitor.BehavioralTransitionDARM

/-!
  DARM Guarantee-Relevant Behavioral Observation

  v0.13.3

  This module instantiates the generic behavioral-adequacy machinery
  with the existing DARM execution semantics.

  The observation is the set of actions currently executable under
  the DARM policy, capability, and operational state.

  The bounded future observation is obtained by evaluating that same
  observation after each trace in a supplied finite trace family.

  This module does not claim that execution authorization is a complete
  semantic model of deployment behavior. It formalizes only the stated
  observation.
-/

namespace DARM

variable {CapId ActionId Token : Type}
  [DecidableEq CapId]
  [DecidableEq ActionId]
  [DecidableEq Token]

/-- Guarantee-relevant execution observation.

    This is intentionally independent of the representation being tested.
    It observes which actions are currently executable according to the
    existing DARM kernel semantics. -/
def executionGuaranteeObservation
    (reqs : ActionId → CapId)
    (s : State CapId ActionId) : Finset ActionId :=
  allowedActions reqs s

/-- A bounded family of execution observations.

    Each supplied event trace is evaluated from the same initial state,
    and the resulting executable-action set is recorded. -/
def boundedExecutionBehavior
    (reqs : ActionId → CapId)
    (stepFn : State CapId ActionId →
      Event CapId ActionId Token →
      State CapId ActionId)
    (traces : List (List (Event CapId ActionId Token)))
    (s : State CapId ActionId) : List (Finset ActionId) :=
  boundedTraceBehavior
    (fun s => s)
    stepFn
    (executionGuaranteeObservation reqs)
    traces
    s

/-- The execution representation is behaviorally adequate for the
    current execution authorization observation. -/
theorem executionRepresentation_guaranteeObservation_adequate
    (reqs : ActionId → CapId) :
    BehaviorallyAdequate
      executionRepresentation
      (executionGuaranteeObservation reqs) := by
  exact executionRepresentation_behaviorallyAdequate_authorization reqs

/-- The execution representation preserves its representation class
    under every DARM transition. -/
theorem executionRepresentation_step_congruent
    (reqs : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken] :
    TransitionCongruent
      executionRepresentation
      (step reqs allowedCapLimit validToken) := by
  exact executionRepresentation_transitionCongruent
    reqs allowedCapLimit validToken

/-- The execution representation is behaviorally adequate for every
    supplied bounded family of future execution observations. -/
theorem executionRepresentation_boundedGuaranteeBehavior_adequate
    (reqs : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (traces : List (List (Event CapId ActionId Token))) :
    BehaviorallyAdequate
      executionRepresentation
      (boundedExecutionBehavior
        reqs
        (step reqs allowedCapLimit validToken)
        traces) := by
  exact behaviorallyAdequate_boundedTraceBehavior
    traces
    (executionRepresentation_guaranteeObservation_adequate reqs)
    (executionRepresentation_step_congruent
      reqs allowedCapLimit validToken)

end DARM

#print axioms DARM.executionRepresentation_guaranteeObservation_adequate
#print axioms DARM.executionRepresentation_step_congruent
#print axioms DARM.executionRepresentation_boundedGuaranteeBehavior_adequate
