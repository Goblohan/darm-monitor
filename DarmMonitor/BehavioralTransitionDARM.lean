/-
  DARM Behavioral Transition Congruence
  Concrete instantiation

  v0.13.2

  This module instantiates the generic behavioral transition theory
  against the existing DARM reference-monitor transition relation.

  The first result establishes the trivial full-state representation.
  This is a calibration theorem, not a substantive claim about
  information sufficiency.
-/

import DarmMonitor.Basic
import DarmMonitor.BehavioralTransition

namespace DARM

variable {CapId ActionId Token : Type}
  [DecidableEq CapId]
  [DecidableEq ActionId]
  [DecidableEq Token]

/--
The identity representation preserves the complete DARM state.
-/
def identityRepresentation :
    State CapId ActionId → State CapId ActionId :=
  fun s => s


/--
Execution-relevant representation of a DARM state.

This representation retains the state components consulted by
`allowedActions` and omits `lastExecuted`.

It is introduced as a test object. No adequacy or congruence
claim is assumed.
-/
def executionRepresentation :
    State CapId ActionId →
      Finset CapId × Finset ActionId × OpState :=
  fun s => (s.cap, s.policy, s.opState)

/--
The complete DARM state representation is transition-congruent.
-/
theorem identityRepresentation_transitionCongruent
    (reqs : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken] :
    TransitionCongruent
      identityRepresentation
      (step reqs allowedCapLimit validToken) := by
  intro s₁ s₂ e hRep
  change s₁ = s₂ at hRep
  subst s₂
  rfl

/--
The complete DARM state representation preserves representation
equality across every finite event trace.
-/
theorem identityRepresentation_tracePreserved
    (reqs : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    {s₁ s₂ : State CapId ActionId}
    (hRep : RepresentationEq identityRepresentation s₁ s₂) :
    RepresentationEq identityRepresentation
      (es.foldl (step reqs allowedCapLimit validToken) s₁)
      (es.foldl (step reqs allowedCapLimit validToken) s₂) := by
  exact trace_representation_preserved
    (identityRepresentation_transitionCongruent
      reqs allowedCapLimit validToken)
    es hRep

#print axioms DARM.identityRepresentation_transitionCongruent
#print axioms DARM.identityRepresentation_tracePreserved

/--
The execution-relevant representation is transition-congruent for the
concrete DARM transition relation.

This theorem tests whether `lastExecuted`, which is omitted from the
representation, can affect the represented successor under `step`.
-/
theorem executionRepresentation_transitionCongruent
    (reqs : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken] :
    TransitionCongruent
      executionRepresentation
      (step reqs allowedCapLimit validToken) := by
  intro s₁ s₂ e hRep
  change
    (s₁.cap, s₁.policy, s₁.opState) =
      (s₂.cap, s₂.policy, s₂.opState) at hRep
  have hCap : s₁.cap = s₂.cap := congrArg Prod.fst hRep
  have hPolicy : s₁.policy = s₂.policy :=
    congrArg (fun x => x.2.1) hRep
  have hOpState : s₁.opState = s₂.opState :=
    congrArg (fun x => x.2.2) hRep
  change
    (
      (step reqs allowedCapLimit validToken s₁ e).cap,
      (step reqs allowedCapLimit validToken s₁ e).policy,
      (step reqs allowedCapLimit validToken s₁ e).opState
    ) =
    (
      (step reqs allowedCapLimit validToken s₂ e).cap,
      (step reqs allowedCapLimit validToken s₂ e).policy,
      (step reqs allowedCapLimit validToken s₂ e).opState
    )
  cases e with
  | autonomousPropose newPolicy =>
      by_cases h : newPolicy ⊆ s₂.policy
      · simp [step, h, hCap, hPolicy, hOpState]
      · simp [step, h, hCap, hPolicy, hOpState]
  | autonomousExpandCap c =>
      by_cases h : c ∈ allowedCapLimit
      · simp [step, h, hCap, hPolicy, hOpState]
      · simp [step, h, hCap, hPolicy, hOpState]
  | authenticatedRatification token newPolicy =>
      by_cases h : validToken token
      · simp [step, h, hCap, hPolicy, hOpState]
      · simp [step, h, hCap, hPolicy, hOpState]
  | externalSuspend =>
      simp [step, hCap, hPolicy, hOpState]
  | execute a =>
      have hAllowed :
          allowedActions reqs s₁ = allowedActions reqs s₂ := by
        simp [allowedActions, hCap, hPolicy, hOpState]
      have hCan :
          canExecute reqs s₁ a = canExecute reqs s₂ a := by
        simp [canExecute, hAllowed]
      by_cases h : canExecute reqs s₂ a
      · simp [step, h, hCan, hCap, hPolicy, hOpState]
      · simp [step, h, hCan, hCap, hPolicy, hOpState]


/--
The execution representation is preserved across every finite DARM event trace.

This is the concrete trace-level instantiation of the generic
representation-preservation theorem.
-/
theorem executionRepresentation_tracePreserved
    (reqs : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    {s₁ s₂ : State CapId ActionId}
    (hRep : RepresentationEq executionRepresentation s₁ s₂) :
    RepresentationEq executionRepresentation
      (es.foldl (step reqs allowedCapLimit validToken) s₁)
      (es.foldl (step reqs allowedCapLimit validToken) s₂) := by
  exact trace_representation_preserved
    (executionRepresentation_transitionCongruent
      reqs allowedCapLimit validToken)
    es
    hRep


/--
Guarantee-relevant authorization observation induced by the DARM
reference-monitor state.

This observation exposes the set of actions currently authorized by
the represented capability, policy, and operational state.
-/
def authorizationObservation
    (reqs : ActionId → CapId)
    (s : State CapId ActionId) : Finset ActionId :=
  allowedActions reqs s

/--
The execution representation is behaviorally adequate for the
authorization observation.

In other words, two states that are identical under the execution
representation cannot differ in their currently authorized actions.
-/
theorem executionRepresentation_behaviorallyAdequate_authorization
    (reqs : ActionId → CapId) :
    BehaviorallyAdequate
      executionRepresentation
      (authorizationObservation reqs) := by
  intro s₁ s₂ hRep
  change
    (s₁.cap, s₁.policy, s₁.opState) =
      (s₂.cap, s₂.policy, s₂.opState) at hRep
  have hCap : s₁.cap = s₂.cap := congrArg Prod.fst hRep
  have hPolicy : s₁.policy = s₂.policy :=
    congrArg (fun x => x.2.1) hRep
  have hOpState : s₁.opState = s₂.opState :=
    congrArg (fun x => x.2.2) hRep
  simp [authorizationObservation, allowedActions, hCap, hPolicy, hOpState]


/--
Authorization behavior remains equal after every common finite trace
when the initial states are equal under the execution representation.

This combines trace representation preservation with behavioral
adequacy of the representation for the authorization observation.
-/
theorem executionRepresentation_traceAuthorizationAdequacy
    (reqs : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    {s₁ s₂ : State CapId ActionId}
    (hRep : RepresentationEq executionRepresentation s₁ s₂) :
    authorizationObservation reqs
      (es.foldl (step reqs allowedCapLimit validToken) s₁) =
    authorizationObservation reqs
      (es.foldl (step reqs allowedCapLimit validToken) s₂) := by
  apply executionRepresentation_behaviorallyAdequate_authorization
  exact executionRepresentation_tracePreserved
    reqs allowedCapLimit validToken es hRep

end DARM


#print axioms DARM.executionRepresentation_transitionCongruent
#print axioms DARM.executionRepresentation_tracePreserved
#print axioms DARM.executionRepresentation_traceAuthorizationAdequacy
