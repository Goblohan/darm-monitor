import DarmMonitor.Basic
import DarmMonitor.Ratification
import DarmMonitor.StratumComposition

/-!
# DARM History-Dependent Safety

This module introduces an explicit observation history and an unrestricted
history-dependent event policy. The policy may be adversarial; safety is
obtained only from the authorization predicate on selected transitions.
-/

namespace DARM.HistorySafety

open DARM.Boundary
open DARM.Composition

/-- The information exposed to a history-dependent policy. -/
structure Observation (ActionId : Type) where
  opState : OpState
  visiblePolicy : Finset ActionId

/-- The observation exposed by the current governance state. -/
def observe {CapId ActionId : Type}
    (s : State CapId ActionId) : Observation ActionId :=
  { opState := s.opState
    visiblePolicy := s.policy }

/-- An observation history. -/
def History (ActionId : Type) := List (Observation ActionId)

/-- An unrestricted history-dependent event-selection policy. -/
def HistoryPolicy (CapId ActionId Token : Type) :=
  History ActionId → Event CapId ActionId Token

/-- The explicit guard required for a ratification event to preserve coherence.
    Non-ratification events are not classified by this predicate yet. -/
def guardedRatificationEvent
    {n : ℕ} {CapId Token : Type}
    (δ : ℝ) (w : Fin n → ℝ)
    (e : Event CapId (Fin n) Token) : Prop :=
  match e with
  | .authenticatedRatification _ p => p ⊆ active δ w
  | _ => True

/-- The unrestricted ratification boundary has a concrete counterexample. -/
theorem unguarded_ratification_counterexample :
    ∃ (s : State Unit (Fin 1)) (δ : ℝ) (w : Fin 1 → ℝ)
      (t : Unit) (p : Finset (Fin 1)),
      IsCoherent s δ w ∧
      ¬ IsCoherent
          (step (fun _ : Fin 1 => ()) (∅ : Finset Unit)
            (fun _ : Unit => True) s
            (Event.authenticatedRatification t p)) δ w := by
  exact DARM.Ratification.ratification_breaks_coherence

/-- The guarded ratification transition preserves coherence. -/
theorem guarded_ratification_step_preserves_coherence
    {n : ℕ} {CapId Token : Type}
    [DecidableEq CapId] [DecidableEq Token]
    (requires : Fin n → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop) [DecidablePred validToken]
    (s : State CapId (Fin n)) (t : Token) (p : Finset (Fin n))
    (δ : ℝ) (w : Fin n → ℝ)
    (hcoh : IsCoherent s δ w)
    (hguard : p ⊆ active δ w) :
    IsCoherent
      (step requires allowedCapLimit validToken s
        (Event.authenticatedRatification t p)) δ w := by
  exact DARM.Ratification.guarded_ratification_preserves_coherence
    requires allowedCapLimit validToken s t p δ w hcoh hguard

end DARM.HistorySafety

#print axioms DARM.HistorySafety.unguarded_ratification_counterexample
#print axioms DARM.HistorySafety.guarded_ratification_step_preserves_coherence
