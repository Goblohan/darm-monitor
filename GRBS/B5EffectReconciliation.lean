/-
  B5 — EFFECT-STATE RECONCILIATION

  B5 addresses the unresolved state left by B4.

  B4 proves that an effect has prior prepared evidence, but an
  UNKNOWN outcome does not by itself establish whether the governed
  target reached its intended state.

  B5 models reconciliation over an abstract observable target state.

  The reconciliation result is deliberately a STATE claim:

    observed = intended  -> confirmedSuccess
    observed = before    -> confirmedFailure
    otherwise             -> unresolved

  ConfirmedSuccess means that the intended target state is observed.
  It does NOT, by itself, establish that the broker caused the observed
  state transition.

  A stronger causal-attribution result requires additional assumptions,
  including an explicit no-independent-writer condition. That condition
  is not built into this first B5 model.

  Filesystem details such as SHA-256, inode identity, directory
  traversal, atomic replacement, and startup reconciliation belong to
  the implementation correspondence layer, not this abstract model.
-/

namespace DARM.EffectReconciliation

/-- Abstract observable state of the governed target. -/
inductive TargetState where
  | absent
  | present (value : Nat)
deriving DecidableEq, Repr

/-- State captured before the attempted effect and the state intended
    after the effect. -/
structure Receipt where
  before : TargetState
  intended : TargetState
deriving DecidableEq, Repr

/-- Result of reconciling a prepared receipt against an observed state. -/
inductive Reconciliation where
  | confirmedSuccess
  | confirmedFailure
  | unresolved
deriving DecidableEq, Repr

/-- Reconcile only from the recorded receipt and the observed target state. -/
def reconcile (r : Receipt) (observed : TargetState) : Reconciliation :=
  if observed = r.intended then
    Reconciliation.confirmedSuccess
  else if observed = r.before then
    Reconciliation.confirmedFailure
  else
    Reconciliation.unresolved

/-- An observed intended state is classified as confirmed success. -/
theorem intended_confirms_success (r : Receipt) :
    reconcile r r.intended = Reconciliation.confirmedSuccess := by
  simp [reconcile]

/-- An observed pre-state is classified as confirmed failure, provided
    the intended state differs from the pre-state. -/
theorem before_confirms_failure (r : Receipt)
    (h : r.before ≠ r.intended) :
    reconcile r r.before = Reconciliation.confirmedFailure := by
  simp [reconcile, h]

/-- An observation matching neither recorded state remains unresolved. -/
theorem neither_state_is_unresolved (r : Receipt) (observed : TargetState)
    (hBefore : observed ≠ r.before)
    (hIntended : observed ≠ r.intended) :
    reconcile r observed = Reconciliation.unresolved := by
  simp [reconcile, hIntended, hBefore]

/-- Confirmed success entails that the observed state is the intended state. -/
theorem confirmed_success_implies_intended (r : Receipt)
    (observed : TargetState)
    (h : reconcile r observed = Reconciliation.confirmedSuccess) :
    observed = r.intended := by
  unfold reconcile at h
  split at h
  · assumption
  · split at h
    · cases h
    · cases h

/-- Confirmed failure entails that the observed state is the recorded
    pre-state. -/
theorem confirmed_failure_implies_before (r : Receipt)
    (observed : TargetState)
    (h : reconcile r observed = Reconciliation.confirmedFailure) :
    observed = r.before := by
  unfold reconcile at h
  split at h
  · simp_all
  · split at h
    · assumption
    · simp_all

/-- The reconciliation result is exhaustive. -/
theorem reconciliation_exhaustive (r : Receipt) (observed : TargetState) :
    reconcile r observed = Reconciliation.confirmedSuccess ∨
    reconcile r observed = Reconciliation.confirmedFailure ∨
    reconcile r observed = Reconciliation.unresolved := by
  by_cases hi : observed = r.intended
  · left
    simp [reconcile, hi]
  · by_cases hb : observed = r.before
    · by_cases hbi : r.before = r.intended
      · left
        simp [reconcile, hb, hbi]
      · right
        left
        simp [reconcile, hb, hbi]
    · right
      right
      simp [reconcile, hi, hb]

/-- B5 deliberately establishes a state claim, not causal attribution:
    confirmed success is equivalent to observing the intended state. -/
theorem success_is_state_confirmation (r : Receipt) (observed : TargetState) :
    reconcile r observed = Reconciliation.confirmedSuccess ↔
    observed = r.intended := by
  constructor
  · exact confirmed_success_implies_intended r observed
  · intro h
    subst h
    exact intended_confirms_success r

end DARM.EffectReconciliation

#print axioms DARM.EffectReconciliation.intended_confirms_success
#print axioms DARM.EffectReconciliation.before_confirms_failure
#print axioms DARM.EffectReconciliation.neither_state_is_unresolved
#print axioms DARM.EffectReconciliation.confirmed_success_implies_intended
#print axioms DARM.EffectReconciliation.confirmed_failure_implies_before
#print axioms DARM.EffectReconciliation.reconciliation_exhaustive
#print axioms DARM.EffectReconciliation.success_is_state_confirmation
