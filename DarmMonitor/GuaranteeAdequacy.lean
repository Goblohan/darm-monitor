import DarmMonitor.BehavioralAdequacy

/-
  DARM Boundary-Indexed Guarantee Adequacy

  v0.13.4

  This module distinguishes behavioral/observational adequacy from
  adequacy for a specific guarantee predicate.

  A representation is guarantee-adequate for a predicate P when
  representation equality preserves the truth of P.

  This is deliberately weaker than claiming that the representation
  captures all system behavior. It states only that the specified
  guarantee is well-defined on the representation classes.

  No claim is made that a particular guarantee is complete, sufficient,
  physically enforced, or semantically exhaustive.
-/

namespace DARM

/--
A guarantee predicate is representation-invariant when two states with
the same representation necessarily agree on whether the guarantee holds.
-/
def GuaranteeAdequate
    {State Representation : Type}
    (ρ : State → Representation)
    (P : State → Prop) : Prop :=
  ∀ s₁ s₂,
    RepresentationEq ρ s₁ s₂ →
    (P s₁ ↔ P s₂)

/--
Guarantee adequacy is exactly invariance of the guarantee predicate
over representation equivalence classes.
-/
theorem guaranteeAdequate_iff
    {State Representation : Type}
    (ρ : State → Representation)
    (P : State → Prop) :
    GuaranteeAdequate ρ P ↔
      ∀ s₁ s₂, ρ s₁ = ρ s₂ → (P s₁ ↔ P s₂) := by
  rfl

/--
A single pair of representation-equivalent states on which the guarantee
has different truth values refutes guarantee adequacy.
-/
theorem not_guaranteeAdequate_of_witness
    {State Representation : Type}
    {ρ : State → Representation}
    {P : State → Prop}
    {s₁ s₂ : State}
    (hRep : RepresentationEq ρ s₁ s₂)
    (hDiff : (P s₁ ∧ ¬ P s₂) ∨ (P s₂ ∧ ¬ P s₁)) :
    ¬ GuaranteeAdequate ρ P := by
  intro hAdequate
  have hIff := hAdequate s₁ s₂ hRep
  cases hDiff with
  | inl h =>
      exact h.2 (hIff.mp h.1)
  | inr h =>
      exact h.2 (hIff.mpr h.1)

/--
If a guarantee predicate is determined by a behavior observation,
and the representation is behaviorally adequate for that observation,
then the representation is adequate for the guarantee.

The factorization hypothesis is explicit. Behavioral adequacy alone
does not establish adequacy for an arbitrary guarantee.
-/
theorem guaranteeAdequate_of_behaviorallyAdequate
    {State Representation Behavior : Type}
    {ρ : State → Representation}
    {B : State → Behavior}
    {P : State → Prop}
    (hBehavior : BehaviorallyAdequate ρ B)
    (guaranteeFromBehavior : Behavior → Prop)
    (hFactor :
      ∀ s, P s ↔ guaranteeFromBehavior (B s)) :
    GuaranteeAdequate ρ P := by
  intro s₁ s₂ hRep
  rw [hFactor s₁, hFactor s₂]
  rw [hBehavior s₁ s₂ hRep]

/--
A guarantee adequate for a representation remains adequate after
post-composing its predicate with any proposition-valued function
through a behavior observation.
-/
theorem guaranteeAdequate_of_behavioralFactor
    {State Representation Behavior : Type}
    {ρ : State → Representation}
    {B : State → Behavior}
    (hBehavior : BehaviorallyAdequate ρ B)
    (Q : Behavior → Prop) :
    GuaranteeAdequate ρ (fun s => Q (B s)) := by
  exact guaranteeAdequate_of_behaviorallyAdequate
    hBehavior
    Q
    (fun _ => Iff.rfl)

end DARM

#print axioms DARM.guaranteeAdequate_iff
#print axioms DARM.not_guaranteeAdequate_of_witness
#print axioms DARM.guaranteeAdequate_of_behaviorallyAdequate
#print axioms DARM.guaranteeAdequate_of_behavioralFactor
