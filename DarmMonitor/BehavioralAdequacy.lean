/-
  DARM Behavioral Representation Adequacy

  v0.13

  PURPOSE

  This module formalizes the distinction between:

    * equality under an assurance representation, and
    * equality of guarantee-relevant behavior.

  The central question is:

    When does a representation preserve enough information for a
    guarantee to remain behaviorally well-defined?

  A representation is behaviorally adequate for a behavior observation
  when two states having the same representation necessarily have the
  same observed behavior.

  This module deliberately does NOT assume that:
    * the representation captures physical reality;
    * the behavior observation is complete;
    * the transition system is correctly implemented;
    * the representation is minimal;
    * the behavior observation is sufficient for every guarantee.

  Those are separate assurance obligations.

  The negative theorem is constructive in the logical sense:

    same representation
      +
    different observed behavior
      ->
    representation is not behaviorally adequate.

  This captures the formal core of the counterexamples developed in
  the DARM empirical laboratory v0.8-v0.12.
-/

namespace DARM

/-- Equality induced by an assurance representation. -/
def RepresentationEq
    {State Representation : Type}
    (ρ : State → Representation)
    (s₁ s₂ : State) : Prop :=
  ρ s₁ = ρ s₂

/--
Behavioral adequacy of a representation for an explicitly supplied
behavior observation.

The representation is adequate exactly when representation equality
forces equality of the behavior observation.
-/
def BehaviorallyAdequate
    {State Representation Behavior : Type}
    (ρ : State → Representation)
    (B : State → Behavior) : Prop :=
  ∀ s₁ s₂,
    RepresentationEq ρ s₁ s₂ →
    B s₁ = B s₂

/--
Equivalent formulation of behavioral adequacy using the representation
function directly.
-/
theorem behaviorallyAdequate_iff
    {State Representation Behavior : Type}
    (ρ : State → Representation)
    (B : State → Behavior) :
    BehaviorallyAdequate ρ B ↔
      ∀ s₁ s₂, ρ s₁ = ρ s₂ → B s₁ = B s₂ := by
  rfl

/--
Reflexivity of representation equality.
-/
theorem representationEq_refl
    {State Representation : Type}
    (ρ : State → Representation)
    (s : State) :
    RepresentationEq ρ s s := by
  rfl

/--
Symmetry of representation equality.
-/
theorem representationEq_symm
    {State Representation : Type}
    {ρ : State → Representation}
    {s₁ s₂ : State}
    (h : RepresentationEq ρ s₁ s₂) :
    RepresentationEq ρ s₂ s₁ := by
  exact h.symm

/--
Transitivity of representation equality.
-/
theorem representationEq_trans
    {State Representation : Type}
    {ρ : State → Representation}
    {s₁ s₂ s₃ : State}
    (h₁ : RepresentationEq ρ s₁ s₂)
    (h₂ : RepresentationEq ρ s₂ s₃) :
    RepresentationEq ρ s₁ s₃ := by
  exact h₁.trans h₂

/--
A behaviorally adequate representation makes behavior constant on
representation equivalence classes.
-/
theorem behavior_constant_on_representation_class
    {State Representation Behavior : Type}
    {ρ : State → Representation}
    {B : State → Behavior}
    (hAdequate : BehaviorallyAdequate ρ B)
    {s₁ s₂ : State}
    (hRep : RepresentationEq ρ s₁ s₂) :
    B s₁ = B s₂ := by
  exact hAdequate s₁ s₂ hRep

/--
A single same-representation/different-behavior witness refutes
behavioral adequacy.

This is the fundamental negative-result theorem for representation
adequacy.
-/
theorem not_behaviorallyAdequate_of_witness
    {State Representation Behavior : Type}
    {ρ : State → Representation}
    {B : State → Behavior}
    {s₁ s₂ : State}
    (hRep : RepresentationEq ρ s₁ s₂)
    (hBehavior : B s₁ ≠ B s₂) :
    ¬ BehaviorallyAdequate ρ B := by
  intro hAdequate
  exact hBehavior (hAdequate s₁ s₂ hRep)

/--
Behavioral adequacy is preserved when the behavior observation is
post-composed with any function.

An injectivity assumption is not required because equality of the
original behavior observation is sufficient to establish equality
after applying the function.
-/
theorem behaviorallyAdequate_postcomp
    {State Representation Behavior Behavior' : Type}
    {ρ : State → Representation}
    {B : State → Behavior}
    (f : Behavior → Behavior')
    (hAdequate : BehaviorallyAdequate ρ B) :
    BehaviorallyAdequate ρ (fun s => f (B s)) := by
  intro s₁ s₂ hRep
  exact congrArg f (hAdequate s₁ s₂ hRep)

/--
A richer representation can only preserve at least as much
representation information as a representation that it determines.

If ρ₁ can be recovered from ρ₂, then behavioral adequacy of ρ₁
implies behavioral adequacy of ρ₂.

This theorem is intentionally one-way. It does not claim that a
richer representation is necessary or minimal.
-/
theorem behaviorallyAdequate_of_refines
    {State R₁ R₂ Behavior : Type}
    {ρ₁ : State → R₁}
    {ρ₂ : State → R₂}
    {B : State → Behavior}
    (recover : R₂ → R₁)
    (hRecover : ∀ s, recover (ρ₂ s) = ρ₁ s)
    (hAdequate : BehaviorallyAdequate ρ₁ B) :
    BehaviorallyAdequate ρ₂ B := by
  intro s₁ s₂ hRep
  apply hAdequate s₁ s₂
  calc
    ρ₁ s₁ = recover (ρ₂ s₁) := by
      symm
      exact hRecover s₁
    _ = recover (ρ₂ s₂) := by rw [hRep]
    _ = ρ₁ s₂ := by
      exact hRecover s₂

end DARM

#print axioms DARM.behaviorallyAdequate_iff
#print axioms DARM.not_behaviorallyAdequate_of_witness
#print axioms DARM.behaviorallyAdequate_postcomp
#print axioms DARM.behaviorallyAdequate_of_refines
