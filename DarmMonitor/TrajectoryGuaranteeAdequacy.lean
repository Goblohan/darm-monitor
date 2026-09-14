import DarmMonitor.GuaranteeAdequacy
import DarmMonitor.BehavioralTransition

namespace DARM

/-
  DARM Trajectory-Level Guarantee Adequacy

  v0.13.5

  A trajectory guarantee is a predicate over an initial state and
  an execution trace.

  This module distinguishes:

    1. representation adequacy for a trajectory observation
    2. semantic dependence of a guarantee on that observation
    3. resulting guarantee adequacy of the representation

  No claim is made that the chosen trace space is complete or that
  the guarantee captures all system-level safety properties.
-/

/--
A trajectory guarantee over an initial state and an execution trace.
-/
def TrajectoryGuarantee (State Event : Type) :=
  State → List Event → Prop

/--
A trajectory observation maps an initial state and trace to a
guarantee-relevant behavioral representation.
-/
def TrajectoryObservation (State Event Behavior : Type) :=
  State → List Event → Behavior

/--
A representation is adequate for a trajectory guarantee when
representation-equivalent initial states cannot disagree on the
guarantee for the same trace.
-/
def TrajectoryGuaranteeAdequate
    {State Representation Event : Type}
    (ρ : State → Representation)
    (G : TrajectoryGuarantee State Event) : Prop :=
  ∀ s₁ s₂ trace,
    RepresentationEq ρ s₁ s₂ →
    (G s₁ trace ↔ G s₂ trace)

/--
A trajectory guarantee is determined by an observation when the
guarantee factors through that observation.
-/
def TrajectoryGuaranteeFactorsThrough
    {State Event Behavior : Type}
    (B : TrajectoryObservation State Event Behavior)
    (G : TrajectoryGuarantee State Event)
    (Q : Behavior → Prop) : Prop :=
  ∀ s trace,
    G s trace ↔ Q (B s trace)

/--
Trajectory guarantee adequacy is exactly invariance of the guarantee
over representation-equivalence classes for every fixed trace.
-/
theorem trajectoryGuaranteeAdequate_iff
    {State Representation Event : Type}
    (ρ : State → Representation)
    (G : TrajectoryGuarantee State Event) :
    TrajectoryGuaranteeAdequate ρ G ↔
      ∀ s₁ s₂ trace,
        ρ s₁ = ρ s₂ →
        (G s₁ trace ↔ G s₂ trace) := by
  rfl

/--
A representation-equivalent pair of initial states with opposite
trajectory-guarantee truth values refutes trajectory guarantee
adequacy.
-/
theorem not_trajectoryGuaranteeAdequate_of_witness
    {State Representation Event : Type}
    {ρ : State → Representation}
    {G : TrajectoryGuarantee State Event}
    {s₁ s₂ : State}
    {trace : List Event}
    (hRep : RepresentationEq ρ s₁ s₂)
    (hDiff :
      (G s₁ trace ∧ ¬ G s₂ trace) ∨
      (G s₂ trace ∧ ¬ G s₁ trace)) :
    ¬ TrajectoryGuaranteeAdequate ρ G := by
  intro hAdequate
  have hIff := hAdequate s₁ s₂ trace hRep
  cases hDiff with
  | inl h =>
      exact h.2 (hIff.mp h.1)
  | inr h =>
      exact h.2 (hIff.mpr h.1)

/--
If a trajectory observation is representation-adequate and a
trajectory guarantee factors through that observation, then the
representation is adequate for the guarantee.

The factorization hypothesis is explicit. Behavioral adequacy for
one observation does not establish adequacy for an arbitrary
guarantee.
-/
theorem trajectoryGuaranteeAdequate_of_behaviorallyAdequate
    {State Representation Event Behavior : Type}
    {ρ : State → Representation}
    {B : TrajectoryObservation State Event Behavior}
    {G : TrajectoryGuarantee State Event}
    (hBehavior :
      ∀ s₁ s₂ trace,
        RepresentationEq ρ s₁ s₂ →
        B s₁ trace = B s₂ trace)
    (Q : Behavior → Prop)
    (hFactor :
      TrajectoryGuaranteeFactorsThrough B G Q) :
    TrajectoryGuaranteeAdequate ρ G := by
  intro s₁ s₂ trace hRep
  rw [hFactor s₁ trace, hFactor s₂ trace]
  rw [hBehavior s₁ s₂ trace hRep]


end DARM

#print axioms DARM.trajectoryGuaranteeAdequate_iff
#print axioms DARM.not_trajectoryGuaranteeAdequate_of_witness
#print axioms DARM.trajectoryGuaranteeAdequate_of_behaviorallyAdequate
