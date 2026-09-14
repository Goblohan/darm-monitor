import R5AssuranceConservation
import R4cLocusSubstitution

namespace GRBS.R4cCorrespondence

open GRBS.R4cLocusSubstitution
open GRBS.R5AssuranceConservation

/-
  R4c is an instance of the R5 assurance-conservation pattern.

  The transformation is a substitution of enforcement locus:

      Locus.mediating -> Locus.observing

  The R5 delta is the set of traces newly passable at the target
  locus but not passable at the source locus.

  The transfer property is the original guarantee G.
-/

def R4cSourceDomain : Tr → Prop :=
  fun t => tracesAtLocus Locus.mediating t

def R4cTargetDomain : Tr → Prop :=
  fun t => tracesAtLocus Locus.observing t

def R4cProperty : Tr → Prop :=
  G

def R4cDeltaObligation : Prop :=
  DeltaObligation Tr R4cSourceDomain R4cTargetDomain R4cProperty

/--
  The generic R5 delta obligation is equivalent to the
  locus-substitution obligation discovered independently in R4c.
-/
theorem r4c_delta_obligation_iff_locus_obligation :
    R4cDeltaObligation ↔
      LocusSubstitutionObligation
        G Locus.mediating Locus.observing tracesAtLocus := by
  constructor
  · intro h t ht2 hnot1
    exact h t ⟨ht2, hnot1⟩
  · intro h t hdelta
    exact h t hdelta.1 hdelta.2

/--
  The violation trace is newly passable at the observing locus.
-/
theorem r4c_violation_is_delta :
    Delta
      Tr
      R4cSourceDomain
      R4cTargetDomain
      Tr.violation := by
  constructor
  · trivial
  · intro h
    exact Tr.noConfusion h

/--
  The R4c delta obligation is not dischargeable in the constructed
  witness because the newly passable violation does not satisfy G.
-/
theorem r4c_delta_obligation_fails :
    ¬ R4cDeltaObligation := by
  intro h
  exact h Tr.violation
    ⟨trivial, fun h => Tr.noConfusion h⟩

/--
  R4c therefore contains an undischarged R5 delta.
-/
theorem r4c_is_undischarged_r5_delta :
    Delta
      Tr
      R4cSourceDomain
      R4cTargetDomain
      Tr.violation
    ∧ ¬ R4cDeltaObligation := by
  exact ⟨r4c_violation_is_delta, r4c_delta_obligation_fails⟩

/--
  Preserve the original R4c failure result.
-/
theorem r4c_original_failure :
    SafeAtLocus G Locus.mediating tracesAtLocus
    ∧ Locus.mediating ≠ Locus.observing
    ∧ ¬ SafeAtLocus G Locus.observing tracesAtLocus
    ∧ ¬ LocusSubstitutionObligation
        G Locus.mediating Locus.observing tracesAtLocus :=
  unsupported_locus_substitution

/--
  R4c matches the R5 pattern.
-/
theorem r4c_matches_r5_pattern :
    Delta
      Tr
      R4cSourceDomain
      R4cTargetDomain
      Tr.violation
    ∧ ¬ R4cDeltaObligation
    ∧ SafeAtLocus G Locus.mediating tracesAtLocus
    ∧ Locus.mediating ≠ Locus.observing
    ∧ ¬ SafeAtLocus G Locus.observing tracesAtLocus
    ∧ ¬ LocusSubstitutionObligation
        G Locus.mediating Locus.observing tracesAtLocus := by
  exact ⟨
    r4c_violation_is_delta,
    r4c_delta_obligation_fails,
    safe_at_mediating,
    locus_differs,
    not_safe_at_observing,
    obligation_not_dischargeable
  ⟩

end GRBS.R4cCorrespondence
