import R5AssuranceConservation
import R4dEvidenceCoverage

namespace GRBS.R4dCorrespondence

open GRBS.R4dEvidenceCoverage
open GRBS.R5AssuranceConservation

/-
  R4d is an epistemic instance of the R5 assurance-conservation pattern.

  Unlike R4a-R4c, the system-side execution domain remains fixed.

  The substitution changes evidentiary coverage.

      source domain = executions covered by E₂
      target domain = executions produced by the system

  The delta therefore consists of produced executions that E₂ does
  not cover.

      Delta(t) = produces(t) ∧ ¬ E₂.covers(t)

  The property imposed on that delta is evidentiary coverage itself.
-/

def R4dSourceDomain : Tr → Prop :=
  fun t => E₂.covers t

def R4dTargetDomain : Tr → Prop :=
  produces

def R4dProperty : Tr → Prop :=
  fun t => E₂.covers t

def R4dDeltaObligation : Prop :=
  DeltaObligation
    Tr
    R4dSourceDomain
    R4dTargetDomain
    R4dProperty

/--
  The R5 delta obligation is equivalent to the R4d
  evidence-substitution obligation.
-/
theorem r4d_delta_obligation_iff_evidence_obligation :
    R4dDeltaObligation ↔
      EvidenceSubstitutionObligation E₂ produces := by
  constructor
  · intro h t ht
    by_cases hc : E₂.covers t
    · exact hc
    · exact h t ⟨ht, hc⟩
  · intro h t hdelta
    exact h t hdelta.1

/--
  safeB is a produced execution outside E₂'s evidentiary coverage.
-/
theorem r4d_safeB_is_delta :
    Delta
      Tr
      R4dSourceDomain
      R4dTargetDomain
      Tr.safeB := by
  constructor
  · trivial
  · intro h
    exact Tr.noConfusion h

/--
  The R4d delta obligation fails because safeB is not covered.
-/
theorem r4d_delta_obligation_fails :
    ¬ R4dDeltaObligation := by
  intro h
  have hc : E₂.covers Tr.safeB := by
    exact h Tr.safeB ⟨trivial, fun h => Tr.noConfusion h⟩
  exact Tr.noConfusion hc

/--
  R4d therefore contains an undischarged R5 delta.
-/
theorem r4d_is_undischarged_r5_delta :
    Delta
      Tr
      R4dSourceDomain
      R4dTargetDomain
      Tr.safeB
    ∧ ¬ R4dDeltaObligation := by
  exact ⟨r4d_safeB_is_delta, r4d_delta_obligation_fails⟩

/--
  Preserve the original R4d result.
-/
theorem r4d_original_failure :
    Assured E₁ produces
    ∧ (∀ t, E₂.observes t → G t)
    ∧ ¬ Assured E₂ produces :=
  unsupported_evidence_substitution

/--
  R4d matches the R5 pattern while preserving the distinction
  between evidence truthfulness and evidence completeness.
-/
theorem r4d_matches_r5_pattern :
    Delta
      Tr
      R4dSourceDomain
      R4dTargetDomain
      Tr.safeB
    ∧ ¬ R4dDeltaObligation
    ∧ Assured E₁ produces
    ∧ (∀ t, E₂.observes t → G t)
    ∧ ¬ Assured E₂ produces := by
  exact ⟨
    r4d_safeB_is_delta,
    r4d_delta_obligation_fails,
    E1_assured,
    E2_truthful,
    E2_not_complete
  ⟩

/--
  The R4d failure is specifically a coverage failure.
  Truthfulness of E₂ does not discharge the R5 delta obligation.
-/
theorem r4d_truthfulness_does_not_discharge_delta :
    (∀ t, E₂.observes t → G t)
    ∧ ¬ R4dDeltaObligation := by
  exact ⟨E2_truthful, r4d_delta_obligation_fails⟩

end GRBS.R4dCorrespondence
