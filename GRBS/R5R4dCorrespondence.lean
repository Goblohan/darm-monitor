import R4dEvidenceCoverage
import DarmMonitor.R5BoundaryRepresentation

namespace GRBS.R5R4dCorrespondence

open GRBS.R4dEvidenceCoverage
open DARM

def r4dProperty : Tr → Prop :=
  G

def r4dEvidenceDomain : Tr → Prop :=
  E₂.covers

def r4dAssuranceDomain : Tr → Prop :=
  fun _ => True

def r4dCoverageDelta : Tr → Prop :=
  GRBS.R5DomainPolymorphism.Delta
    Tr
    r4dEvidenceDomain
    r4dAssuranceDomain

theorem r4d_coverage_gap_is_r5_delta :
    r4dCoverageDelta Tr.violation := by
  exact ⟨trivial, fun h => Tr.noConfusion h⟩

theorem r4d_coverage_gap_property_fails :
    ¬ r4dProperty Tr.violation := by
  exact fun h => h

theorem r4d_coverage_obligation_is_r5_delta_obligation :
    GRBS.R5DomainPolymorphism.DeltaObligation
      Tr
      r4dEvidenceDomain
      r4dAssuranceDomain
      r4dProperty ↔
      ∀ t : Tr,
        (r4dAssuranceDomain t →
         ¬ r4dEvidenceDomain t →
         r4dProperty t) := by
  constructor
  · intro hR5 t htTarget htNotSource
    exact hR5 t ⟨htTarget, htNotSource⟩
  · intro hCoverage t hDelta
    exact hCoverage t hDelta.1 hDelta.2

theorem r4d_coverage_obligation_is_undischarged :
    ¬ GRBS.R5DomainPolymorphism.DeltaObligation
      Tr
      r4dEvidenceDomain
      r4dAssuranceDomain
      r4dProperty := by
  intro hR5
  exact
    r4d_coverage_gap_property_fails
      (hR5 Tr.violation r4d_coverage_gap_is_r5_delta)

end GRBS.R5R4dCorrespondence

#print axioms GRBS.R5R4dCorrespondence.r4d_coverage_gap_is_r5_delta
#print axioms GRBS.R5R4dCorrespondence.r4d_coverage_gap_property_fails
#print axioms GRBS.R5R4dCorrespondence.r4d_coverage_obligation_is_r5_delta_obligation
#print axioms GRBS.R5R4dCorrespondence.r4d_coverage_obligation_is_undischarged
