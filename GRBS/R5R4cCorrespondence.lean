import R4cLocusSubstitution
import DarmMonitor.R5BoundaryRepresentation

namespace GRBS.R5R4cCorrespondence

open GRBS.R4cLocusSubstitution
open DARM

def r4cProperty : Tr → Prop :=
  G

def r4cSourceDomain : Tr → Prop :=
  tracesAtLocus Locus.mediating

def r4cTargetDomain : Tr → Prop :=
  tracesAtLocus Locus.observing

theorem r4c_locus_obligation_iff_r5_delta_obligation :
    LocusSubstitutionObligation
      G
      Locus.mediating
      Locus.observing
      tracesAtLocus ↔
      GRBS.R5DomainPolymorphism.DeltaObligation
        Tr
        r4cSourceDomain
        r4cTargetDomain
        r4cProperty := by
  constructor
  · intro hR4c t hDelta
    exact hR4c t hDelta.1 hDelta.2
  · intro hR5 t htTarget htNotSource
    exact hR5 t ⟨htTarget, htNotSource⟩

theorem r4c_violation_is_r5_delta_witness :
    GRBS.R5DomainPolymorphism.Delta
      Tr
      r4cSourceDomain
      r4cTargetDomain
      Tr.violation := by
  exact ⟨trivial, fun h => Tr.noConfusion h⟩

theorem r4c_violation_property_fails :
    ¬ r4cProperty Tr.violation := by
  exact fun h => h

theorem r4c_is_undischarged_r5_delta :
    ¬ GRBS.R5DomainPolymorphism.DeltaObligation
      Tr
      r4cSourceDomain
      r4cTargetDomain
      r4cProperty := by
  intro hR5
  exact
    obligation_not_dischargeable
      (fun t htTarget htNotSource =>
        hR5 t ⟨htTarget, htNotSource⟩)

end GRBS.R5R4cCorrespondence

#print axioms GRBS.R5R4cCorrespondence.r4c_locus_obligation_iff_r5_delta_obligation
#print axioms GRBS.R5R4cCorrespondence.r4c_violation_is_r5_delta_witness
#print axioms GRBS.R5R4cCorrespondence.r4c_violation_property_fails
#print axioms GRBS.R5R4cCorrespondence.r4c_is_undischarged_r5_delta
