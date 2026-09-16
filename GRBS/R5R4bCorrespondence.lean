import R4bAuthoritySubstitution
import DarmMonitor.R5BoundaryRepresentation

namespace GRBS.R5R4bCorrespondence

open GRBS.R4bAuthoritySubstitution
open DARM

def r4bProperty : Tr → Prop :=
  G

def r4bSourceDomain : Tr → Prop :=
  tracesUnder Auth.enforcing

def r4bTargetDomain : Tr → Prop :=
  tracesUnder Auth.permissive

theorem r4b_authority_obligation_iff_r5_delta_obligation :
    AuthSubstitutionObligation
      G
      Auth.enforcing
      Auth.permissive
      tracesUnder ↔
      GRBS.R5DomainPolymorphism.DeltaObligation
        Tr
        r4bSourceDomain
        r4bTargetDomain
        r4bProperty := by
  constructor
  · intro hR4b t hDelta
    exact hR4b t hDelta.1 hDelta.2
  · intro hR5 t htTarget htNotSource
    exact hR5 t ⟨htTarget, htNotSource⟩

theorem r4b_violation_is_r5_delta_witness :
    GRBS.R5DomainPolymorphism.Delta
      Tr
      r4bSourceDomain
      r4bTargetDomain
      Tr.violation := by
  exact ⟨trivial, fun h => Tr.noConfusion h⟩

theorem r4b_violation_property_fails :
    ¬ r4bProperty Tr.violation := by
  exact fun h => h

theorem r4b_is_undischarged_r5_delta :
    ¬ GRBS.R5DomainPolymorphism.DeltaObligation
      Tr
      r4bSourceDomain
      r4bTargetDomain
      r4bProperty := by
  intro hR5
  exact
    obligation_not_dischargeable
      (fun t htTarget htNotSource =>
        hR5 t ⟨htTarget, htNotSource⟩)

end GRBS.R5R4bCorrespondence

#print axioms GRBS.R5R4bCorrespondence.r4b_authority_obligation_iff_r5_delta_obligation
#print axioms GRBS.R5R4bCorrespondence.r4b_violation_is_r5_delta_witness
#print axioms GRBS.R5R4bCorrespondence.r4b_violation_property_fails
#print axioms GRBS.R5R4bCorrespondence.r4b_is_undischarged_r5_delta
