import R4aScopeExpansion
import DarmMonitor.R5BoundaryRepresentation

namespace GRBS.R5R4aCorrespondence

open GRBS.R4aScopeExpansion
open DARM

theorem r4a_scope_obligation_iff_r5_delta_obligation :
    ScopeExpansionObligation G S₁ S₂ produces ↔
      GRBS.R5DomainPolymorphism.DeltaObligation
        Component
        S₁
        S₂
        (fun c => ∀ t, produces c t → G t) := by
  constructor
  · intro hR4a c hDelta
    exact hR4a c hDelta.1 hDelta.2
  · intro hR5 c hc2 hc1 t ht
    exact hR5 c ⟨hc2, hc1⟩ t ht

theorem r4a_remote_is_r5_delta_witness :
    GRBS.R5DomainPolymorphism.Delta
      Component
      S₁
      S₂
      Component.compRemote := by
  exact ⟨trivial, fun h => Component.noConfusion h⟩

theorem r4a_remote_property_fails :
    ¬ (∀ t, produces Component.compRemote t → G t) := by
  intro h
  exact h Tr.violation trivial

theorem r4a_is_undischarged_r5_delta :
    ¬ GRBS.R5DomainPolymorphism.DeltaObligation
      Component
      S₁
      S₂
      (fun c => ∀ t, produces c t → G t) := by
  intro h
  exact
    r4a_remote_property_fails
      (h Component.compRemote
        (r4a_remote_is_r5_delta_witness))

end GRBS.R5R4aCorrespondence

#print axioms GRBS.R5R4aCorrespondence.r4a_scope_obligation_iff_r5_delta_obligation
#print axioms GRBS.R5R4aCorrespondence.r4a_remote_is_r5_delta_witness
#print axioms GRBS.R5R4aCorrespondence.r4a_remote_property_fails
#print axioms GRBS.R5R4aCorrespondence.r4a_is_undischarged_r5_delta
