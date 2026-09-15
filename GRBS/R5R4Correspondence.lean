/-
  R5/R4 CORRESPONDENCE

  PURPOSE:

  Test whether independently constructed R4 attacks can be represented
  by the generic R5 assurance-delta structure without changing their
  semantics.

  TARGETS:

    R4a — scope expansion
    R4e — boundary composition

  IMPORTANT:

  These are correspondence propositions, not claims that R5 is equivalent
  to every R4 attack or that the abstraction is novel.
-/

import R5AssuranceConservation
import R4eBoundaryComposition
import R4aScopeExpansion

namespace GRBS.R5R4Correspondence

open GRBS.R5AssuranceConservation

/-!
  R4a → R5

  R4a defines a narrower scope S₁ and an expanded scope S₂.

  R5 represents the newly introduced scope as:

      Delta S₁ S₂ = S₂ \ S₁

  The R4a expansion obligation requires the guarantee to hold for every
  newly introduced component and every trace produced by that component.

  R5 expresses the same requirement through a property over each
  delta element.
-/

namespace R4aCorrespondence

open GRBS.R4aScopeExpansion

def R4aProperty : Component → Prop :=
  fun c => ∀ t, produces c t → G t

def R4aDeltaObligation : Prop :=
  DeltaObligation Component S₁ S₂ R4aProperty

/-
  R4a writes delta membership as two separate premises:

      S₂ c
      ¬ S₁ c

  R5 packages the same information as:

      S₂ c ∧ ¬ S₁ c
-/

theorem r4a_delta_obligation_iff_scope_obligation :
    R4aDeltaObligation ↔
      ScopeExpansionObligation G S₁ S₂ produces := by
  constructor
  · intro h c hc2 hnc1 t ht
    exact h c ⟨hc2, hnc1⟩ t ht
  · intro h c hdelta t ht
    exact h c hdelta.1 hdelta.2 t ht

/-
  The additional component introduced by R4a is an R5 delta element.
-/

theorem r4a_remote_is_delta :
    Delta Component S₁ S₂ Component.compRemote := by
  constructor
  · trivial
  · intro h
    exact Component.noConfusion h

/-
  The R5 delta obligation is not dischargeable in the R4a witness.
-/

theorem r4a_delta_obligation_fails :
    ¬ R4aDeltaObligation := by
  intro h
  exact h Component.compRemote
    ⟨trivial, fun h => Component.noConfusion h⟩
    Tr.violation
    trivial

/-
  R4a therefore contains an assurance-relevant delta whose obligation
  is independently shown to be undischargeable.
-/

theorem r4a_is_undischarged_r5_delta :
    Delta Component S₁ S₂ Component.compRemote
    ∧ ¬ R4aDeltaObligation := by
  exact ⟨r4a_remote_is_delta, r4a_delta_obligation_fails⟩

/-
  Preserve the independently established R4a result.
-/

theorem r4a_original_failure :
    SafeOverScope G S₁ produces
    ∧ (∀ c, S₁ c → S₂ c)
    ∧ (∃ c, S₂ c ∧ ¬ S₁ c)
    ∧ ¬ SafeOverScope G S₂ produces
    ∧ ¬ ScopeExpansionObligation G S₁ S₂ produces :=
  unsupported_scope_expansion

/-
  Final R4a/R5 correspondence.
-/

theorem r4a_matches_r5_pattern :
    Delta Component S₁ S₂ Component.compRemote
    ∧ ¬ R4aDeltaObligation
    ∧ SafeOverScope G S₁ produces
    ∧ (∀ c, S₁ c → S₂ c)
    ∧ (∃ c, S₂ c ∧ ¬ S₁ c)
    ∧ ¬ SafeOverScope G S₂ produces
    ∧ ¬ ScopeExpansionObligation G S₁ S₂ produces := by
  exact ⟨
    r4a_remote_is_delta,
    r4a_delta_obligation_fails,
    safe_over_S1,
    scope_included,
    scope_strict,
    not_safe_over_S2,
    obligation_not_dischargeable
  ⟩

end R4aCorrespondence

/-!
  R4e → R5

  R4e is kept in a separate namespace because it defines its own
  Dependency type. This prevents the Component type from R4a from
  being confused with the R4e model.
-/

namespace R4eCorrespondence

open GRBS.R4eBoundaryComposition

def R4eSourceDomain : Dependency → Prop :=
  fun d => DepA d ∨ DepB d

def R4eTargetDomain : Dependency → Prop :=
  DepAB

def R4eProperty : Dependency → Prop :=
  CovAB

/-
  The interaction dependency is introduced by composition and is not
  present in either local dependency domain.
-/

theorem interaction_is_r5_delta :
    Delta Dependency R4eSourceDomain R4eTargetDomain
      Dependency.interactionAB := by
  constructor
  · exact interaction_is_compositional.1
  · intro h
    rcases h with hA | hB
    · exact interaction_is_compositional.2.1 hA
    · exact interaction_is_compositional.2.2 hB

/-
  R5's property for the interaction dependency is exactly its composed
  coverage predicate.
-/

theorem interaction_obligation_is_r5_property :
    R4eProperty Dependency.interactionAB ↔
      CovAB Dependency.interactionAB := by
  rfl

/-
  The interaction dependency is not covered by the composed boundary.
-/

theorem interaction_delta_obligation_fails :
    ¬ R4eProperty Dependency.interactionAB :=
  interaction_uncovered_composition

theorem r4e_is_undischarged_r5_delta :
    Delta Dependency R4eSourceDomain R4eTargetDomain
      Dependency.interactionAB
    ∧ ¬ R4eProperty Dependency.interactionAB := by
  exact ⟨interaction_is_r5_delta, interaction_delta_obligation_fails⟩

/-
  Preserve the independently established R4e result.
-/

theorem r4e_original_failure :
    AssuredA ∧ AssuredB ∧ ¬ AssuredAB :=
  unsupported_boundary_composition

end R4eCorrespondence

end GRBS.R5R4Correspondence
