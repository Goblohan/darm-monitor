/-
  R5 / R4 AUDIT

  This artifact records the formal correspondence between the six R4
  assurance-transfer attacks and the generic R5 conservation kernel.

  It does not claim that R5 discovers the assurance-relevant delta.

  Each R4 artifact independently identifies a transfer failure.
  The correspondence artifacts represent those failures using the
  generic R5 Delta / DeltaObligation structure.

  Assurance-object domains:

      R4a  Component
      R4b  Tr
      R4c  Tr
      R4d  Tr
      R4e  Dependency
      R4f  Object × Object

  The purpose is to test whether the same R5 transfer structure survives
  across these materially different assurance domains.
-/

import R5DomainPolymorphism
import R5R4Correspondence
import R5R4bCorrespondence
import R5R4cCorrespondence
import R5R4dCorrespondence
import R4fRelationalAssurance

namespace GRBS.R5R4Audit

/-
  R4a — Scope expansion

  X = Component

  The remote component is introduced into the target assurance domain.
-/

theorem r4a_instantiates_r5 :
    R5AssuranceConservation.Delta
        R4aScopeExpansion.Component
        R4aScopeExpansion.S₁
        R4aScopeExpansion.S₂
        R4aScopeExpansion.Component.compRemote
    ∧
    ¬ R5R4Correspondence.R4aCorrespondence.R4aDeltaObligation := by
  exact R5R4Correspondence.R4aCorrespondence.r4a_is_undischarged_r5_delta

/-
  R4b — Authority substitution

  X = execution trace

  The target authority admits a violating execution outside the source
  authority's assurance domain.
-/

theorem r4b_instantiates_r5 :
    R5AssuranceConservation.Delta
        R4bAuthoritySubstitution.Tr
        R4bCorrespondence.R4bSourceDomain
        R4bCorrespondence.R4bTargetDomain
        R4bAuthoritySubstitution.Tr.violation
    ∧
    ¬ R4bCorrespondence.R4bDeltaObligation := by
  exact R4bCorrespondence.r4b_is_undischarged_r5_delta

/-
  R4c — Enforcement-locus substitution

  X = execution trace
-/

theorem r4c_instantiates_r5 :
    R5AssuranceConservation.Delta
        R4cLocusSubstitution.Tr
        R4cCorrespondence.R4cSourceDomain
        R4cCorrespondence.R4cTargetDomain
        R4cLocusSubstitution.Tr.violation
    ∧
    ¬ R4cCorrespondence.R4cDeltaObligation := by
  exact R4cCorrespondence.r4c_is_undischarged_r5_delta

/-
  R4d — Evidence substitution

  X = execution trace

  The system execution domain is unchanged.

  The delta is a produced execution outside substituted evidence
  coverage.
-/

theorem r4d_instantiates_r5 :
    R5AssuranceConservation.Delta
        R4dEvidenceCoverage.Tr
        R4dCorrespondence.R4dSourceDomain
        R4dCorrespondence.R4dTargetDomain
        R4dEvidenceCoverage.Tr.safeB
    ∧
    ¬ R4dCorrespondence.R4dDeltaObligation := by
  exact R4dCorrespondence.r4d_is_undischarged_r5_delta

/-
  R4e — Boundary composition

  X = Dependency

  Composition introduces an interaction dependency absent from both
  local dependency domains.
-/

theorem r4e_instantiates_r5 :
    R5AssuranceConservation.Delta
        R4eBoundaryComposition.Dependency
        R5R4Correspondence.R4eCorrespondence.R4eSourceDomain
        R5R4Correspondence.R4eCorrespondence.R4eTargetDomain
        R4eBoundaryComposition.Dependency.interactionAB
    ∧
    ¬ R5R4Correspondence.R4eCorrespondence.R4eProperty
        R4eBoundaryComposition.Dependency.interactionAB := by
  exact R5R4Correspondence.R4eCorrespondence.r4e_is_undischarged_r5_delta

/-
  R4f — Relational assurance

  X = Object × Object

  The relational pair (A,B) is an R5 delta whose property obligation
  cannot be discharged.
-/

theorem r4f_instantiates_r5 :
    R4fRelationalAssurance.R5Delta
        (R4fRelationalAssurance.Object.A,
         R4fRelationalAssurance.Object.B)
    ∧
    ¬ R4fRelationalAssurance.R5DeltaObligation := by
  exact R4fRelationalAssurance.relational_failure_is_r5_delta_failure

/-
  Combined audit.

  Every R4 witness contains an assurance-relevant delta for which the
  corresponding R5 conservation obligation is not discharged.

  This establishes structural correspondence only.

  It does not assert semantic equivalence between the six attacks.
-/

theorem six_attack_audit :
    (
      R5AssuranceConservation.Delta
          R4aScopeExpansion.Component
          R4aScopeExpansion.S₁
          R4aScopeExpansion.S₂
          R4aScopeExpansion.Component.compRemote
      ∧
      ¬ R5R4Correspondence.R4aCorrespondence.R4aDeltaObligation
    )
    ∧
    (
      R5AssuranceConservation.Delta
          R4bAuthoritySubstitution.Tr
          R4bCorrespondence.R4bSourceDomain
          R4bCorrespondence.R4bTargetDomain
          R4bAuthoritySubstitution.Tr.violation
      ∧
      ¬ R4bCorrespondence.R4bDeltaObligation
    )
    ∧
    (
      R5AssuranceConservation.Delta
          R4cLocusSubstitution.Tr
          R4cCorrespondence.R4cSourceDomain
          R4cCorrespondence.R4cTargetDomain
          R4cLocusSubstitution.Tr.violation
      ∧
      ¬ R4cCorrespondence.R4cDeltaObligation
    )
    ∧
    (
      R5AssuranceConservation.Delta
          R4dEvidenceCoverage.Tr
          R4dCorrespondence.R4dSourceDomain
          R4dCorrespondence.R4dTargetDomain
          R4dEvidenceCoverage.Tr.safeB
      ∧
      ¬ R4dCorrespondence.R4dDeltaObligation
    )
    ∧
    (
      R5AssuranceConservation.Delta
          R4eBoundaryComposition.Dependency
          R5R4Correspondence.R4eCorrespondence.R4eSourceDomain
          R5R4Correspondence.R4eCorrespondence.R4eTargetDomain
          R4eBoundaryComposition.Dependency.interactionAB
      ∧
      ¬ R5R4Correspondence.R4eCorrespondence.R4eProperty
          R4eBoundaryComposition.Dependency.interactionAB
    )
    ∧
    (
      R4fRelationalAssurance.R5Delta
          (R4fRelationalAssurance.Object.A,
           R4fRelationalAssurance.Object.B)
      ∧
      ¬ R4fRelationalAssurance.R5DeltaObligation
    ) := by
  exact ⟨
    R5R4Correspondence.R4aCorrespondence.r4a_is_undischarged_r5_delta,
    R4bCorrespondence.r4b_is_undischarged_r5_delta,
    R4cCorrespondence.r4c_is_undischarged_r5_delta,
    R4dCorrespondence.r4d_is_undischarged_r5_delta,
    R5R4Correspondence.R4eCorrespondence.r4e_is_undischarged_r5_delta,
    R4fRelationalAssurance.relational_failure_is_r5_delta_failure
  ⟩

end GRBS.R5R4Audit
