import DarmMonitor.BoundaryIndexedAssuranceCertificate
import DarmMonitor.AuthorizedCompositionNegative

namespace DARM

def authorizedNegativeWeakBasis :
    AuthorizedNegativeState → Prop :=
  fun state => state.sourceSafe = true

def authorizedNegativeCertificate :
    BoundaryIndexedAssuranceCertificate
      (G := authorizedNegativeGuarantee)
      (Evidence := authorizedNegativeEvidence)
      (Enforced := authorizedNegativeEnforced)
      (Authorized := authorizedNegativeAuthority)
      (source := AuthorizedNegativeBoundary.source)
      (target := AuthorizedNegativeBoundary.target)
      (targetLocus := AuthorizedNegativeLocus.targetEnforcer)
      authorizedNegativeWeakBasis :=
  { sourceBoundary := AuthorizedNegativeBoundary.source
    targetBoundary := AuthorizedNegativeBoundary.target
    authorityActor := AuthorizedNegativeActor.authorizedActor
    state := authorizedNegativeState
    sourceGuarantee := authorizedNegative_sourceGuarantee
    sourceEvidence := authorizedNegative_sourceEvidence
    authorizedTransport := authorizedNegativeAuthorizedTransport
    targetEnforcement := authorizedNegative_enforcement }


theorem authorizedNegativeCertificate_has_targetEvidence :
    authorizedNegativeEvidence
      authorizedNegativeCertificate.targetBoundary
      authorizedNegativeCertificate.state := by
  exact certificate_targetEvidence_of_transport
    authorizedNegativeCertificate


theorem authorizedNegativeCertificate_targetGuarantee_fails :
    ¬ authorizedNegativeGuarantee
      authorizedNegativeCertificate.targetBoundary
      authorizedNegativeCertificate.state := by
  exact authorizedNegative_targetGuarantee_fails


theorem authorizedNegativeCertificate_has_all_nonsemantic_components :
    authorizedNegativeCertificate.sourceBoundary =
        AuthorizedNegativeBoundary.source ∧
    authorizedNegativeCertificate.targetBoundary =
        AuthorizedNegativeBoundary.target ∧
    authorizedNegativeCertificate.authorityActor =
        AuthorizedNegativeActor.authorizedActor := by
  constructor
  · rfl
  constructor <;> rfl


end DARM

#print axioms DARM.authorizedNegativeCertificate_has_targetEvidence
#print axioms DARM.authorizedNegativeCertificate_targetGuarantee_fails
#print axioms DARM.authorizedNegativeCertificate_has_all_nonsemantic_components
