import DarmMonitor.BoundaryIndexedAssuranceCertificate

namespace DARM

structure PositiveState where
  safe : Bool

inductive PositiveBoundary
  | source
  | target

inductive PositiveLocus
  | targetEnforcer

inductive PositiveActor
  | authorizedActor

def positiveGuarantee :
    BoundaryIndexedGuarantee PositiveState PositiveBoundary :=
  fun _ state => state.safe = true

def positiveEvidence :
    ScopedEvidence PositiveBoundary PositiveState :=
  fun _ state => state.safe = true

def positiveEnforced :
    PositiveLocus →
      PositiveBoundary →
      PositiveState →
      Prop :=
  fun locus boundary state =>
    match locus, boundary with
    | PositiveLocus.targetEnforcer,
      PositiveBoundary.target =>
        state.safe = true
    | _, _ =>
        False

def positiveAuthority :
    EvidenceTransportAuthority
      PositiveActor
      PositiveBoundary :=
  fun actor src tgt =>
    match actor, src, tgt with
    | PositiveActor.authorizedActor,
      .source,
      .target =>
        True
    | _, _, _ =>
        False

theorem positiveTransport :
    EvidenceTransport
      positiveEvidence
      .source
      .target := by
  intro state hEvidence
  exact hEvidence

def positiveAuthorizedTransport :
    AuthorizedEvidenceTransport
      (Evidence := positiveEvidence)
      (Authorized := positiveAuthority)
      .source
      .target :=
  { actor := PositiveActor.authorizedActor
    authorization := by
      trivial
    transport := positiveTransport }

def positiveState : PositiveState :=
  { safe := true }

theorem positive_sourceGuarantee :
    positiveGuarantee
      .source
      positiveState := by
  rfl

theorem positive_sourceEvidence :
    positiveEvidence
      .source
      positiveState := by
  rfl

theorem positive_enforcement :
    positiveEnforced
      .targetEnforcer
      .target
      positiveState := by
  rfl

def positiveBasis :
    PositiveState → Prop :=
  fun state => state.safe = true

theorem positive_basisEstablishment :
    BasisEstablishment
      (G := positiveGuarantee)
      (Evidence := positiveEvidence)
      (Enforced := positiveEnforced)
      (source := PositiveBoundary.source)
      (target := PositiveBoundary.target)
      (targetLocus := PositiveLocus.targetEnforcer)
      positiveBasis := by
  intro state hSource hEvidence hEnforcement
  exact hSource

theorem positive_basisTargetAdequacy :
    BasisTargetAdequacy
      (G := positiveGuarantee)
      PositiveBoundary.target
      positiveBasis := by
  intro state hBasis
  exact hBasis

def positiveCertificate :
    BoundaryIndexedAssuranceCertificate
      (G := positiveGuarantee)
      (Evidence := positiveEvidence)
      (Enforced := positiveEnforced)
      (Authorized := positiveAuthority)
      (source := PositiveBoundary.source)
      (target := PositiveBoundary.target)
      (targetLocus := PositiveLocus.targetEnforcer)
      positiveBasis :=
  { sourceBoundary := PositiveBoundary.source
    targetBoundary := PositiveBoundary.target
    authorityActor := PositiveActor.authorizedActor
    state := positiveState
    sourceGuarantee := positive_sourceGuarantee
    sourceEvidence := positive_sourceEvidence
    authorizedTransport := positiveAuthorizedTransport
    targetEnforcement := positive_enforcement }

theorem positiveValidity :
    BoundaryIndexedAssuranceValidity
      positiveCertificate :=
  { boundary_alignment := by
      constructor <;> rfl
    actor_alignment := by
      rfl
    basis_establishment := positive_basisEstablishment
    basis_target_adequacy := positive_basisTargetAdequacy }

theorem positiveCertificate_targetGuarantee :
    positiveGuarantee
      positiveCertificate.targetBoundary
      positiveCertificate.state :=
  validCertificate_implies_targetGuarantee
    positiveCertificate
    positiveValidity

#print axioms DARM.positiveCertificate_targetGuarantee

end DARM
