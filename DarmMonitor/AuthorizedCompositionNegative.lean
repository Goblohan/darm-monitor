import DarmMonitor.AuthorizedFactorizedComposition

namespace DARM

structure AuthorizedNegativeState where
  sourceSafe : Bool
  targetSafe : Bool

inductive AuthorizedNegativeBoundary
  | source
  | target

inductive AuthorizedNegativeLocus
  | targetEnforcer

inductive AuthorizedNegativeActor
  | authorizedActor

def authorizedNegativeGuarantee :
    BoundaryIndexedGuarantee
      AuthorizedNegativeState
      AuthorizedNegativeBoundary :=
  fun boundary state =>
    match boundary with
    | AuthorizedNegativeBoundary.source =>
        state.sourceSafe = true
    | AuthorizedNegativeBoundary.target =>
        state.targetSafe = true

def authorizedNegativeEvidence :
    ScopedEvidence
      AuthorizedNegativeBoundary
      AuthorizedNegativeState :=
  fun boundary state =>
    match boundary with
    | AuthorizedNegativeBoundary.source =>
        state.sourceSafe = true
    | AuthorizedNegativeBoundary.target =>
        state.sourceSafe = true

def authorizedNegativeEnforced :
    AuthorizedNegativeLocus →
      AuthorizedNegativeBoundary →
      AuthorizedNegativeState →
      Prop :=
  fun locus boundary state =>
    match locus, boundary with
    | AuthorizedNegativeLocus.targetEnforcer,
      AuthorizedNegativeBoundary.target =>
        state.sourceSafe = true
    | _, _ =>
        False

def authorizedNegativeAuthority :
    EvidenceTransportAuthority
      AuthorizedNegativeActor
      AuthorizedNegativeBoundary :=
  fun actor source target =>
    match actor, source, target with
    | AuthorizedNegativeActor.authorizedActor,
      .source,
      .target =>
        True
    | _, _, _ =>
        False

theorem authorizedNegativeTransport :
    EvidenceTransport
      authorizedNegativeEvidence
      .source
      .target := by
  intro s hEvidence
  exact hEvidence

def authorizedNegativeAuthorizedTransport :
    AuthorizedEvidenceTransport
      (Evidence := authorizedNegativeEvidence)
      (Authorized := authorizedNegativeAuthority)
      .source
      .target :=
  { actor := AuthorizedNegativeActor.authorizedActor
    authorization := by
      trivial
    transport := authorizedNegativeTransport }

def authorizedNegativeState : AuthorizedNegativeState :=
  { sourceSafe := true
    targetSafe := false }

theorem authorizedNegative_sourceGuarantee :
    authorizedNegativeGuarantee
      .source
      authorizedNegativeState := by
  rfl

theorem authorizedNegative_sourceEvidence :
    authorizedNegativeEvidence
      .source
      authorizedNegativeState := by
  rfl

theorem authorizedNegative_targetEvidence :
    authorizedNegativeEvidence
      .target
      authorizedNegativeState := by
  rfl

theorem authorizedNegative_authorization :
    authorizedNegativeAuthority
      .authorizedActor
      .source
      .target := by
  trivial

theorem authorizedNegative_enforcement :
    authorizedNegativeEnforced
      .targetEnforcer
      .target
      authorizedNegativeState := by
  rfl

theorem authorizedNegative_targetGuarantee_fails :
    ¬ authorizedNegativeGuarantee
      .target
      authorizedNegativeState := by
  intro h
  cases h

theorem authorizedNegative_components_do_not_imply_target :
    ¬ (
      authorizedNegativeGuarantee
        .source
        authorizedNegativeState ∧
      authorizedNegativeEvidence
        .source
        authorizedNegativeState ∧
      authorizedNegativeEvidence
        .target
        authorizedNegativeState ∧
      authorizedNegativeAuthority
        .authorizedActor
        .source
        .target ∧
      authorizedNegativeEnforced
        .targetEnforcer
        .target
        authorizedNegativeState ∧
      authorizedNegativeGuarantee
        .target
        authorizedNegativeState
    ) := by
  intro h
  exact authorizedNegative_targetGuarantee_fails
    h.2.2.2.2.2

end DARM

#print axioms DARM.authorizedNegative_sourceGuarantee
#print axioms DARM.authorizedNegative_sourceEvidence
#print axioms DARM.authorizedNegative_targetEvidence
#print axioms DARM.authorizedNegative_authorization
#print axioms DARM.authorizedNegativeTransport
#print axioms DARM.authorizedNegative_enforcement
#print axioms DARM.authorizedNegative_targetGuarantee_fails
#print axioms DARM.authorizedNegative_components_do_not_imply_target
