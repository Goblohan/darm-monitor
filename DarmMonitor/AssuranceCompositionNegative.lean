import DarmMonitor.AssuranceComposition

namespace DARM

structure NegativeState where
  sourceSafe : Bool
  targetSafe : Bool
  deriving DecidableEq, Repr

inductive NegativeBoundary
  | source
  | target
  deriving DecidableEq, Repr

inductive NegativeLocus
  | sourceEnforcer
  | targetEnforcer
  deriving DecidableEq, Repr

inductive NegativeActor
  | authorizedActor
  deriving DecidableEq, Repr

def negativeGuarantee :
    BoundaryIndexedGuarantee NegativeState NegativeBoundary :=
  fun boundary state =>
    match boundary with
    | NegativeBoundary.source => state.sourceSafe = true
    | NegativeBoundary.target => state.targetSafe = true

/--
Evidence deliberately does not encode target safety.
This allows target evidence to hold while the target guarantee fails.
-/
def negativeEvidence :
    ScopedEvidence NegativeBoundary NegativeState :=
  fun boundary state =>
    match boundary with
    | NegativeBoundary.source => state.sourceSafe = true
    | NegativeBoundary.target => state.sourceSafe = true

/--
The target enforcement claim is also deliberately independent of
targetSafe. This models the distinction between an enforcement claim
and the semantic truth of the broader guarantee.
-/
def negativeEnforced :
    NegativeLocus → NegativeBoundary → NegativeState → Prop :=
  fun locus boundary state =>
    match locus, boundary with
    | NegativeLocus.sourceEnforcer, NegativeBoundary.source =>
        state.sourceSafe = true
    | NegativeLocus.targetEnforcer, NegativeBoundary.target =>
        state.sourceSafe = true
    | _, _ => False

def negativeAuthorization :
    EvidenceTransportAuthority NegativeActor NegativeBoundary :=
  fun actor sourceBoundary targetBoundary =>
    actor = NegativeActor.authorizedActor ∧
    sourceBoundary = NegativeBoundary.source ∧
    targetBoundary = NegativeBoundary.target

def negativeSourceState : NegativeState :=
  { sourceSafe := true
    targetSafe := false }

theorem negative_source_guarantee :
    negativeGuarantee
      NegativeBoundary.source
      negativeSourceState := by
  rfl

theorem negative_source_evidence :
    negativeEvidence
      NegativeBoundary.source
      negativeSourceState := by
  rfl

theorem negative_target_evidence :
    negativeEvidence
      NegativeBoundary.target
      negativeSourceState := by
  rfl

theorem negative_target_enforcement :
    negativeEnforced
      NegativeLocus.targetEnforcer
      NegativeBoundary.target
      negativeSourceState := by
  rfl

theorem negative_target_guarantee_fails :
    ¬ negativeGuarantee
        NegativeBoundary.target
        negativeSourceState := by
  intro h
  exact Bool.noConfusion h

theorem negative_components_do_not_imply_target :
    negativeGuarantee
        NegativeBoundary.source
        negativeSourceState →
    negativeEvidence
        NegativeBoundary.target
        negativeSourceState →
    negativeEnforced
        NegativeLocus.targetEnforcer
        NegativeBoundary.target
        negativeSourceState →
    ¬ negativeGuarantee
        NegativeBoundary.target
        negativeSourceState := by
  intro _ _ _
  exact negative_target_guarantee_fails

theorem negative_authorization_holds :
    negativeAuthorization
      NegativeActor.authorizedActor
      NegativeBoundary.source
      NegativeBoundary.target := by
  exact ⟨rfl, rfl, rfl⟩

theorem negative_authorization_does_not_establish_target :
    negativeAuthorization
        NegativeActor.authorizedActor
        NegativeBoundary.source
        NegativeBoundary.target →
    ¬ negativeGuarantee
        NegativeBoundary.target
        negativeSourceState := by
  intro _
  exact negative_target_guarantee_fails

end DARM

#print axioms DARM.negative_source_guarantee
#print axioms DARM.negative_source_evidence
#print axioms DARM.negative_target_evidence
#print axioms DARM.negative_target_enforcement
#print axioms DARM.negative_target_guarantee_fails
#print axioms DARM.negative_components_do_not_imply_target
#print axioms DARM.negative_authorization_holds
#print axioms DARM.negative_authorization_does_not_establish_target
