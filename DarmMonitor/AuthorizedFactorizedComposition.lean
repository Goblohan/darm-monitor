import DarmMonitor.CompositionRuleBasisFactorization
import DarmMonitor.AuthorizedEvidenceTransport

namespace DARM

structure AuthorizedFactorizedCompositionBasis
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {targetLocus : Locus}
    (Basis : State → Prop) where
  basisEstablishment :
    BasisEstablishment
      (G := G)
      (Evidence := Evidence)
      (Enforced := Enforced)
      (source := source)
      (target := target)
      (targetLocus := targetLocus)
      Basis
  basisTargetAdequacy :
    BasisTargetAdequacy
      (G := G)
      target
      Basis
  authorizedEvidenceTransport :
    AuthorizedEvidenceTransport
      (Evidence := Evidence)
      (Authorized := Authorized)
      source
      target

theorem authorizedFactorizedBasis_implies_compositionBasis
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {targetLocus : Locus}
    {Basis : State → Prop}
    (hBasis :
      AuthorizedFactorizedCompositionBasis
        (G := G)
        (Evidence := Evidence)
        (Enforced := Enforced)
        (Authorized := Authorized)
        (source := source)
        (target := target)
        (targetLocus := targetLocus)
        Basis) :
    CompositionRuleBasis
      G Evidence Enforced
      source target
      targetLocus Basis := by
  exact factorizedBasis_implies_compositionBasis
    ⟨hBasis.basisEstablishment, hBasis.basisTargetAdequacy⟩

theorem authorizedTransport_supplies_targetEvidence
    {State Boundary Actor : Type}
    {Evidence : ScopedEvidence Boundary State}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    (transport :
      AuthorizedEvidenceTransport
        (Evidence := Evidence)
        (Authorized := Authorized)
        source target)
    (s : State)
    (hSourceEvidence : Evidence source s) :
    Evidence target s := by
  exact transport.transport s hSourceEvidence

theorem authorizedFactorizedComposition_establishes_target
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {targetLocus : Locus}
    {Basis : State → Prop}
    (hBasis :
      AuthorizedFactorizedCompositionBasis
        (G := G)
        (Evidence := Evidence)
        (Enforced := Enforced)
        (Authorized := Authorized)
        (source := source)
        (target := target)
        (targetLocus := targetLocus)
        Basis)
    (s : State)
    (hSource : G source s)
    (hEnforced : Enforced targetLocus target s)
    (hSourceEvidence : Evidence source s) :
    G target s := by
  have hTargetEvidence :
      Evidence target s :=
    authorizedTransport_supplies_targetEvidence
      hBasis.authorizedEvidenceTransport
      s
      hSourceEvidence
  exact factorizedBasis_establishes_target
    ⟨hBasis.basisEstablishment, hBasis.basisTargetAdequacy⟩
    s
    hSource
    hTargetEvidence
    hEnforced

end DARM

#print axioms DARM.authorizedFactorizedBasis_implies_compositionBasis
#print axioms DARM.authorizedTransport_supplies_targetEvidence
#print axioms DARM.authorizedFactorizedComposition_establishes_target
