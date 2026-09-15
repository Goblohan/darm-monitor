import DarmMonitor.AuthorizedFactorizedComposition

namespace DARM

structure BoundaryIndexedAssuranceCertificate
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {targetLocus : Locus}
    (Basis : State → Prop) where

  sourceBoundary : Boundary
  targetBoundary : Boundary
  authorityActor : Actor
  state : State

  sourceGuarantee :
    G sourceBoundary state

  sourceEvidence :
    Evidence sourceBoundary state

  authorizedTransport :
    AuthorizedEvidenceTransport
      (Evidence := Evidence)
      (Authorized := Authorized)
      sourceBoundary
      targetBoundary

  targetEnforcement :
    Enforced targetLocus targetBoundary state


structure BoundaryIndexedAssuranceValidity
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {targetLocus : Locus}
    {Basis : State → Prop}
    (certificate :
      BoundaryIndexedAssuranceCertificate
        (G := G)
        (Evidence := Evidence)
        (Enforced := Enforced)
        (Authorized := Authorized)
        (source := source)
        (target := target)
        (targetLocus := targetLocus)
        Basis) : Prop where

  boundary_alignment :
    certificate.sourceBoundary = source ∧
    certificate.targetBoundary = target

  actor_alignment :
    certificate.authorizedTransport.actor =
      certificate.authorityActor

  basis_establishment :
    BasisEstablishment
      (G := G)
      (Evidence := Evidence)
      (Enforced := Enforced)
      (source := source)
      (target := target)
      (targetLocus := targetLocus)
      Basis

  basis_target_adequacy :
    BasisTargetAdequacy
      (G := G)
      target
      Basis


theorem certificate_sourceGuarantee_explicit
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {targetLocus : Locus}
    {Basis : State → Prop}
    (certificate :
      BoundaryIndexedAssuranceCertificate
        (G := G)
        (Evidence := Evidence)
        (Enforced := Enforced)
        (Authorized := Authorized)
        (source := source)
        (target := target)
        (targetLocus := targetLocus)
        Basis) :
    G certificate.sourceBoundary certificate.state :=
  certificate.sourceGuarantee


theorem certificate_authority_explicit
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {targetLocus : Locus}
    {Basis : State → Prop}
    (certificate :
      BoundaryIndexedAssuranceCertificate
        (G := G)
        (Evidence := Evidence)
        (Enforced := Enforced)
        (Authorized := Authorized)
        (source := source)
        (target := target)
        (targetLocus := targetLocus)
        Basis) :
    Authorized
      certificate.authorizedTransport.actor
      certificate.sourceBoundary
      certificate.targetBoundary :=
  certificate.authorizedTransport.authorization


theorem certificate_enforcement_explicit
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {targetLocus : Locus}
    {Basis : State → Prop}
    (certificate :
      BoundaryIndexedAssuranceCertificate
        (G := G)
        (Evidence := Evidence)
        (Enforced := Enforced)
        (Authorized := Authorized)
        (source := source)
        (target := target)
        (targetLocus := targetLocus)
        Basis) :
    Enforced
      targetLocus
      certificate.targetBoundary
      certificate.state :=
  certificate.targetEnforcement


theorem certificate_targetEvidence_of_transport
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {targetLocus : Locus}
    {Basis : State → Prop}
    (certificate :
      BoundaryIndexedAssuranceCertificate
        (G := G)
        (Evidence := Evidence)
        (Enforced := Enforced)
        (Authorized := Authorized)
        (source := source)
        (target := target)
        (targetLocus := targetLocus)
        Basis) :
    Evidence
      certificate.targetBoundary
      certificate.state := by
  exact
    (authorizedEvidenceTransport_implies_transport
      certificate.authorizedTransport)
      certificate.state
      certificate.sourceEvidence


theorem validCertificate_implies_targetGuarantee
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {targetLocus : Locus}
    {Basis : State → Prop}
    (certificate :
      BoundaryIndexedAssuranceCertificate
        (G := G)
        (Evidence := Evidence)
        (Enforced := Enforced)
        (Authorized := Authorized)
        (source := source)
        (target := target)
        (targetLocus := targetLocus)
        Basis)
    (validity :
      BoundaryIndexedAssuranceValidity
        certificate) :
    G target certificate.state := by

  have hTargetEvidence :
      Evidence certificate.targetBoundary certificate.state :=
    certificate_targetEvidence_of_transport certificate

  have hBasis :
      Basis certificate.state := by
    have hEstablish :=
      validity.basis_establishment certificate.state

    have hSource :
        G source certificate.state := by
      simpa [validity.boundary_alignment.1] using
        certificate.sourceGuarantee

    have hTargetEvidence' :
        Evidence target certificate.state := by
      simpa [validity.boundary_alignment.2] using
        hTargetEvidence

    have hEnforcement :
        Enforced targetLocus target certificate.state := by
      simpa [validity.boundary_alignment.2] using
        certificate.targetEnforcement

    exact
      hEstablish
        hSource
        hTargetEvidence'
        hEnforcement

  exact
    validity.basis_target_adequacy
      certificate.state
      hBasis

end DARM
