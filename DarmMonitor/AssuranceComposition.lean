import DarmMonitor.EnforcementLocus

namespace DARM

/--
An assurance composition rule explicitly states the conditions under
which a source guarantee, transported evidence, and target enforcement
jointly establish a target guarantee.
-/
structure AssuranceCompositionRule
    {State Boundary Locus : Type}
    (G : BoundaryIndexedGuarantee State Boundary)
    (Evidence : ScopedEvidence Boundary State)
    (Enforced : Locus → Boundary → State → Prop)
    (source target : Boundary)
    (targetLocus : Locus) where
  establishesTarget :
    ∀ s,
      G source s →
      Evidence target s →
      Enforced targetLocus target s →
      G target s

/--
A composed assurance certificate records the source assurance,
authorized evidence transport, and target enforcement claim.
The target guarantee is not assumed. It must be derived from an
explicit composition rule.
-/
structure ComposedAssuranceCertificate
    {State Boundary Locus Actor : Type}
    (G : BoundaryIndexedGuarantee State Boundary)
    (Evidence : ScopedEvidence Boundary State)
    (Enforced : Locus → Boundary → State → Prop)
    (Authorized : EvidenceTransportAuthority Actor Boundary)
    (source target : Boundary)
    (sourceLocus targetLocus : Locus)
    (actor : Actor)
    (state : State) where
  sourceGuarantee : G source state
  sourceEvidence : Evidence source state
  evidenceAuthorization :
    Authorized actor source target
  evidenceTransport :
    EvidenceTransport Evidence source target
  targetEnforcement :
    Enforced targetLocus target state

/--
An authorized transport carried by a composed assurance certificate
establishes the target-scoped evidence.
-/
theorem composedCertificate_targetEvidence
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {sourceLocus targetLocus : Locus}
    {actor : Actor}
    {state : State}
    (certificate :
      ComposedAssuranceCertificate
        G Evidence Enforced Authorized
        source target sourceLocus targetLocus actor state) :
    Evidence target state := by
  exact certificate.evidenceTransport state certificate.sourceEvidence

/--
An explicit composition rule derives the target guarantee from the
components recorded in a composed assurance certificate.
-/
theorem composedCertificate_targetGuarantee
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {sourceLocus targetLocus : Locus}
    {actor : Actor}
    {state : State}
    (rule :
      AssuranceCompositionRule
        G Evidence Enforced source target targetLocus)
    (certificate :
      ComposedAssuranceCertificate
        G Evidence Enforced Authorized
        source target sourceLocus targetLocus actor state) :
    G target state := by
  exact rule.establishesTarget
    state
    certificate.sourceGuarantee
    (composedCertificate_targetEvidence certificate)
    certificate.targetEnforcement

/--
The authorization recorded by a composed assurance certificate is
explicitly available as a proposition.
-/
theorem composedCertificate_authorization
    {State Boundary Locus Actor : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    {sourceLocus targetLocus : Locus}
    {actor : Actor}
    {state : State}
    (certificate :
      ComposedAssuranceCertificate
        G Evidence Enforced Authorized
        source target sourceLocus targetLocus actor state) :
    Authorized actor source target :=
  certificate.evidenceAuthorization

end DARM

#print axioms DARM.composedCertificate_targetEvidence
#print axioms DARM.composedCertificate_targetGuarantee
#print axioms DARM.composedCertificate_authorization
