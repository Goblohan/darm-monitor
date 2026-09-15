import DarmMonitor.AuthorizedEvidenceTransport

namespace DARM

/--
An assurance certificate records a guarantee at an explicit boundary
for an explicit state, together with scoped evidence on which the
certificate relies.
-/
structure AssuranceCertificate
    {State Boundary : Type}
    (G : BoundaryIndexedGuarantee State Boundary)
    (Evidence : ScopedEvidence Boundary State) where
  boundary : Boundary
  state : State
  evidenceSource : Boundary
  guarantee : G boundary state
  evidence : Evidence evidenceSource state

/--
A certificate explicitly identifies the boundary at which its guarantee
is established.
-/
theorem assuranceCertificate_boundary_explicit
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    (certificate : AssuranceCertificate G Evidence) :
    G certificate.boundary certificate.state :=
  certificate.guarantee

/--
A certificate explicitly identifies the source boundary of its evidence.
-/
theorem assuranceCertificate_evidence_source_explicit
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    (certificate : AssuranceCertificate G Evidence) :
    Evidence certificate.evidenceSource certificate.state :=
  certificate.evidence

/--
A certificate expansion denotes a target-boundary guarantee for the
state carried by the source certificate.
-/
def CertificateExpansion
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    (certificate : AssuranceCertificate G Evidence)
    (target : Boundary) : Prop :=
  G target certificate.state

/--
An explicit basis justifies expansion of a certificate from its declared
boundary to a target boundary using both the source guarantee and its
scoped evidence.
-/
structure CertificateExpansionBasis
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    (certificate : AssuranceCertificate G Evidence)
    (target : Boundary) where
  establishesTarget :
    G certificate.boundary certificate.state →
    Evidence certificate.evidenceSource certificate.state →
    G target certificate.state

/--
An explicit expansion basis establishes the target-boundary guarantee
represented by the certificate expansion.
-/
theorem certificateExpansion_of_basis
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {certificate : AssuranceCertificate G Evidence}
    {target : Boundary}
    (basis : CertificateExpansionBasis certificate target) :
    CertificateExpansion certificate target := by
  exact basis.establishesTarget
    certificate.guarantee
    certificate.evidence

end DARM

#print axioms DARM.assuranceCertificate_boundary_explicit
#print axioms DARM.assuranceCertificate_evidence_source_explicit
#print axioms DARM.certificateExpansion_of_basis
