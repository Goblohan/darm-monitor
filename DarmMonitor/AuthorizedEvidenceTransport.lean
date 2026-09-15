import DarmMonitor.ScopedEvidence

namespace DARM

/--
An authority predicate identifies which actors are authorized to
transport evidence from one boundary to another.
-/
def EvidenceTransportAuthority
    (Actor Boundary : Type) : Type :=
  Actor → Boundary → Boundary → Prop

/--
An authorized evidence transport records the actor, the explicit
authorization for that actor to transport evidence between the
specified boundaries, and the transport rule itself.
-/
structure AuthorizedEvidenceTransport
    {Actor Boundary State : Type}
    (Evidence : ScopedEvidence Boundary State)
    (Authorized : EvidenceTransportAuthority Actor Boundary)
    (source target : Boundary) where
  actor : Actor
  authorization : Authorized actor source target
  transport : EvidenceTransport Evidence source target

/--
An authorized transport necessarily provides the corresponding
evidence-transport rule.
-/
theorem authorizedEvidenceTransport_implies_transport
    {Actor Boundary State : Type}
    {Evidence : ScopedEvidence Boundary State}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    (hAuthorized :
      AuthorizedEvidenceTransport
        Evidence Authorized source target) :
    EvidenceTransport Evidence source target :=
  hAuthorized.transport

/--
An authorized transport permits evidence to be moved for a particular
state.
-/
theorem authorizedEvidenceTransport_transports
    {Actor Boundary State : Type}
    {Evidence : ScopedEvidence Boundary State}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    (hAuthorized :
      AuthorizedEvidenceTransport
        Evidence Authorized source target)
    (s : State)
    (hEvidence : Evidence source s) :
    Evidence target s := by
  exact hAuthorized.transport s hEvidence

/--
Authorization is carried explicitly by an authorized transport
certificate and applies to the actor named by that certificate.
-/
theorem authorization_is_explicit
    {Actor Boundary State : Type}
    {Evidence : ScopedEvidence Boundary State}
    {Authorized : EvidenceTransportAuthority Actor Boundary}
    {source target : Boundary}
    (hAuthorized :
      AuthorizedEvidenceTransport
        Evidence Authorized source target) :
    Authorized hAuthorized.actor source target := by
  exact hAuthorized.authorization

end DARM

#print axioms DARM.authorizedEvidenceTransport_implies_transport
#print axioms DARM.authorizedEvidenceTransport_transports
#print axioms DARM.authorization_is_explicit
