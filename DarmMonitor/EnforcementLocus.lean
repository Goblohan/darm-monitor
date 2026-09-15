import DarmMonitor.AssuranceCertificate

namespace DARM

/--
An explicit enforcement relation associates a guarantee boundary and
state with a declared enforcement locus.
-/
def EnforcedAt
    {State Boundary Locus : Type}
    (Enforced : Locus → Boundary → State → Prop)
    (locus : Locus)
    (boundary : Boundary)
    (state : State) : Prop :=
  Enforced locus boundary state

/--
An enforcement certificate records a guarantee together with the
proposition that the guarantee is enforced at its declared locus.
-/
structure EnforcementCertificate
    {State Boundary Locus : Type}
    (G : BoundaryIndexedGuarantee State Boundary)
    (Enforced : Locus → Boundary → State → Prop) where
  boundary : Boundary
  locus : Locus
  state : State
  guarantee : G boundary state
  enforcement : Enforced locus boundary state

/--
An enforcement certificate establishes the guarantee at its declared
boundary and state.
-/
theorem enforcementCertificate_guarantee
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Enforced : Locus → Boundary → State → Prop}
    (certificate : EnforcementCertificate G Enforced) :
    G certificate.boundary certificate.state :=
  certificate.guarantee

/--
An enforcement certificate establishes an enforcement claim at its
declared locus, boundary, and state.
-/
theorem enforcementCertificate_enforcement
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Enforced : Locus → Boundary → State → Prop}
    (certificate : EnforcementCertificate G Enforced) :
    Enforced certificate.locus certificate.boundary certificate.state :=
  certificate.enforcement

/--
A locus-transfer rule explicitly states when an enforcement claim may
be transferred from one locus to another.
-/
def LocusTransfer
    {State Boundary Locus : Type}
    (Enforced : Locus → Boundary → State → Prop)
    (source target : Locus) : Prop :=
  ∀ b s, Enforced source b s → Enforced target b s

/--
An explicit locus-transfer rule permits an enforcement claim to move
between loci.
-/
theorem locusTransfer
    {State Boundary Locus : Type}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Locus}
    (hTransfer : LocusTransfer Enforced source target)
    (b : Boundary)
    (s : State)
    (hEnforced : Enforced source b s) :
    Enforced target b s := by
  exact hTransfer b s hEnforced

end DARM

#print axioms DARM.enforcementCertificate_guarantee
#print axioms DARM.enforcementCertificate_enforcement
#print axioms DARM.locusTransfer
