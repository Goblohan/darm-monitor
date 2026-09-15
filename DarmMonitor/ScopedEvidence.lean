import DarmMonitor.LicensedExpansion

namespace DARM

/--
Evidence is indexed by the boundary at which it is established and
the state to which it applies.
-/
def ScopedEvidence
    (Boundary State : Type) :=
  Boundary → State → Prop

/--
An explicit rule authorizing transport of evidence from one boundary
to another for the same state.
-/
def EvidenceTransport
    {Boundary State : Type}
    (Evidence : ScopedEvidence Boundary State)
    (source target : Boundary) : Prop :=
  ∀ s, Evidence source s → Evidence target s

/--
A scoped assurance basis identifies an assumption at the target
boundary, evidence originating at an explicit source boundary, and
the logical relation from the target assumption to the broader
guarantee.
-/
structure ScopedExpansionBasis
    {State Boundary : Type}
    (G : BoundaryIndexedGuarantee State Boundary)
    (narrow broad : Boundary) where
  Assumption : Boundary → State → Prop
  Evidence : ScopedEvidence Boundary State
  evidenceSource : Boundary
  narrow_implies_targetAssumption :
    ∀ s, G narrow s → Assumption broad s
  evidence_establishes_targetAssumption :
    ∀ s, Evidence evidenceSource s → Assumption broad s
  targetAssumption_implies_broad :
    ∀ s, Assumption broad s → G broad s

/--
A state satisfies the licensed expansion when its narrower guarantee
holds and evidence from the designated source boundary is available.
-/
def LicensedExpansionAt
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    (narrow broad : Boundary)
    (basis : ScopedExpansionBasis G narrow broad)
    (s : State) : Prop :=
  G narrow s ∧ basis.Evidence basis.evidenceSource s

/--
A licensed expansion at a state establishes the broader guarantee when
the basis' evidence is sufficient for the target assumption.
-/
theorem licensedExpansionAt_implies_broad
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {narrow broad : Boundary}
    (basis : ScopedExpansionBasis G narrow broad)
    (s : State)
    (hLicensed : LicensedExpansionAt narrow broad basis s) :
    G broad s := by
  exact basis.targetAssumption_implies_broad s
    (basis.evidence_establishes_targetAssumption s hLicensed.2)

/--
If the narrower guarantee itself establishes the target assumption,
then the broader guarantee follows without using additional evidence.
This is the purely logical expansion case.
-/
theorem narrowGuarantee_implies_broad_of_basis
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {narrow broad : Boundary}
    (basis : ScopedExpansionBasis G narrow broad) :
    GuaranteeExpansion G narrow broad := by
  intro s hNarrow
  exact basis.targetAssumption_implies_broad s
    (basis.narrow_implies_targetAssumption s hNarrow)

/--
An explicit transport rule permits evidence to move from its source
boundary to another boundary for the same state.
-/
theorem evidence_transport
    {Boundary State : Type}
    {Evidence : ScopedEvidence Boundary State}
    {source target : Boundary}
    (hTransport : EvidenceTransport Evidence source target)
    (s : State)
    (hEvidence : Evidence source s) :
    Evidence target s := by
  exact hTransport s hEvidence

/--
Concrete evidence for the boundary-expansion model. Local evidence
can hold while system evidence additionally requires external safety.
-/
def concreteEvidence :
    ScopedEvidence Boundary State :=
  fun b s =>
    match b with
    | Boundary.localScope => localGuarantee s
    | Boundary.systemScope => systemGuarantee s

/--
Local evidence can hold while system evidence fails for the same state.
-/
theorem localEvidence_does_not_imply_systemEvidence :
    ¬ (
      ∀ s : State,
        concreteEvidence Boundary.localScope s →
        concreteEvidence Boundary.systemScope s
    ) := by
  intro h
  have hLocal :
      concreteEvidence Boundary.localScope
        { localValue := true, externalSafe := false } := by
    simp [concreteEvidence, localGuarantee]
  have hSystem :=
    h { localValue := true, externalSafe := false } hLocal
  simp [concreteEvidence, systemGuarantee] at hSystem

/--
Consequently, local evidence alone does not define a valid transport
rule to the system boundary.
-/
theorem concreteEvidence_transport_is_not_automatic :
    ¬ EvidenceTransport
      concreteEvidence
      Boundary.localScope
      Boundary.systemScope := by
  intro hTransport
  apply localEvidence_does_not_imply_systemEvidence
  intro s hLocal
  exact hTransport s hLocal

end DARM

#print axioms DARM.licensedExpansionAt_implies_broad
#print axioms DARM.narrowGuarantee_implies_broad_of_basis
#print axioms DARM.evidence_transport
#print axioms DARM.localEvidence_does_not_imply_systemEvidence
#print axioms DARM.concreteEvidence_transport_is_not_automatic
