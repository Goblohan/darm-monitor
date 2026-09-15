import DarmMonitor.GuaranteeExpansion

namespace DARM

/--
An assurance basis for expanding a narrower guarantee to a broader
guarantee. The basis explicitly separates the assumption required for
the expansion from the evidence that establishes that assumption.
-/
structure ExpansionBasis
    {State Boundary : Type}
    (G : BoundaryIndexedGuarantee State Boundary)
    (narrow broad : Boundary) where
  Assumption : State → Prop
  Evidence : Prop
  narrow_implies_assumption :
    ∀ s, G narrow s → Assumption s
  evidence_establishes_assumption :
    ∀ s, Evidence → Assumption s
  assumption_implies_broad :
    ∀ s, Assumption s → G broad s

/--
A licensed guarantee expansion exists when the explicit evidence in
the assurance basis establishes the assumption needed for expansion.
-/
def LicensedGuaranteeExpansion
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    (narrow broad : Boundary)
    (basis : ExpansionBasis G narrow broad) : Prop :=
  basis.Evidence

/--
A licensed expansion entails the corresponding logical guarantee
expansion.
-/
theorem licensedExpansion_implies_guaranteeExpansion
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {narrow broad : Boundary}
    (basis : ExpansionBasis G narrow broad)
    (hLicensed : LicensedGuaranteeExpansion narrow broad basis) :
    GuaranteeExpansion G narrow broad := by
  intro s hNarrow
  exact basis.assumption_implies_broad s
    (basis.evidence_establishes_assumption s hLicensed)

/--
A licensed expansion cannot exist when logical guarantee expansion
already fails.
-/
theorem no_licensedExpansion_of_no_logicalExpansion
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {narrow broad : Boundary}
    (hNoExpansion : ¬ GuaranteeExpansion G narrow broad) :
    ∀ basis : ExpansionBasis G narrow broad,
      ¬ LicensedGuaranteeExpansion narrow broad basis := by
  intro basis hLicensed
  exact hNoExpansion
    (licensedExpansion_implies_guaranteeExpansion basis hLicensed)

/--
For the concrete boundary-expansion model, no assurance basis can
license expansion from the local guarantee to the system guarantee,
because logical expansion already fails.
-/
theorem no_licensed_local_to_system_expansion :
    ∀ basis :
      ExpansionBasis
        scopedGuarantee
        Boundary.localScope
        Boundary.systemScope,
      ¬ LicensedGuaranteeExpansion
        Boundary.localScope
        Boundary.systemScope
        basis := by
  intro basis
  exact no_licensedExpansion_of_no_logicalExpansion
    localGuarantee_does_not_expand_to_systemGuarantee basis

end DARM

#print axioms DARM.licensedExpansion_implies_guaranteeExpansion
#print axioms DARM.no_licensedExpansion_of_no_logicalExpansion
#print axioms DARM.no_licensed_local_to_system_expansion
