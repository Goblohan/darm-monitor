import DarmMonitor.BoundaryExpansion

namespace DARM

/--
A guarantee expansion claims that satisfaction of a guarantee at a
narrower boundary entails satisfaction of the same scoped guarantee
at a broader boundary.
-/
def GuaranteeExpansion
    {State Boundary : Type}
    (G : BoundaryIndexedGuarantee State Boundary)
    (narrow broad : Boundary) : Prop :=
  ∀ s, G narrow s → G broad s

/--
A concrete guarantee expansion is valid when the narrower guarantee
logically entails the broader guarantee for every state.
-/
def ValidGuaranteeExpansion
    {State Boundary : Type}
    (G : BoundaryIndexedGuarantee State Boundary)
    (narrow broad : Boundary) : Prop :=
  GuaranteeExpansion G narrow broad

/--
Failure of guarantee expansion is witnessed by a state satisfying
the narrower guarantee but violating the broader guarantee.
-/
theorem not_guaranteeExpansion_of_witness
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {narrow broad : Boundary}
    (s : State)
    (hNarrow : G narrow s)
    (hNotBroad : ¬ G broad s) :
    ¬ GuaranteeExpansion G narrow broad := by
  intro hExpansion
  exact hNotBroad (hExpansion s hNarrow)

/--
The local guarantee in the boundary-expansion model does not
logically expand to the broader system guarantee.
-/
theorem localGuarantee_does_not_expand_to_systemGuarantee :
    ¬ GuaranteeExpansion
      scopedGuarantee
      Boundary.localScope
      Boundary.systemScope := by
  apply not_guaranteeExpansion_of_witness
    (s := { localValue := true, externalSafe := false })
  · simp [scopedGuarantee, localGuarantee]
  · simp [scopedGuarantee, systemGuarantee]

/--
The failure of logical guarantee expansion is independent of any
claim about representation adequacy.
-/
theorem local_guarantee_expansion_failure :
    ¬ GuaranteeExpansion
      scopedGuarantee
      Boundary.localScope
      Boundary.systemScope := by
  exact localGuarantee_does_not_expand_to_systemGuarantee

end DARM

#print axioms DARM.not_guaranteeExpansion_of_witness
#print axioms DARM.localGuarantee_does_not_expand_to_systemGuarantee
#print axioms DARM.local_guarantee_expansion_failure
