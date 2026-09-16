import DarmMonitor.BoundaryIndexedGuarantee
import R5DomainPolymorphism

namespace DARM

/--
A boundary-indexed representation of an assurance domain.

For each DARM boundary, `D` identifies the assurance objects that
are considered relevant at that boundary.

The assurance-object type `X` is intentionally independent of
`BoundaryIndexedGuarantee`. This prevents the DARM boundary itself
from being identified with the R5 assurance-object domain.
-/
def BoundaryAssuranceDomain
    (Boundary X : Type) :=
  Boundary → X → Prop

/--
The assurance-relevant delta induced by a pair of DARM boundaries.

An object belongs to the delta exactly when it is represented in the
target boundary's assurance domain but not in the source boundary's
assurance domain.

This delegates the delta definition to the generic R5 conservation
kernel rather than duplicating it.
-/
def BoundaryDelta
    {Boundary X : Type}
    (D : BoundaryAssuranceDomain Boundary X)
    (source target : Boundary) : X → Prop :=
  GRBS.R5DomainPolymorphism.Delta
    X
    (D source)
    (D target)

/--
The R5 conservation obligation induced by a DARM boundary transition.

This is deliberately only a representation of the obligation.
It does not assert that the obligation is discharged.
-/
def BoundaryDeltaObligation
    {Boundary X : Type}
    (D : BoundaryAssuranceDomain Boundary X)
    (source target : Boundary)
    (property : X → Prop) : Prop :=
  GRBS.R5DomainPolymorphism.DeltaObligation
    X
    (D source)
    (D target)
    property

/--
Boundary delta membership unfolds directly to the R5 delta condition.
-/
theorem boundaryDelta_iff
    {Boundary X : Type}
    (D : BoundaryAssuranceDomain Boundary X)
    (source target : Boundary)
    (x : X) :
    BoundaryDelta D source target x ↔
      D target x ∧ ¬ D source x := by
  rfl

/--
The boundary-indexed obligation is exactly the corresponding
R5 delta obligation.
-/
theorem boundaryDeltaObligation_iff
    {Boundary X : Type}
    (D : BoundaryAssuranceDomain Boundary X)
    (source target : Boundary)
    (property : X → Prop) :
    BoundaryDeltaObligation D source target property ↔
      GRBS.R5DomainPolymorphism.DeltaObligation
        X
        (D source)
        (D target)
        property := by
  rfl

/--
A discharged boundary delta obligation transfers the source
assurance property to the target boundary.

This is the DARM-side instantiation of the generic R5 conservation
kernel. It does not assert that the delta obligation is discharged.
-/
theorem target_assured_of_source_and_boundaryDeltaObligation
    {Boundary X : Type}
    (D : BoundaryAssuranceDomain Boundary X)
    (source target : Boundary)
    (property : X → Prop)
    (hSource :
      GRBS.R5DomainPolymorphism.SourceAssured
        X
        (D source)
        property)
    (hDelta :
      BoundaryDeltaObligation
        D
        source
        target
        property) :
    GRBS.R5DomainPolymorphism.TargetAssured
      X
      (D target)
      property := by
  exact
    GRBS.R5DomainPolymorphism.target_assured_of_source_and_delta
      X
      (D source)
      (D target)
      property
      hSource
      hDelta

/--
An assurance-relevant object introduced by a boundary transition
cannot support target assurance when the required property is false
for that object.

This is the DARM-side form of the generic R5 negative conservation
kernel. It identifies an undischarged delta witness without asserting
that every DARM boundary transition has such a witness.
-/
theorem boundaryDelta_witness_blocks_target_assurance
    {Boundary X : Type}
    (D : BoundaryAssuranceDomain Boundary X)
    (source target : Boundary)
    (property : X → Prop)
    (x₀ : X)
    (hIntroduced :
      BoundaryDelta D source target x₀)
    (hUnestablished :
      ¬ property x₀) :
    ¬ GRBS.R5DomainPolymorphism.TargetAssured
      X
      (D target)
      property := by
  apply GRBS.R5DomainPolymorphism.target_not_assured_of_bad_delta
      X
      (D source)
      (D target)
      property
      x₀
  · exact hIntroduced
  · exact hUnestablished

end DARM

#print axioms DARM.boundaryDelta_iff
#print axioms DARM.boundaryDeltaObligation_iff
#print axioms DARM.target_assured_of_source_and_boundaryDeltaObligation


#print axioms DARM.boundaryDelta_witness_blocks_target_assurance
