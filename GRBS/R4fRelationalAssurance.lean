/-
  R4f — RELATIONAL / EMERGENT ASSURANCE ATTACK

  QUESTION:

  Can two individually assured objects compose into an assurance failure
  because of a property that exists only over their relation?

  ISOLATION:

    Individual object A       CONSTANT
    Individual object B       CONSTANT
    Individual properties     CONSTANT
    Scope                     CONSTANT
    Authority                 CONSTANT
    Enforcement locus         CONSTANT
    Evidence                  CONSTANT

    The assurance-relevant object becomes relational:

        (A, B)

  This attacks the possibility that R5's delta formulation is restricted
  to unary objects.

  The intended result is deliberately non-trivial:

      P(A)
      P(B)

  while:

      R(A,B) = false

  We then test whether R5 can represent the relational assurance object
  without modification by choosing:

      X := Object × Object

  The experiment is therefore a test of domain polymorphism, not a claim
  that R5 is intrinsically relational.
-/

import R5AssuranceConservation

namespace GRBS.R4fRelationalAssurance

-- § 1 Objects

inductive Object where
  | A
  | B
deriving DecidableEq

/--
The assurance object is a pair of objects.

The relation itself is the object whose assurance is being transferred.
-/
abbrev Rel := Object × Object

-- § 2 Individual properties

/--
Both objects are individually safe.
-/
def IndividuallySafe : Object → Prop
  | Object.A => True
  | Object.B => True

theorem A_individually_safe :
    IndividuallySafe Object.A := by
  trivial

theorem B_individually_safe :
    IndividuallySafe Object.B := by
  trivial

/--
The relational property.

The pair (A,B) is unsafe because the two objects interact in a forbidden
combination.

All other pairs are safe in this minimal witness.
-/
def RelationalSafe : Rel → Prop
  | (Object.A, Object.B) => False
  | _ => True

/--
The emergent interaction is unsafe.
-/
theorem AB_relationally_unsafe :
    ¬ RelationalSafe (Object.A, Object.B) := by
  intro h
  exact h

/--
The unsafe relation is not attributable to either object individually.
-/
theorem individual_safety_does_not_imply_relational_safety :
    IndividuallySafe Object.A
    ∧ IndividuallySafe Object.B
    ∧ ¬ RelationalSafe (Object.A, Object.B) := by
  exact ⟨A_individually_safe, B_individually_safe,
    AB_relationally_unsafe⟩

-- § 3 Source and target relational domains

/--
The source assurance domain contains only individually represented objects.

For the relational experiment, the source contains the reflexive
self-relations.

The pair (A,B) is not part of the source assurance domain.
-/
def SourceDomain : Rel → Prop
  | (Object.A, Object.A) => True
  | (Object.B, Object.B) => True
  | _ => False

/--
The target assurance domain introduces the interaction relation (A,B).
-/
def TargetDomain : Rel → Prop
  | (Object.A, Object.A) => True
  | (Object.B, Object.B) => True
  | (Object.A, Object.B) => True
  | _ => False

/--
The relational assurance property required over the target domain.
-/
def Property : Rel → Prop :=
  RelationalSafe

-- § 4 R5 delta

open GRBS.R5AssuranceConservation

def R5Delta : Rel → Prop :=
  Delta Rel SourceDomain TargetDomain

def R5DeltaObligation : Prop :=
  DeltaObligation
    Rel
    SourceDomain
    TargetDomain
    Property

/--
The emergent interaction (A,B) is an R5 delta.

It is admitted by the target domain but absent from the source domain.
-/
theorem AB_is_r5_delta :
    R5Delta (Object.A, Object.B) := by
  constructor
  · trivial
  · intro h
    exact h

/--
The R5 delta obligation fails on the emergent interaction.
-/
theorem relational_delta_obligation_fails :
    ¬ R5DeltaObligation := by
  intro h
  exact AB_relationally_unsafe (h (Object.A, Object.B)
    ⟨trivial, fun h => h⟩)

/--
The relational failure is therefore represented by R5 without modifying
the R5 definitions.

The assurance-relevant object is simply the relation itself.
-/
theorem relational_failure_is_r5_delta_failure :
    R5Delta (Object.A, Object.B)
    ∧ ¬ R5DeltaObligation := by
  exact ⟨AB_is_r5_delta, relational_delta_obligation_fails⟩

-- § 5 Source assurance

/--
The source domain is safe.

Both source relations satisfy the relational property.
-/
theorem source_is_assured :
    ∀ r, SourceDomain r → Property r := by
  intro r hr
  cases r with
  | mk x y =>
    cases x <;> cases y <;> simp_all [SourceDomain, Property, RelationalSafe]

/--
The target domain is not assured because the emergent relation is unsafe.
-/
theorem target_is_not_assured :
    ¬ (∀ r, TargetDomain r → Property r) := by
  intro h
  exact AB_relationally_unsafe
    (h (Object.A, Object.B) trivial)

/--
The complete R4f witness.
-/
theorem unsupported_relational_composition :
    (∀ r, SourceDomain r → Property r)
    ∧ R5Delta (Object.A, Object.B)
    ∧ ¬ R5DeltaObligation
    ∧ ¬ (∀ r, TargetDomain r → Property r) := by
  exact ⟨
    source_is_assured,
    AB_is_r5_delta,
    relational_delta_obligation_fails,
    target_is_not_assured
  ⟩

end GRBS.R4fRelationalAssurance
