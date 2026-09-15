/-
  R4e — BOUNDARY COMPOSITION ATTACK

  QUESTION:

  Can two individually justified assurance boundaries be composed into a
  larger assurance boundary without establishing the conditions introduced
  by their interaction?

  ISOLATION:

    Component A assurance      HOLDS
    Component B assurance      HOLDS
    Composed assurance         FAILS

  The failure is caused by an interaction dependency introduced only by
  composition.

  IMPORTANT:

  The interaction dependency is represented explicitly. It is not hidden
  inside an arbitrary unsafe definition.

  The structure is:

      Dep(A+B) = Dep(A) ∪ Dep(B) ∪ Dep(A,B)

  where Dep(A,B) is a genuinely new compositional dependency.

  The individual boundaries cover their own dependencies.

  Neither individual boundary covers Dep(A,B).

  Therefore individual assurance does not automatically transfer to the
  composed boundary.

  This artifact does not claim that compositional reasoning is novel.
  It tests whether boundary composition requires an explicit obligation for
  newly introduced cross-boundary dependencies.
-/

namespace GRBS.R4eBoundaryComposition

-- § 1  Components and traces

inductive Component where
  | A
  | B
deriving DecidableEq

inductive Tr where
  | A_safe
  | B_safe
  | AB_violation
deriving DecidableEq

/--
The component guarantees.

Each isolated component has a safe local execution.
The cross-boundary interaction has a distinct violation trace.
-/
def G_A : Tr → Prop
  | Tr.A_safe => True
  | _ => True

def G_B : Tr → Prop
  | Tr.B_safe => True
  | _ => True

/--
The composed guarantee.

The individual executions remain safe, but the cross-boundary interaction
violates the composed guarantee.
-/
def G_AB : Tr → Prop
  | Tr.A_safe => True
  | Tr.B_safe => True
  | Tr.AB_violation => False

-- § 2  Dependency space

inductive Dependency where
  | depA
  | depB
  | interactionAB
deriving DecidableEq

/--
Dependencies required by the individual assurance claims.
-/
def DepA : Dependency → Prop
  | Dependency.depA => True
  | _ => False

def DepB : Dependency → Prop
  | Dependency.depB => True
  | _ => False

/--
The composed assurance claim requires all three dependencies.

The third dependency exists only because the boundaries interact.
-/
def DepAB : Dependency → Prop
  | Dependency.depA => True
  | Dependency.depB => True
  | Dependency.interactionAB => True

-- § 3  Individual boundary coverage

/--
Boundary A controls its own dependency.
It does not claim authority over the cross-boundary interaction.
-/
def CovA : Dependency → Prop
  | Dependency.depA => True
  | _ => False

/--
Boundary B controls its own dependency.
It does not claim authority over the cross-boundary interaction.
-/
def CovB : Dependency → Prop
  | Dependency.depB => True
  | _ => False

/--
The composed boundary inherits the two local coverages but introduces
no additional coverage for the interaction dependency.
-/
def CovAB : Dependency → Prop
  | Dependency.depA => True
  | Dependency.depB => True
  | Dependency.interactionAB => False

-- § 4  Individual assurance

/--
A local boundary is justified when every dependency required by its claim
is covered by that boundary.
-/
def AssuredA : Prop :=
  ∀ d, DepA d → CovA d

def AssuredB : Prop :=
  ∀ d, DepB d → CovB d

/--
The composed claim requires coverage of every dependency introduced by
composition.
-/
def AssuredAB : Prop :=
  ∀ d, DepAB d → CovAB d

theorem A_is_assured :
    AssuredA := by
  intro d hd
  cases d with
  | depA => trivial
  | depB => contradiction
  | interactionAB => contradiction

theorem B_is_assured :
    AssuredB := by
  intro d hd
  cases d with
  | depA => contradiction
  | depB => trivial
  | interactionAB => contradiction

-- § 5  Composition introduces a new dependency

theorem interaction_is_compositional :
    DepAB Dependency.interactionAB
    ∧ ¬ DepA Dependency.interactionAB
    ∧ ¬ DepB Dependency.interactionAB := by
  constructor
  · trivial
  constructor
  · intro h
    cases h
  · intro h
    cases h

/--
The interaction dependency is not covered by either original boundary.
-/
theorem interaction_uncovered_locally :
    ¬ CovA Dependency.interactionAB
    ∧ ¬ CovB Dependency.interactionAB := by
  constructor
  · intro h
    cases h
  · intro h
    cases h

/--
The composed boundary also lacks coverage of the newly introduced
interaction dependency.
-/
theorem interaction_uncovered_composition :
    ¬ CovAB Dependency.interactionAB := by
  intro h
  cases h

-- § 6  The composed assurance fails

theorem composed_assurance_fails :
    ¬ AssuredAB := by
  intro h
  have hc : CovAB Dependency.interactionAB :=
    h Dependency.interactionAB trivial
  exact hc

-- § 7  The failure is not caused by either component individually

/--
Both original assurance claims hold simultaneously.
-/
theorem individual_assurance_holds :
    AssuredA ∧ AssuredB := by
  exact ⟨A_is_assured, B_is_assured⟩

/--
Individual assurance does not imply composed assurance in this witness.
-/
theorem unsupported_boundary_composition :
    AssuredA
    ∧ AssuredB
    ∧ ¬ AssuredAB := by
  exact ⟨A_is_assured, B_is_assured, composed_assurance_fails⟩

-- § 8  Explicit composition obligation

/--
The additional obligation introduced by composition is coverage of every
dependency that belongs to the composed assurance claim but to neither
original local claim.
-/
def BoundaryCompositionObligation : Prop :=
  ∀ d,
    DepAB d →
    (¬ DepA d ∧ ¬ DepB d) →
    CovAB d

/--
The obligation is not dischargeable in this witness.
-/
theorem boundary_composition_obligation_fails :
    ¬ BoundaryCompositionObligation := by
  intro h
  have hc :
      CovAB Dependency.interactionAB :=
    h Dependency.interactionAB trivial
      (by
        constructor
        · intro hd
          cases hd
        · intro hd
          cases hd)
  exact hc

/-!
  ## R4e discovery

  The witness establishes:

      AssuredA
      ∧ AssuredB
      ∧ ¬AssuredAB

  because composition introduces:

      interactionAB

  which is not present in either individual dependency set and is not
  covered by either individual boundary.

  Therefore:

      individual assurance
          ≠
      automatically composed assurance

  The newly discovered obligation is:

      newly introduced compositional dependency
          -> explicit coverage

  R4e therefore tests a different failure mode from R4a-R4d.

  R4a: scope substitution
  R4b: authority substitution
  R4c: locus substitution
  R4d: evidence substitution
  R4e: boundary composition

  No claim of universal compositional incompleteness is made here.
  The result is a machine-checked counterexample to automatic assurance
  transfer from individually justified boundaries to their composition.
-/

end GRBS.R4eBoundaryComposition
