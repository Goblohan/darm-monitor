/-
R19b: Semantic Dependency Bridge

PURPOSE

R19 established an independent semantic model for boundary-mediated transfer.
This module introduces the missing bridge between structural assurance
dependencies and semantic transition obligations.

The bridge is deliberately represented as an explicit adequacy relation.
It is not identified with GRBS and is not defined in terms of
`DARMTransferAdmissible`.

ARCHITECTURAL DISTINCTION

Structural layer:
  dependency -> coverage

Semantic layer:
  dependency -> transition obligation -> property preservation

Bridge:
  a discharged structural dependency is adequate for the corresponding
  semantic transition obligation.

The central result is therefore conditional:

  structural coverage
      +
  semantic discharge
      +
  discharge adequacy
      ->
  semantic preservation.

This module does not claim that structural coverage alone establishes
semantic safety.

NEGATIVE RESULT

A dependency may be covered structurally while its semantic obligation remains
undischarged. Therefore coverage alone cannot establish semantic preservation.
-/

namespace GRBS.R19bSemanticDependencyBridge

/-- A semantic transition obligation associated with a dependency. -/
structure SemanticDependency (D State : Type) where
  dependency : D
  source : State
  target : State

/-- Whether a semantic dependency obligation is relevant to the guarantee. -/
def Relevant
    {D State : Type}
    (r : SemanticDependency D State → Prop)
    (d : SemanticDependency D State) : Prop :=
  r d

/-- Structural boundary coverage of a dependency. -/
def Covered
    {D : Type}
    (covered : D → Prop)
    (d : D) : Prop :=
  covered d

/-- Semantic discharge of a dependency. -/
def Discharged
    {D : Type}
    (discharge : D → Prop)
    (d : D) : Prop :=
  discharge d

/--
Adequacy relation connecting a discharged structural dependency to its
semantic transition obligation.

The relation is intentionally an assumption supplied by the assurance
producer or refinement argument. DARM does not manufacture it.
-/
def DischargeAdequate
    {D State : Type}
    (discharge : D → Prop)
    (preserves : SemanticDependency D State → Prop) : Prop :=
  ∀ d, discharge d →
    ∀ sd : SemanticDependency D State,
      sd.dependency = d →
      preserves sd

/--
Every relevant semantic dependency must be structurally covered.
-/
def RelevantDependenciesCovered
    {D State : Type}
    (relevant : SemanticDependency D State → Prop)
    (covered : D → Prop) : Prop :=
  ∀ sd, relevant sd → covered sd.dependency

/--
Every structurally covered dependency is semantically discharged.
-/
def CoveredDependenciesDischarged
    {D : Type}
    (covered discharge : D → Prop) : Prop :=
  ∀ d, covered d → discharge d

/--
The semantic bridge theorem.

If:

  1. every relevant semantic dependency is covered,
  2. every covered dependency is discharged, and
  3. discharge is adequate for semantic preservation,

then every relevant semantic dependency is semantically preserved.
-/
theorem covered_and_discharged_imply_semantic_preservation
    {D State : Type}
    (relevant : SemanticDependency D State → Prop)
    (covered discharge : D → Prop)
    (preserves : SemanticDependency D State → Prop)
    (hCovered :
      RelevantDependenciesCovered relevant covered)
    (hDischarged :
      CoveredDependenciesDischarged covered discharge)
    (hAdequate :
      DischargeAdequate discharge preserves) :
    ∀ sd, relevant sd → preserves sd := by
  intro sd hRelevant
  have hCov : covered sd.dependency := hCovered sd hRelevant
  have hDis : discharge sd.dependency := hDischarged sd.dependency hCov
  exact hAdequate sd.dependency hDis sd rfl

/--
A semantic preservation condition that is independent of structural
coverage.
-/
def SemanticPreservation
    {D State : Type}
    (relevant : SemanticDependency D State → Prop)
    (preserves : SemanticDependency D State → Prop) : Prop :=
  ∀ sd, relevant sd → preserves sd

/--
Structural coverage alone is insufficient for semantic preservation.

There exists a dependency that is covered but not discharged, while its
semantic preservation obligation is false.
-/
theorem coverage_does_not_imply_semantic_preservation :
    ∃ (D : Type)
      (covered discharge : D → Prop)
      (preserves : D → Prop),
      (∀ d, covered d) ∧
      (∃ d, covered d ∧ ¬ discharge d ∧ ¬ preserves d) := by
  let D := Unit
  let covered : D → Prop := fun _ => True
  let discharge : D → Prop := fun _ => False
  let preserves : D → Prop := fun _ => False

  refine ⟨D, covered, discharge, preserves, ?_, ?_⟩
  · intro d
    trivial
  · refine ⟨(), ?_, ?_, ?_⟩
    · trivial
    · trivial
    · trivial

/--
The semantic bridge is not equivalent to structural coverage.

A covered dependency can fail semantic discharge, and therefore cannot satisfy
the bridge's adequacy premise.
-/
theorem covered_dependency_need_not_be_adequate :
    ∃ (D State : Type)
      (covered discharge : D → Prop)
      (preserves : SemanticDependency D State → Prop),
      (∀ d, covered d) ∧
      (¬ CoveredDependenciesDischarged covered discharge ∨
       ¬ DischargeAdequate discharge preserves) := by
  let D := Unit
  let State := Unit
  let covered : D → Prop := fun _ => True
  let discharge : D → Prop := fun _ => False
  let preserves : SemanticDependency D State → Prop := fun _ => False

  refine ⟨D, State, covered, discharge, preserves, ?_, ?_⟩
  · intro d
    trivial
  · left
    intro h
    have hd : discharge () := h () trivial
    exact hd

end GRBS.R19bSemanticDependencyBridge
