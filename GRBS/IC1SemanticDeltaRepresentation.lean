import DARMCoreCalculus
import IC1AbstractionGap
import R19BoundaryMediatedTransferSemantics
import R19bSemanticDependencyBridge

namespace GRBS.IC1SemanticDeltaRepresentation

open GRBS
open GRBS.DARMCoreCalculus
open GRBS.IC1AbstractionGap
open GRBS.R6GRBSDeltaBridge
open GRBS.R5AssuranceConservation
open GRBS.R19BoundaryMediatedTransferSemantics
open GRBS.R19bSemanticDependencyBridge

/--
A semantic request is represented by a dependency that preserves both
tool identity and argument identity.
-/
def semanticDependency
    (r : SemanticRequest) : Nat × Nat :=
  (r.tool, r.argument)

/--
The runtime observation preserves only the tool identity.
-/
def runtimeDependency
    (r : SemanticRequest) : Nat :=
  r.tool

/--
Two semantic requests with the same runtime dependency can nevertheless
have distinct semantic dependencies.
-/
theorem runtime_dependency_aliases_semantic_dependency :
    ∃ (r₁ r₂ : SemanticRequest),
      runtimeDependency r₁ = runtimeDependency r₂ ∧
      semanticDependency r₁ ≠ semanticDependency r₂ := by
  let r₁ : SemanticRequest :=
    { tool := 1
      argument := 0 }

  let r₂ : SemanticRequest :=
    { tool := 1
      argument := 1 }

  refine ⟨r₁, r₂, ?_, ?_⟩
  · rfl
  · simp [semanticDependency, r₁, r₂]

/--
A tool-only representation cannot distinguish the two semantic
dependencies in the witness above.
-/
theorem tool_only_representation_cannot_preserve_semantic_identity :
    ¬ ∀ r₁ r₂ : SemanticRequest,
        runtimeDependency r₁ = runtimeDependency r₂ →
        semanticDependency r₁ = semanticDependency r₂ := by
  intro h
  let r₁ : SemanticRequest :=
    { tool := 1
      argument := 0 }

  let r₂ : SemanticRequest :=
    { tool := 1
      argument := 1 }

  have hRuntime :
      runtimeDependency r₁ = runtimeDependency r₂ := by
    rfl

  have hSemantic :
      semanticDependency r₁ = semanticDependency r₂ :=
    h r₁ r₂ hRuntime

  simp [semanticDependency, r₁, r₂] at hSemantic

/--
Concrete DARM representation failure caused by the tool-only runtime
abstraction.

The runtime-visible tool identity is identical for the two requests,
but the semantic delta contains an argument-sensitive dependency that
is not represented by the runtime-level dependency relation.
-/
theorem tool_only_runtime_does_not_establish_delta_representation :
    ∃
      (F : Frame)
      (g : F.Guarantee)
      (s : F.System)
      (c : TransferCandidate F.Dependency),
      ¬ DeltaRepresented F g s c := by

  let F : Frame :=
    { Trace := Unit
      Guarantee := Unit
      System := Unit
      Boundary := Unit
      Locus := Unit
      Dependency := Nat × Nat
      Environment := Unit
      Safe := fun _ _ => True
      dep := fun _ _ d => d = (1, 0)
      cov := fun _ _ _ _ => True
      Envs := fun _ _ => True
      Traces := fun _ _ _ _ => True
      Perturbs := fun _ _ => True }

  let c : TransferCandidate F.Dependency :=
    { source := fun _ => False
      target := fun d => d = (1, 1)
      property := fun _ => True }

  refine ⟨F, (), (), c, ?_⟩

  intro hRepresented

  have hDelta :
      Delta F.Dependency c.source c.target (1, 1) := by
    simp [Delta, c]

  have hDep :
      F.dep () () (1, 1) :=
    hRepresented (1, 1) hDelta

  simp [F] at hDep

/--
The dependency relation induced by the runtime representation preserves
only the tool component of a semantic request.
-/
def runtimeInducedDependency
    (r : SemanticRequest)
    (d : Nat × Nat) : Prop :=
  d.1 = runtimeDependency r

/--
The runtime-induced dependency relation cannot preserve the full
argument-sensitive semantic dependency.
-/
theorem runtime_induced_dependency_is_semantically_incomplete :
    ∃ (r₁ r₂ : SemanticRequest),
      runtimeDependency r₁ = runtimeDependency r₂ ∧
      semanticDependency r₁ ≠ semanticDependency r₂ ∧
      runtimeInducedDependency r₁ (semanticDependency r₂) := by
  let r₁ : SemanticRequest :=
    { tool := 1
      argument := 0 }

  let r₂ : SemanticRequest :=
    { tool := 1
      argument := 1 }

  refine ⟨r₁, r₂, ?_, ?_, ?_⟩
  · rfl
  · simp [semanticDependency, r₁, r₂]
  · simp [runtimeInducedDependency, runtimeDependency, semanticDependency, r₁, r₂]


/--
R19's central adequacy schema does not itself require
DependencyRepresentation.

Thus the schema can hold even when a semantically relevant dependency is
not represented by either the source or target domain.
-/
theorem r19_adequacy_does_not_require_dependency_representation :
    ∃
      (D : Type)
      (source target relevant covered discharge : D → Prop),
      DARMToSemanticAdequacy
        D relevant covered discharge True ∧
      ¬ DependencyRepresentation D source target relevant := by

  let D := Unit

  let source : D → Prop := fun _ => False
  let target : D → Prop := fun _ => False
  let relevant : D → Prop := fun _ => True
  let covered : D → Prop := fun _ => True
  let discharge : D → Prop := fun _ => True

  refine ⟨D, source, target, relevant, covered, discharge, ?_, ?_⟩

  · constructor
    · intro d hd
      trivial
    · constructor
      · intro d hd
        trivial
      · intro d hd
        trivial

  · intro hRepresentation
    have h := hRepresentation ()
    simp [source, target, relevant] at h

/--
R19b's discharge adequacy relation does not by itself require a structural
dependency to preserve semantic identity.

Two distinct semantic obligations may share the same structural dependency
while both satisfy the stated discharge adequacy condition.
-/
theorem discharge_adequacy_does_not_imply_semantic_identity :
    ∃
      (D State : Type)
      (discharge : D → Prop)
      (preserves : SemanticDependency D State → Prop),
      DischargeAdequate discharge preserves ∧
      ∃ sd₁ sd₂ : SemanticDependency D State,
        sd₁.dependency = sd₂.dependency ∧
        sd₁ ≠ sd₂ := by

  let D := Unit
  let State := Bool
  let discharge : D → Prop := fun _ => True
  let preserves : SemanticDependency D State → Prop := fun _ => True

  let sd₁ : SemanticDependency D State :=
    { dependency := ()
      source := false
      target := false }

  let sd₂ : SemanticDependency D State :=
    { dependency := ()
      source := false
      target := true }

  refine ⟨D, State, discharge, preserves, ?_, sd₁, sd₂, ?_, ?_⟩

  · intro d hd sd hEq
    trivial

  · rfl

  · intro hEq
    have hTarget :
        sd₁.target = sd₂.target :=
      congrArg SemanticDependency.target hEq
    simp [sd₁, sd₂] at hTarget

end GRBS.IC1SemanticDeltaRepresentation


#print axioms GRBS.IC1SemanticDeltaRepresentation.tool_only_runtime_does_not_establish_delta_representation

#print axioms GRBS.IC1SemanticDeltaRepresentation.runtime_induced_dependency_is_semantically_incomplete

#print axioms GRBS.IC1SemanticDeltaRepresentation.r19_adequacy_does_not_require_dependency_representation

#print axioms GRBS.IC1SemanticDeltaRepresentation.discharge_adequacy_does_not_imply_semantic_identity
