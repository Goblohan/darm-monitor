import IC1AbstractionGap
import R20DARMToSemanticCorrespondence
import IC1R20CausalCoverage
import R21RepairAdequacy

namespace GRBS.IC1R20CausalCoverageRefinement

open GRBS
open GRBS.IC1AbstractionGap
open GRBS.IC1R20CausalCoverage
open GRBS.R20DARMToSemanticCorrespondence
open GRBS.R21RepairAdequacy

/--
IC1/R20 refinement experiment:
the structural dependency is refined from tool identity to the
tool-and-argument identity required by the semantic domain.
-/
def refinedDependency (r : SemanticRequest) : Nat × Nat :=
  (r.tool, r.argument)

/-- The refined dependency projects back to the original tool identity. -/
def projectRuntimeDependency (d : Nat × Nat) : Nat :=
  d.1

/--
The IC1 argument-sensitive representation is a genuine refinement
of the original tool-only representation.
-/
theorem ic1_representation_refines_tool_identity :
    RepresentationRefines
      (fun r : SemanticRequest => r.tool)
      refinedDependency
      projectRuntimeDependency := by
  intro r
  rfl

/--
The IC1 refinement is strict: it preserves the old tool identity
while distinguishing two requests that the old representation
collapses.
-/
theorem ic1_refinement_is_strict :
    RepresentationRefines
        (fun r : SemanticRequest => r.tool)
        refinedDependency
        projectRuntimeDependency ∧
    (fun r : SemanticRequest => r.tool)
      { tool := 1, argument := 0 } =
    (fun r : SemanticRequest => r.tool)
      { tool := 1, argument := 1 } ∧
    refinedDependency { tool := 1, argument := 0 } ≠
      refinedDependency { tool := 1, argument := 1 } := by
  refine ⟨ic1_representation_refines_tool_identity, ?_, ?_⟩
  · rfl
  · intro h
    have hArg :
        (0 : Nat) = 1 :=
      congrArg Prod.snd h
    simp at hArg

/-- Refinement preserves the dependency observed by the original runtime. -/
theorem refined_dependency_projects_to_runtime_dependency
    (r : SemanticRequest) :
    projectRuntimeDependency (refinedDependency r) = r.tool := by
  rfl

/--
The refinement preserves the original tool identity while separating
the two semantically distinct IC1 witness requests.
-/
theorem refined_dependency_preserves_old_identity_and_new_distinction :
    projectRuntimeDependency (refinedDependency
      { tool := 1, argument := 0 }) =
        projectRuntimeDependency (refinedDependency
          { tool := 1, argument := 1 }) ∧
    refinedDependency { tool := 1, argument := 0 } ≠
      refinedDependency { tool := 1, argument := 1 } := by
  constructor
  · rfl
  · intro h
    have hArg :
        (0 : Nat) = 1 :=
      congrArg Prod.snd h
    simp at hArg

/--
The refined realization preserves both tool and argument identity.
-/
def realize : SemanticRealization (Nat × Nat) semanticSystem :=
  fun d =>
    { dependency := d
      source := { tool := d.1, argument := d.2 }
      target := { tool := d.1, argument := d.2 } }

def relevant :
    SemanticDependency (Nat × Nat) semanticSystem.State → Prop :=
  fun _ => True

/--
The argument-sensitive refinement provides R20 causal-domain coverage
for the semantic transitions in the IC1 witness domain.
-/
theorem refined_runtime_satisfies_r20_causal_coverage :
    RelevantRealizationCausalCoverage
        semanticSystem
        { mediated := fun x y => x = y }
        realize
        relevant
        causeable := by
  intro x y hCause
  rcases hCause with
    ⟨hx0, hy0⟩ | ⟨hx1, hy1⟩

  · refine ⟨(1, 0), ?_, ?_, ?_⟩
    · trivial
    · simpa [realize] using hx0.symm
    · simpa [realize] using hy0.symm

  · refine ⟨(1, 1), ?_, ?_, ?_⟩
    · trivial
    · simpa [realize] using hx1.symm
    · simpa [realize] using hy1.symm

/--
Concrete IC1 repair witness:
the coarse tool-only representation fails causal-domain coverage,
while the refined representation preserves the old identity and
restores causal-domain coverage over the same semantic domain.
-/
theorem ic1_representation_refinement_repairs_coverage :
    (¬ RelevantRealizationCausalCoverage
        GRBS.IC1R20CausalCoverage.semanticSystem
        { mediated := fun x y => x = y }
        GRBS.IC1R20CausalCoverage.realize
        GRBS.IC1R20CausalCoverage.relevant
        GRBS.IC1R20CausalCoverage.causeable) ∧
    RepresentationRefines
      (fun r : SemanticRequest => r.tool)
      refinedDependency
      projectRuntimeDependency ∧
    RelevantRealizationCausalCoverage
        semanticSystem
        { mediated := fun x y => x = y }
        realize
        relevant
        causeable := by
  refine ⟨?_, ic1_representation_refines_tool_identity, ?_⟩
  · exact GRBS.IC1R20CausalCoverage.tool_only_runtime_fails_r20_causal_coverage
  · exact refined_runtime_satisfies_r20_causal_coverage


end GRBS.IC1R20CausalCoverageRefinement

#print axioms
  GRBS.IC1R20CausalCoverageRefinement.refined_runtime_satisfies_r20_causal_coverage

#print axioms
  GRBS.IC1R20CausalCoverageRefinement.refined_dependency_projects_to_runtime_dependency

#print axioms
  GRBS.IC1R20CausalCoverageRefinement.refined_dependency_preserves_old_identity_and_new_distinction

#print axioms
  GRBS.IC1R20CausalCoverageRefinement.ic1_representation_refines_tool_identity


#print axioms
  GRBS.IC1R20CausalCoverageRefinement.ic1_refinement_is_strict


#print axioms
  GRBS.IC1R20CausalCoverageRefinement.ic1_representation_refinement_repairs_coverage
