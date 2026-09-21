import IC1AbstractionGap
import R20DARMToSemanticCorrespondence
import IC1R20CausalCoverage
import IC1R20CausalCoverage_refinement

namespace GRBS.IC1RepresentationRefinementNegative

open GRBS
open GRBS.IC1AbstractionGap
open GRBS.R20DARMToSemanticCorrespondence

def badRefinedRealize :
    SemanticRealization (Nat × Nat)
      _root_.GRBS.IC1R20CausalCoverage.semanticSystem :=
  fun d =>
    { dependency := d
      source := { tool := d.1, argument := 0 }
      target := { tool := d.1, argument := 0 } }

def refinedRelevant :
    SemanticDependency (Nat × Nat)
      _root_.GRBS.IC1R20CausalCoverage.semanticSystem.State → Prop :=
  fun _ => True

theorem bad_refined_realize_is_faithful :
    RealizationFaithful badRefinedRealize := by
  intro d
  rfl

theorem representation_refinement_does_not_imply_causal_coverage :
    _root_.GRBS.R21RepairAdequacy.RepresentationRefines
        (fun r : SemanticRequest => r.tool)
        _root_.GRBS.IC1R20CausalCoverageRefinement.refinedDependency
        _root_.GRBS.IC1R20CausalCoverageRefinement.projectRuntimeDependency ∧
    ¬ RelevantRealizationCausalCoverage
        _root_.GRBS.IC1R20CausalCoverage.semanticSystem
        { mediated := fun x y => x = y }
        badRefinedRealize
        refinedRelevant
        _root_.GRBS.IC1R20CausalCoverage.causeable := by

  refine ⟨
    _root_.GRBS.IC1R20CausalCoverageRefinement.ic1_representation_refines_tool_identity,
    ?_
  ⟩

  intro hCoverage

  have hCause :
      _root_.GRBS.IC1R20CausalCoverage.causeable
        { tool := 1, argument := 1 }
        { tool := 1, argument := 1 } := by
    right
    exact ⟨rfl, rfl⟩

  obtain ⟨d, _hRelevant, _hSource, hTarget⟩ :=
    hCoverage
      { tool := 1, argument := 1 }
      { tool := 1, argument := 1 }
      hCause

  have hTargetFixed :
      (badRefinedRealize d).target =
        { tool := d.1, argument := 0 } := by
    rfl

  have hTargetArgument :
      ({ tool := 1, argument := 1 } : SemanticRequest).argument =
        (badRefinedRealize d).target.argument := by
    exact congrArg SemanticRequest.argument hTarget.symm

  rw [hTargetFixed] at hTargetArgument
  simp at hTargetArgument

end GRBS.IC1RepresentationRefinementNegative

#print axioms
  GRBS.IC1RepresentationRefinementNegative.bad_refined_realize_is_faithful

#print axioms
  GRBS.IC1RepresentationRefinementNegative.representation_refinement_does_not_imply_causal_coverage
