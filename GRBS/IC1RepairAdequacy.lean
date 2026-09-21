import IC1R20CausalCoverage_refinement

namespace GRBS.IC1RepairAdequacy

open GRBS
open GRBS.IC1AbstractionGap
open GRBS.IC1R20CausalCoverage
open GRBS.IC1R20CausalCoverageRefinement
open GRBS.R20DARMToSemanticCorrespondence

/--
The refined representation and its semantic realization agree with
the semantic request represented by that dependency.
-/
def RealizationAgreesWithRequest
    (representation : SemanticRequest → Nat × Nat)
    (realize :
      SemanticRealization (Nat × Nat) semanticSystem) : Prop :=
  ∀ r,
    (realize (representation r)).source = r ∧
    (realize (representation r)).target = r

/--
Every causeable semantic transition is represented by a request in
the semantic request domain.

This is a domain-completeness condition, not a coverage predicate.
-/
def CauseableRequestComplete : Prop :=
  ∀ x y,
    causeable x y →
    ∃ r : SemanticRequest,
      r = x ∧ r = y

/--
For the IC1 semantic model, the refined realization agrees with the
semantic request it represents.
-/
theorem refined_realization_agrees_with_request :
    RealizationAgreesWithRequest
      refinedDependency
      realize := by
  intro r
  constructor <;> rfl

/--
The IC1 causeable domain is complete with respect to SemanticRequest.
-/
theorem ic1_causeable_request_complete :
    CauseableRequestComplete := by
  intro x y hCause
  rcases hCause with
    ⟨hx0, hy0⟩ | ⟨hx1, hy1⟩
  · refine ⟨x, rfl, ?_⟩
    exact hx0.trans hy0.symm
  · refine ⟨x, rfl, ?_⟩
    exact hx1.trans hy1.symm

/--
Non-circular semantic repair condition:

if a refined representation is semantically realized exactly as the
request it represents, and every causeable transition is represented
by such a request, then the resulting realization has causal coverage.
-/
theorem realization_agreement_plus_request_completeness_implies_causal_coverage
    (representation : SemanticRequest → Nat × Nat)
    (realize' :
      SemanticRealization (Nat × Nat) semanticSystem)
    (hAgreement :
      RealizationAgreesWithRequest representation realize')
    (hComplete :
      CauseableRequestComplete) :
    RelevantRealizationCausalCoverage
      semanticSystem
      { mediated := fun x y => x = y }
      realize'
      (fun _ => True)
      causeable := by
  intro x y hCause

  obtain ⟨r, hrx, hry⟩ :=
    hComplete x y hCause

  obtain ⟨hSource, hTarget⟩ :=
    hAgreement r

  refine ⟨representation r, trivial, ?_, ?_⟩
  · exact hSource.trans hrx
  · exact hTarget.trans hry

/--
The concrete IC1 refinement satisfies both independent semantic
repair conditions.
-/
theorem ic1_refined_repair_adequacy :
    RealizationAgreesWithRequest
        refinedDependency
        realize ∧
    CauseableRequestComplete := by
  exact ⟨
    refined_realization_agrees_with_request,
    ic1_causeable_request_complete
  ⟩

end GRBS.IC1RepairAdequacy

#print axioms
  GRBS.IC1RepairAdequacy.refined_realization_agrees_with_request

#print axioms
  GRBS.IC1RepairAdequacy.ic1_causeable_request_complete

#print axioms
  GRBS.IC1RepairAdequacy.realization_agreement_plus_request_completeness_implies_causal_coverage

#print axioms
  GRBS.IC1RepairAdequacy.ic1_refined_repair_adequacy
