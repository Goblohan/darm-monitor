import IC1AbstractionGap
import R20DARMToSemanticCorrespondence

namespace GRBS.IC1R20CausalCoverage

open GRBS
open GRBS.IC1AbstractionGap
open GRBS.R20DARMToSemanticCorrespondence

/--
IC1/R20 experiment:
the runtime dependency observes only the tool, while semantic states
retain both tool and argument.
-/
def runtimeDependency (r : SemanticRequest) : Nat :=
  r.tool

def semanticTransition
    (r : SemanticRequest) : SemanticRequest × SemanticRequest :=
  (r, r)

/--
The semantic system distinguishes requests by their full request identity.
-/
def semanticSystem : SemanticSystem :=
  { State := SemanticRequest
    Step := fun x y => x = y }

/--
A semantic transition is causeable when it is the identity transition
for one of the two IC1 witness requests.
-/
def causeable : SemanticCauseableTransition semanticSystem.State :=
  fun x y =>
    (x = { tool := 1, argument := 0 } ∧
     y = { tool := 1, argument := 0 }) ∨
    (x = { tool := 1, argument := 1 } ∧
     y = { tool := 1, argument := 1 })

/--
A tool-only realization has one structural dependency for tool 1.
It therefore realizes only one semantic request for that dependency.
-/
def realize : SemanticRealization Nat semanticSystem :=
  fun d =>
    { dependency := d
      source := { tool := d, argument := 0 }
      target := { tool := d, argument := 0 } }

def relevant : SemanticDependency Nat semanticSystem.State → Prop :=
  fun _ => True

/--
The tool-only realization cannot provide causal coverage for the
argument=1 semantic transition.
-/
theorem tool_only_runtime_fails_r20_causal_coverage :
    ¬ RelevantRealizationCausalCoverage
        semanticSystem
        { mediated := fun x y => x = y }
        realize
        relevant
        causeable := by
  intro hCoverage

  have hCause :
      causeable
        { tool := 1, argument := 1 }
        { tool := 1, argument := 1 } := by
    right
    exact ⟨rfl, rfl⟩

  obtain ⟨d, _hRelevant, hSource, hTarget⟩ :=
    hCoverage
      { tool := 1, argument := 1 }
      { tool := 1, argument := 1 }
      hCause

  have hSourceFalse :
      (realize d).source ≠
        { tool := 1, argument := 1 } := by
    intro h
    have hArgument :
        (0 : Nat) = 1 :=
      congrArg SemanticRequest.argument h
    simp at hArgument

  exact hSourceFalse hSource

end GRBS.IC1R20CausalCoverage

#print axioms
  GRBS.IC1R20CausalCoverage.tool_only_runtime_fails_r20_causal_coverage
