import IC1RuntimeSemantics
import R21RepairAdequacy
import R22RuntimeSemanticCorrespondence

namespace GRBS.R22RuntimeImplementationCorrespondence

open GRBS
open GRBS.IC1RuntimeSemantics
open GRBS.R21RepairAdequacy
open GRBS.R22RuntimeSemanticCorrespondence

/--
R22-IC — Runtime implementation correspondence.

This module formalizes the observable authorization boundary of the
current DARM Guard integration.

The integration supplies only the tool name to `DARMGuard.check`.
Arguments are passed only to the underlying tool after authorization.
The purpose here is to characterize the resulting representation gap
against an argument-sensitive semantic authorization predicate.
-/
structure RuntimeInvocation where
  tool : String
  argument : Nat
  deriving DecidableEq

/--
The authorization observation exposed by the current Python integration.

`_GuardedTool.run` calls:

  guard.check({self.name})

and therefore exposes only the tool identity to the authorization
kernel.
-/
def currentRuntimeRequest
    (r : RuntimeInvocation) : Finset String :=
  {r.tool}

/-- Argument-sensitive semantic authorization used by this experiment. -/
def semanticAuthorized
    (r : RuntimeInvocation) : Prop :=
  r.argument = 0

/-- Two invocations with the same tool but different arguments collapse
    to the same current runtime authorization observation. -/
theorem current_runtime_observation_collapses_semantic_distinction :
    currentRuntimeRequest
      { tool := "demo", argument := 0 } =
    currentRuntimeRequest
      { tool := "demo", argument := 1 } := by
  rfl

/-- The two collapsed invocations nevertheless have different
    semantic authorization status. -/
theorem collapsed_invocations_have_different_semantic_authority :
    semanticAuthorized
        { tool := "demo", argument := 0 } ∧
    ¬ semanticAuthorized
        { tool := "demo", argument := 1 } := by
  constructor <;> simp [semanticAuthorized]

/--
No authorization classifier over the current runtime observation can
exactly represent this argument-sensitive semantic authorization
predicate.
-/
theorem no_current_runtime_semantic_authorizer :
    ¬ ∃ classifier : Finset String → Prop,
        ∀ r,
          classifier (currentRuntimeRequest r) ↔
            semanticAuthorized r := by
  rintro ⟨classifier, hClassifier⟩
  have hSame :
      classifier
          (currentRuntimeRequest
            { tool := "demo", argument := 0 }) ↔
      classifier
          (currentRuntimeRequest
            { tool := "demo", argument := 1 }) := by
    rw [current_runtime_observation_collapses_semantic_distinction]
  have hZero :
      classifier
          (currentRuntimeRequest
            { tool := "demo", argument := 0 }) := by
    exact (hClassifier
      { tool := "demo", argument := 0 }).mpr (by
        simp [semanticAuthorized])
  have hOne :
      classifier
          (currentRuntimeRequest
            { tool := "demo", argument := 1 }) := by
    exact hSame.mp hZero
  have hForbidden :
      ¬ classifier
          (currentRuntimeRequest
            { tool := "demo", argument := 1 }) := by
    intro h
    have hSemantic :=
      (hClassifier
        { tool := "demo", argument := 1 }).mp h
    simp [semanticAuthorized] at hSemantic
  exact hForbidden hOne

/--
The refined invocation representation preserves the current tool
identity while retaining the argument needed by the semantic layer.
-/
def refinedRuntimeRequest
    (r : RuntimeInvocation) : String × Nat :=
  (r.tool, r.argument)

/-- Projection from the refined representation back to the current
    runtime authorization representation. -/
def projectRefinedRuntimeRequest
    (r : String × Nat) : Finset String :=
  {r.1}

/-- The refined representation is a representation refinement in the
    generic R21 sense. -/
theorem refined_runtime_request_refines_current_runtime_request :
    RepresentationRefines
      currentRuntimeRequest
      refinedRuntimeRequest
      projectRefinedRuntimeRequest := by
  intro r
  rfl

/-- The refinement preserves the old runtime tool identity. -/
theorem refined_runtime_request_preserves_tool_identity :
    ∀ r,
      projectRefinedRuntimeRequest
        (refinedRuntimeRequest r) =
      currentRuntimeRequest r := by
  intro r
  rfl

/-- The refined representation distinguishes the two previously
    indistinguishable semantic invocations. -/
theorem refined_runtime_request_distinguishes_arguments :
    refinedRuntimeRequest
        { tool := "demo", argument := 0 } ≠
    refinedRuntimeRequest
        { tool := "demo", argument := 1 } := by
  intro h
  cases h

/-- The refined representation exactly recovers the experiment's
    argument-sensitive semantic authorization predicate. -/
def refinedSemanticClassifier
    (r : String × Nat) : Prop :=
  r.2 = 0

theorem refined_classifier_recovers_semantic_authorization :
    ∀ r,
      refinedSemanticClassifier
        (refinedRuntimeRequest r) ↔
      semanticAuthorized r := by
  intro r
  rfl

/--
The refined representation therefore rejects the semantic bypass that
the current tool-only observation cannot distinguish.
-/
theorem refined_representation_rejects_forbidden_argument :
    ¬ refinedSemanticClassifier
        (refinedRuntimeRequest
          { tool := "demo", argument := 1 }) := by
  simp [refinedSemanticClassifier, refinedRuntimeRequest]

/--
The current runtime's executable authorization predicate remains
tool-level. This theorem records the correspondence boundary rather
than asserting that the Python implementation itself is verified.
-/
def currentRuntimeAdmission
    (tool : String) : Prop :=
  tool = "demo"

theorem current_runtime_admits_both_semantic_cases :
    currentRuntimeAdmission "demo" ∧
    currentRuntimeAdmission "demo" := by
  constructor <;> rfl

theorem current_runtime_admission_does_not_imply_semantic_authorization :
    ∃ r,
      currentRuntimeAdmission r.tool ∧
      ¬ semanticAuthorized r := by
  refine ⟨{ tool := "demo", argument := 1 }, ?_⟩
  constructor
  · rfl
  · simp [semanticAuthorized]

/--
The implementation-level gap is exactly the missing correspondence:
tool-level runtime admission cannot imply the richer semantic
authorization predicate.
-/
theorem current_runtime_lacks_r22_semantic_correspondence :
    ¬ ∀ r,
        currentRuntimeAdmission r.tool →
        semanticAuthorized r := by
  intro h
  have hBad := h { tool := "demo", argument := 1 }
  simp [currentRuntimeAdmission, semanticAuthorized] at hBad

#print axioms current_runtime_observation_collapses_semantic_distinction
#print axioms collapsed_invocations_have_different_semantic_authority
#print axioms no_current_runtime_semantic_authorizer
#print axioms refined_runtime_request_refines_current_runtime_request
#print axioms refined_runtime_request_preserves_tool_identity
#print axioms refined_runtime_request_distinguishes_arguments
#print axioms refined_classifier_recovers_semantic_authorization
#print axioms refined_representation_rejects_forbidden_argument
#print axioms current_runtime_admission_does_not_imply_semantic_authorization
#print axioms current_runtime_lacks_r22_semantic_correspondence

end GRBS.R22RuntimeImplementationCorrespondence
