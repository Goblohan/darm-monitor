import IC1AbstractionGap

namespace GRBS.IC1RuntimeSemanticRepresentation

open GRBS.IC1AbstractionGap

/--
A runtime observation is semantically adequate for a request when the
observation contains enough information to establish the semantic
admissibility predicate.
-/
def RuntimeSemanticRepresentation
    (view : RuntimeView)
    (r : SemanticRequest) : Prop :=
  view = runtimeView r ∧ SemanticAdmissible r

/--
The current runtime projection cannot establish semantic admissibility
for every semantic request because distinct semantic requests can have
the same runtime view.
-/
theorem no_tool_only_semantic_representation :
    ¬ ∃ f : RuntimeView → Prop,
      ∀ r : SemanticRequest,
        f (runtimeView r) ↔ SemanticAdmissible r := by
  exact no_runtime_view_only_semantic_classifier

/--
Concrete witness showing that the runtime observation is identical
while the semantic admissibility status differs.
-/
theorem runtime_view_does_not_determine_semantics :
    ∃ (r₁ r₂ : SemanticRequest),
      runtimeView r₁ = runtimeView r₂ ∧
      SemanticAdmissible r₁ ∧
      ¬ SemanticAdmissible r₂ := by
  let r₁ : SemanticRequest :=
    { tool := 1
      argument := 0 }

  let r₂ : SemanticRequest :=
    { tool := 1
      argument := 1 }

  refine ⟨r₁, r₂, ?_, ?_, ?_⟩
  · exact same_runtime_view_same_tool r₁ r₂ rfl
  · simp [SemanticAdmissible, r₁]
  · simp [SemanticAdmissible, r₂]

end GRBS.IC1RuntimeSemanticRepresentation
