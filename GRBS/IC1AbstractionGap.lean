import Mathlib.Data.Finset.Basic

namespace GRBS.IC1AbstractionGap

/-- What the current runtime authorization layer observes. -/
structure RuntimeView where
  tools : Finset Nat
deriving DecidableEq

/-- A richer request containing information invisible to the current runtime. -/
structure SemanticRequest where
  tool : Nat
  argument : Nat
deriving DecidableEq

/-- Current runtime projection: only the tool identity is visible. -/
def runtimeView (r : SemanticRequest) : RuntimeView :=
  { tools := {r.tool} }

/-- A deliberately richer semantic boundary. -/
def SemanticAdmissible (r : SemanticRequest) : Prop :=
  r.argument = 0

/-- Tool-name-level authorization used by the current runtime abstraction. -/
def RuntimeToolAuthorized
    (authorized : Finset Nat)
    (r : SemanticRequest) : Prop :=
  r.tool ∈ authorized

/-- Same tool means identical runtime observations. -/
theorem same_runtime_view_same_tool
    (r₁ r₂ : SemanticRequest)
    (hTool : r₁.tool = r₂.tool) :
    runtimeView r₁ = runtimeView r₂ := by
  simp [runtimeView, hTool]

/--
Concrete abstraction-gap witness.

The two requests expose exactly the same tool to the runtime,
but differ at the semantic boundary.
-/
theorem semantic_abstraction_gap :
    ∃ (r₁ r₂ : SemanticRequest) (authorized : Finset Nat),
      r₁.tool = r₂.tool ∧
      RuntimeToolAuthorized authorized r₁ ∧
      RuntimeToolAuthorized authorized r₂ ∧
      runtimeView r₁ = runtimeView r₂ ∧
      SemanticAdmissible r₁ ∧
      ¬ SemanticAdmissible r₂ := by

  let r₁ : SemanticRequest :=
    { tool := 1
      argument := 0 }

  let r₂ : SemanticRequest :=
    { tool := 1
      argument := 1 }

  let authorized : Finset Nat := {1}

  refine ⟨r₁, r₂, authorized, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [RuntimeToolAuthorized, authorized, r₁]
  · simp [RuntimeToolAuthorized, authorized, r₂]
  · exact same_runtime_view_same_tool r₁ r₂ rfl
  · simp [SemanticAdmissible, r₁]
  · simp [SemanticAdmissible, r₂]

/--
No classifier whose input is only the current runtime view can
reproduce this richer semantic boundary for every request.
-/
theorem no_runtime_view_only_semantic_classifier :
    ¬ ∃ f : RuntimeView → Prop,
      ∀ r : SemanticRequest,
        f (runtimeView r) ↔ SemanticAdmissible r := by

  intro h
  obtain ⟨f, hf⟩ := h

  let r₁ : SemanticRequest :=
    { tool := 1
      argument := 0 }

  let r₂ : SemanticRequest :=
    { tool := 1
      argument := 1 }

  have hView :
      runtimeView r₁ = runtimeView r₂ :=
    same_runtime_view_same_tool r₁ r₂ rfl

  have h1 :
      f (runtimeView r₁) :=
    (hf r₁).mpr (by
      simp [SemanticAdmissible, r₁])

  have h2 :
      f (runtimeView r₂) := by
    rw [← hView]
    exact h1

  have hNot :
      ¬ f (runtimeView r₂) := by
    intro hf2
    have hSemantic : SemanticAdmissible r₂ :=
      (hf r₂).mp hf2
    simp [SemanticAdmissible, r₂] at hSemantic

  exact hNot h2

end GRBS.IC1AbstractionGap

#print axioms GRBS.IC1AbstractionGap.semantic_abstraction_gap
#print axioms GRBS.IC1AbstractionGap.no_runtime_view_only_semantic_classifier
