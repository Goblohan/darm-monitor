import GRBS
import GRBS.E13CausalSemanticCorrespondence
import GRBS.R20DARMToSemanticCorrespondence

namespace GRBS
namespace E13ExactLiftMissingA1

open E13CausalSemanticCorrespondence
open R20DARMToSemanticCorrespondence

abbrev State := Bool

abbrev S : SemanticSystem :=
  { State := State
    Step := fun s s' => s = false ∧ s' = false }

abbrev G : SemanticGuarantee S :=
  { property := fun s => s = false }

abbrev B : SemanticBoundary S :=
  { mediated := fun _ _ => True }

/--
Exact-lift A1 deletion witness.

The represented transition is safe and satisfies all downstream
correspondence/mediation/discharge conditions. A second causeable
transition, false -> true, is not represented. Therefore the exact
causal guarantee conclusion fails when A1 is removed.
-/
theorem exact_lift_missing_A1 :
    ∃ (Access : Type)
      (causeable : CauseableTransition State)
      (represents : Represents Access State)
      (mediated : AccessMediated Access State)
      (realize : SemanticRealization Access S),

      RepresentationCompleteMediation represents mediated ∧

      (∀ a s s',
        represents a s s' →
        (realize a).source = s ∧
        (realize a).target = s') ∧

      (∀ a s s',
        represents a s s' →
        S.Step s s') ∧

      (∀ a s s',
        mediated a s s' →
        B.mediated s s') ∧

      (∀ a,
        BoundaryMediatedStep S B
          (realize a).source
          (realize a).target →
        G.property (realize a).source →
        G.property (realize a).target) ∧

      ¬ EffectRepresentationComplete causeable represents ∧

      (∃ s s',
        causeable s s' ∧
        G.property s ∧
        ¬ G.property s') := by

  let Access : Type := Unit

  let causeable : CauseableTransition State :=
    fun s s' =>
      (s = false ∧ s' = false) ∨
      (s = false ∧ s' = true)

  let represents : Represents Access State :=
    fun _ s s' =>
      s = false ∧ s' = false

  let mediated : AccessMediated Access State :=
    fun _ _ _ => True

  let realize : SemanticRealization Access S :=
    fun a =>
      { dependency := a
        source := false
        target := false }

  refine ⟨Access, causeable, represents, mediated, realize, ?_⟩

  constructor
  · intro a s s' hRep
    trivial

  constructor
  · intro a s s' hRep
    simp [realize, represents] at hRep ⊢
    exact hRep

  constructor
  · intro a s s' hRep
    exact hRep

  constructor
  · intro a s s' hMed
    trivial

  constructor
  · intro a hBoundary hSource
    exact hSource


  constructor
  · intro hComplete
    have hRep : ∃ a, represents a false true :=
      hComplete false true (by
        exact Or.inr ⟨rfl, rfl⟩)
    rcases hRep with ⟨a, h⟩
    exact Bool.noConfusion h.2

  · refine ⟨false, true, ?_, ?_, ?_⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · rfl
    · intro h
      cases h

end E13ExactLiftMissingA1
end GRBS
