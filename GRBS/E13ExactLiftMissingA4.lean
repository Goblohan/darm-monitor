import GRBS
import GRBS.E13CausalSemanticCorrespondence
import GRBS.R20DARMToSemanticCorrespondence

namespace GRBS
namespace E13ExactLiftMissingA4

open E13CausalSemanticCorrespondence
open R20DARMToSemanticCorrespondence

abbrev State := Bool

abbrev S : SemanticSystem :=
  { State := State
    Step := fun s s' =>
      s = false ∧ s' = true }

abbrev G : SemanticGuarantee S :=
  { property := fun s => s = false }

abbrev B : SemanticBoundary S :=
  { mediated := fun _ _ => False }

theorem exact_lift_missing_A4 :
    ∃ (Access : Type)
      (causeable : CauseableTransition State)
      (represents : Represents Access State)
      (mediated : AccessMediated Access State)
      (realize : SemanticRealization Access S),

      EffectRepresentationComplete causeable represents ∧

      (∀ a s s',
        represents a s s' →
        (realize a).source = s ∧
        (realize a).target = s') ∧

      (∀ a s s',
        represents a s s' →
        S.Step s s') ∧

      (∀ a s s',
        mediated a s s' →
        ¬ B.mediated s s') ∧

      RepresentationCompleteMediation represents mediated ∧

      (∀ a,
        BoundaryMediatedStep S B
          (realize a).source
          (realize a).target →
        G.property (realize a).source →
        G.property (realize a).target) ∧

      (∃ s s',
        causeable s s' ∧
        G.property s ∧
        ¬ G.property s') := by

  let Access : Type := Unit

  let causeable : CauseableTransition State :=
    fun s s' =>
      s = false ∧ s' = true

  let represents : Represents Access State :=
    fun _ s s' =>
      s = false ∧ s' = true

  let mediated : AccessMediated Access State :=
    fun _ _ _ => True

  let realize : SemanticRealization Access S :=
    fun a =>
      { dependency := a
        source := false
        target := true }

  refine ⟨Access, causeable, represents, mediated, realize, ?_⟩

  constructor
  · intro s s' hCause
    exact ⟨(), hCause⟩

  constructor
  · intro a s s' hRep
    constructor
    · simpa [realize] using hRep.1.symm
    · simpa [realize] using hRep.2.symm

  constructor
  · intro a s s' hRep
    exact hRep

  constructor
  · intro a s s' hMed
    simp

  constructor
  · intro a s s' hRep
    trivial

  constructor
  · intro a hBoundary hSource
    have hBoundaryFalse : False := by
      exact hBoundary.2
    exact False.elim hBoundaryFalse

  · refine ⟨false, true, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · rfl
    · intro h
      cases h

end E13ExactLiftMissingA4
end GRBS
