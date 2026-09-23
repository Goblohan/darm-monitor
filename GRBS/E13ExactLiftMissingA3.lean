import GRBS
import E13CausalSemanticCorrespondence
import R20DARMToSemanticCorrespondence

namespace GRBS
namespace E13ExactLiftMissingA3

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

theorem exact_lift_missing_A3 :
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
        ¬ S.Step s s') ∧

      (∀ a s s',
        mediated a s s' →
        B.mediated s s') ∧

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
    intro hStep
    have hFalse : False := by
      have hTarget : s' = false := hStep.2
      have hTargetRep : s' = true := hRep.2
      exact Bool.noConfusion (hTargetRep.symm.trans hTarget)
    exact hFalse

  constructor
  · intro a s s' hMed
    trivial

  constructor
  · intro a s s' hRep
    trivial

  constructor
  · intro a hBoundary hSource
    have hStep := hBoundary.1
    simp [realize] at hStep

  · refine ⟨false, true, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · rfl
    · intro h
      cases h

end E13ExactLiftMissingA3
end GRBS
