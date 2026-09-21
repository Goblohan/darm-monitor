import R21RepairAdequacy

namespace GRBS.R21RepairAdequacyMinimality

open GRBS
open GRBS.R20DARMToSemanticCorrespondence
open GRBS.R21RepairAdequacy

/--
Deletion witness for `representation_refines`.

The semantic realization and interpretation remain perfectly adequate,
and every causeable transition is represented, but the proposed new
representation does not preserve the old representation through the
claimed projection.
-/
theorem representation_refinement_is_necessary :
    ¬ (
      ∀
        {R Old New : Type}
        {S : SemanticSystem}
        (old : R → Old)
        (new : R → New)
        (project : New → Old)
        (realize : SemanticRealization New S)
        (interpret : SemanticInterpretation R S)
        (causeable : SemanticCauseableTransition S.State),
        RealizationAgreesWithInterpretation new realize interpret →
        CauseableInterpretationComplete interpret causeable →
        RepairAdequacy
          old
          new
          project
          realize
          interpret
          causeable
    ) := by
  intro hUniversal

  let S : SemanticSystem :=
    { State := Unit
      Step := fun _ _ => True }

  let old : Unit → Nat :=
    fun _ => 0

  let new : Unit → Bool :=
    fun _ => true

  let project : Bool → Nat :=
    fun _ => 1

  let interpret : SemanticInterpretation Unit S :=
    fun _ => ()

  let realize : SemanticRealization Bool S :=
    fun _ =>
      { dependency := true
        source := ()
        target := () }

  let causeable : SemanticCauseableTransition S.State :=
    fun _ _ => True

  have hAgreement :
      RealizationAgreesWithInterpretation new realize interpret := by
    intro r
    constructor <;> rfl

  have hComplete :
      CauseableInterpretationComplete interpret causeable := by
    intro x y hCause
    refine ⟨(), ?_, ?_⟩ <;> cases x <;> cases y <;> rfl

  have hRepair :=
    hUniversal
      old
      new
      project
      realize
      interpret
      causeable
      hAgreement
      hComplete

  have hRefines :
      RepresentationRefines old new project :=
    hRepair.representation_refines

  have hFalse : (1 : Nat) = 0 := by
    simpa [RepresentationRefines, old, new, project] using hRefines ()

  omega

end GRBS.R21RepairAdequacyMinimality

namespace GRBS.R21RepairAdequacyMinimality
open GRBS
open GRBS.R20DARMToSemanticCorrespondence
open GRBS.R21RepairAdequacy

/--
Deletion witness for `realization_agrees`.

The refined representation preserves the old representation and the
semantic interpretation covers every causeable transition, but the
semantic realization maps the refined representation to the wrong
semantic state.
-/
theorem realization_agreement_is_necessary :
    ¬ (
      ∀
        {R Old New : Type}
        {S : SemanticSystem}
        (old : R → Old)
        (new : R → New)
        (project : New → Old)
        (realize : SemanticRealization New S)
        (interpret : SemanticInterpretation R S)
        (causeable : SemanticCauseableTransition S.State),
        RepresentationRefines old new project →
        CauseableInterpretationComplete interpret causeable →
        RepairAdequacy
          old
          new
          project
          realize
          interpret
          causeable
    ) := by
  intro hUniversal

  let S : SemanticSystem :=
    { State := Bool
      Step := fun x y => x = y }

  let old : Unit → Nat :=
    fun _ => 0

  let new : Unit → Bool :=
    fun _ => true

  let project : Bool → Nat :=
    fun _ => 0

  let interpret : SemanticInterpretation Unit S :=
    fun _ => true

  let realize : SemanticRealization Bool S :=
    fun _ =>
      { dependency := true
        source := false
        target := false }

  let causeable : SemanticCauseableTransition S.State :=
    fun x y => x = true ∧ y = true

  have hRefines :
      RepresentationRefines old new project := by
    intro r
    rfl

  have hComplete :
      CauseableInterpretationComplete interpret causeable := by
    intro x y hCause
    refine ⟨(), ?_, ?_⟩
    · exact (hCause.1).symm
    · exact (hCause.2).symm

  have hRepair :=
    hUniversal
      old
      new
      project
      realize
      interpret
      causeable
      hRefines
      hComplete

  have hAgreement :
      RealizationAgreesWithInterpretation new realize interpret :=
    hRepair.realization_agrees

  have hFalse : false = true := by
    have h := (hAgreement ())
    exact h.1

  cases hFalse

open GRBS
open GRBS.R20DARMToSemanticCorrespondence
open GRBS.R21RepairAdequacy
end GRBS.R21RepairAdequacyMinimality

open GRBS
open GRBS.R20DARMToSemanticCorrespondence
open GRBS.R21RepairAdequacy
namespace GRBS.R21RepairAdequacyMinimality

/--
Deletion witness for `causeable_complete`.

The refined representation preserves the old representation and its
semantic realization agrees exactly with the request interpretation,
but the causeable semantic domain contains a transition for which no
request interpretation exists.
-/
theorem causeable_completeness_is_necessary :
    ¬ (
      ∀
        {R Old New : Type}
        {S : SemanticSystem}
        (old : R → Old)
        (new : R → New)
        (project : New → Old)
        (realize : SemanticRealization New S)
        (interpret : SemanticInterpretation R S)
        (causeable : SemanticCauseableTransition S.State),
        RepresentationRefines old new project →
        RealizationAgreesWithInterpretation new realize interpret →
        RepairAdequacy
          old
          new
          project
          realize
          interpret
          causeable
    ) := by
  intro hUniversal

  let S : SemanticSystem :=
    { State := Bool
      Step := fun x y => x = y }

  let old : Unit → Nat :=
    fun _ => 0

  let new : Unit → Bool :=
    fun _ => true

  let project : Bool → Nat :=
    fun _ => 0

  let interpret : SemanticInterpretation Unit S :=
    fun _ => true

  let realize : SemanticRealization Bool S :=
    fun d =>
      { dependency := d
        source := d
        target := d }

  let causeable : SemanticCauseableTransition S.State :=
    fun x y => x = y

  have hRefines :
      RepresentationRefines old new project := by
    intro r
    rfl

  have hAgreement :
      RealizationAgreesWithInterpretation new realize interpret := by
    intro r
    constructor <;> rfl

  have hRepair :=
    hUniversal
      old
      new
      project
      realize
      interpret
      causeable
      hRefines
      hAgreement

  have hComplete :
      CauseableInterpretationComplete interpret causeable :=
    hRepair.causeable_complete

  have hFalse :
      interpret () = false := by
    have hWitness := hComplete false false
    have hCause : causeable false false := by
      rfl
    obtain ⟨r, hrx, hry⟩ := hWitness hCause
    exact hrx

  simp [interpret] at hFalse

end GRBS.R21RepairAdequacyMinimality
