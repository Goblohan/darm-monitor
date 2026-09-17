import GRBS
import AGBypass
import GRBS.R20DARMToSemanticCorrespondence
import GRBS.R19BoundaryMediatedTransferSemantics

namespace GRBS
namespace E13CausalSemanticCorrespondence

/--
A causeable effect is a state transition that an adversary can induce
in the system under consideration.
-/
abbrev CauseableTransition (State : Type) :=
  State → State → Prop

/--
The governed transition relation is the transition space represented
by the authorization boundary.
-/
abbrev GovernedTransition (State : Type) :=
  State → State → Prop


/--
Causeable effects are fully represented by the semantic boundary when every
causeable transition is an actual boundary-mediated semantic transition.
-/
def MediatedCausalCoverage
    {State : Type}
    (causeable : CauseableTransition State)
    (mediated : State → State → Prop) : Prop :=
  ∀ s s',
    causeable s s' →
    mediated s s'

/--
Causal effect coverage: every causeable effect is represented by a
governed transition.
-/
def CausalCoverage
    {State : Type}
    (causeable : CauseableTransition State)
    (governed : GovernedTransition State) : Prop :=
  ∀ s s', causeable s s' → governed s s'

/--
The semantic realization interface can be perfectly adequate while
causal coverage remains a separate obligation.
-/
theorem semantic_adequacy_does_not_imply_causal_coverage :
    ∃ (State : Type)
      (causeable governed : GovernedTransition State),
      (∀ s s', governed s s' → governed s s') ∧
      ¬ CausalCoverage causeable governed := by
  let State := Bool

  let governed : GovernedTransition State :=
    fun s s' =>
      s = false ∧ s' = false

  let causeable : CauseableTransition State :=
    fun s s' =>
      s = false ∧ s' = true

  refine ⟨State, causeable, governed, ?_, ?_⟩

  · intro s s' h
    exact h

  · intro hCoverage
    have hCause : causeable false true := by
      constructor <;> rfl
    have hGoverned : governed false true :=
      hCoverage false true hCause
    exact Bool.noConfusion hGoverned.2

/--
Once causal coverage is supplied, a governed safety theorem can be
lifted to the causeable effect domain.
-/
theorem causal_coverage_lifts_governed_safety
    {State : Type}
    (causeable governed : CauseableTransition State)
    (safe : State → Prop)
    (hCoverage : CausalCoverage causeable governed)
    (hGovernedSafe :
      ∀ s s', governed s s' → safe s → safe s') :
    ∀ s s', causeable s s' → safe s → safe s' := by
  intro s s' hCause hSafe
  exact hGovernedSafe s s'
    (hCoverage s s' hCause)
    hSafe

/--
R20 semantic realization adequacy can hold for the represented dependency
domain without establishing causal coverage of a larger causeable transition
domain.

This separates semantic adequacy of the realization from completeness of the
causeable effect domain.
-/
theorem r20_adequacy_does_not_imply_causal_coverage :
    ∃ (D : Type)
      (S : GRBS.R20DARMToSemanticCorrespondence.SemanticSystem)
      (G : GRBS.R20DARMToSemanticCorrespondence.SemanticGuarantee S)
      (B : GRBS.R20DARMToSemanticCorrespondence.SemanticBoundary S)
      (realize :
        GRBS.R20DARMToSemanticCorrespondence.SemanticRealization D S)
      (relevant :
        GRBS.R20DARMToSemanticCorrespondence.SemanticDependency D S.State → Prop)
      (discharge : D → Prop)
      (causeable : CauseableTransition S.State),
      GRBS.R20DARMToSemanticCorrespondence.SemanticRealizationAdequate
        S G B realize relevant discharge ∧
      ¬ CausalCoverage causeable S.Step := by
  let D := Unit
  let State := Bool

  let S : GRBS.R20DARMToSemanticCorrespondence.SemanticSystem :=
    { State := State
      Step := fun x y => x = false ∧ y = false }

  let G : GRBS.R20DARMToSemanticCorrespondence.SemanticGuarantee S :=
    { property := fun _ => True }

  let B : GRBS.R20DARMToSemanticCorrespondence.SemanticBoundary S :=
    { mediated := fun x y => x = false ∧ y = false }

  let realize :
      GRBS.R20DARMToSemanticCorrespondence.SemanticRealization D S :=
    fun d =>
      { dependency := d
        source := false
        target := false }

  let relevant :
      GRBS.R20DARMToSemanticCorrespondence.SemanticDependency D S.State → Prop :=
    fun _ => True

  let discharge : D → Prop := fun _ => True

  let causeable : CauseableTransition S.State :=
    fun x y => x = false ∧ y = true

  refine ⟨D, S, G, B, realize, relevant, discharge, causeable, ?_, ?_⟩

  · constructor
    · intro d
      rfl
    · constructor
      · intro d hRelevant
        constructor
        · constructor <;> rfl
        · trivial
      · intro d hDischarge hStep hSource
        trivial

  · intro hCoverage
    have hCause : causeable false true := by
      constructor <;> rfl
    have hStep : S.Step false true :=
      hCoverage false true hCause
    exact Bool.noConfusion hStep.2

/--
Causal coverage is the missing bridge from semantic-domain safety to safety
over the larger causeable effect domain.

This theorem deliberately treats causal coverage as an explicit assumption.
It does not claim that R20 semantic realization adequacy supplies that
assumption.
-/
theorem semantic_safety_plus_causal_coverage_implies_causeable_safety
    {D : Type}
    {S : GRBS.R20DARMToSemanticCorrespondence.SemanticSystem}
    {G : GRBS.R20DARMToSemanticCorrespondence.SemanticGuarantee S}
    {B : GRBS.R20DARMToSemanticCorrespondence.SemanticBoundary S}
    {realize :
      GRBS.R20DARMToSemanticCorrespondence.SemanticRealization D S}
    {relevant :
      GRBS.R20DARMToSemanticCorrespondence.SemanticDependency D S.State → Prop}
    {discharge : D → Prop}
    {causeable : CauseableTransition S.State}
    (hAdequate :
      GRBS.R20DARMToSemanticCorrespondence.SemanticRealizationAdequate
        S G B realize relevant discharge)
    (hCoverage : CausalCoverage causeable S.Step)
    (hSemanticSafety :
      ∀ s s',
        S.Step s s' →
        G.property s →
        G.property s') :
    ∀ s s',
      causeable s s' →
      G.property s →
      G.property s' := by
  exact causal_coverage_lifts_governed_safety
    causeable
    S.Step
    G.property
    hCoverage
    hSemanticSafety



/--
If every causeable effect is represented by a boundary-mediated semantic
transition, then R19 semantic preservation lifts to the entire causeable
effect domain.

This is the causal-domain completeness bridge: R19 supplies preservation
inside the mediated semantic domain; E13 supplies coverage of the causeable
effect domain by that mediated domain.
-/
theorem mediated_causal_coverage_plus_r19_preservation
    {S : R19BoundaryMediatedTransferSemantics.SemanticSystem}
    {G : R19BoundaryMediatedTransferSemantics.SemanticGuarantee S}
    {B : R19BoundaryMediatedTransferSemantics.SemanticBoundary S}
    {causeable : CauseableTransition S.State}
    (hCoverage :
      MediatedCausalCoverage
        causeable
        (fun s s' =>
          R19BoundaryMediatedTransferSemantics.BoundaryMediatedStep
            S B s s'))
    (hPreserves :
      R19BoundaryMediatedTransferSemantics.SemanticallyPreserves
        S G B) :
    ∀ s s',
      causeable s s' →
      G.property s →
      G.property s' := by
  intro s s' hCause hSafe
  exact hPreserves s s'
    (hCoverage s s' hCause)
    hSafe



/--
A concrete positive witness for the E13/R19 composition.

Here the causeable transition domain is exactly the boundary-mediated
semantic domain. R19 preservation therefore lifts directly to the
causeable domain.
-/
theorem r19_preservation_plus_causal_coverage_positive :
    ∃
      (S : R19BoundaryMediatedTransferSemantics.SemanticSystem)
      (G : R19BoundaryMediatedTransferSemantics.SemanticGuarantee S)
      (B : R19BoundaryMediatedTransferSemantics.SemanticBoundary S)
      (causeable : CauseableTransition S.State),
      MediatedCausalCoverage
        causeable
        (fun s s' =>
          R19BoundaryMediatedTransferSemantics.BoundaryMediatedStep
            S B s s') ∧
      R19BoundaryMediatedTransferSemantics.SemanticallyPreserves
        S G B ∧
      (∀ s s',
        causeable s s' →
        G.property s →
        G.property s') := by
  let State := Bool

  let S : R19BoundaryMediatedTransferSemantics.SemanticSystem :=
    { State := State
      Step := fun s s' => s = false ∧ s' = false }

  let G : R19BoundaryMediatedTransferSemantics.SemanticGuarantee S :=
    { property := fun _ => True }

  let B : R19BoundaryMediatedTransferSemantics.SemanticBoundary S :=
    { mediated := fun s s' => s = false ∧ s' = false }

  let causeable : CauseableTransition S.State :=
    fun s s' => s = false ∧ s' = false

  refine ⟨S, G, B, causeable, ?_, ?_, ?_⟩

  · intro s s' hCause
    constructor
    · simpa [S, causeable] using hCause
    · simpa [B, causeable] using hCause

  · intro s s' hMediated hSafe
    trivial

  · intro s s' hCause hSafe
    have hMediated :
        R19BoundaryMediatedTransferSemantics.BoundaryMediatedStep
          S B s s' := by
      constructor
      · simpa [S, causeable] using hCause
      · simpa [B, causeable] using hCause
    exact hSafe


/--
Controlled E13 perturbation.

The R19 semantic system and its preservation property remain unchanged,
but the causeable domain gains one transition that is not represented
by the mediated semantic domain. Thus semantic preservation can hold
while E13 causal coverage fails.
-/
theorem r19_preservation_without_causal_coverage :
    ∃
      (S : R19BoundaryMediatedTransferSemantics.SemanticSystem)
      (G : R19BoundaryMediatedTransferSemantics.SemanticGuarantee S)
      (B : R19BoundaryMediatedTransferSemantics.SemanticBoundary S)
      (causeable : CauseableTransition S.State),
      R19BoundaryMediatedTransferSemantics.SemanticallyPreserves
        S G B ∧
      ¬ MediatedCausalCoverage
        causeable
        (fun s s' =>
          R19BoundaryMediatedTransferSemantics.BoundaryMediatedStep
            S B s s') := by
  let State := Bool

  let S : R19BoundaryMediatedTransferSemantics.SemanticSystem :=
    { State := State
      Step := fun s s' => s = false ∧ s' = false }

  let G : R19BoundaryMediatedTransferSemantics.SemanticGuarantee S :=
    { property := fun _ => True }

  let B : R19BoundaryMediatedTransferSemantics.SemanticBoundary S :=
    { mediated := fun s s' => s = false ∧ s' = false }

  let causeable : CauseableTransition S.State :=
    fun s s' =>
      (s = false ∧ s' = false) ∨
      (s = false ∧ s' = true)

  refine ⟨S, G, B, causeable, ?_, ?_⟩

  · intro s s' hMediated hSafe
    trivial

  · intro hCoverage
    have hCause : causeable false true := by
      right
      constructor <;> rfl

    have hMediated :
        R19BoundaryMediatedTransferSemantics.BoundaryMediatedStep
          S B false true :=
      hCoverage false true hCause

    have hStep : S.Step false true := hMediated.1

    exact Bool.noConfusion hStep.2


/--
AGBypass correspondence witness.

The AGBypass physical footprint induces a causeable trace transition,
while the coverage topology induces the mediated transition relation.
For S2, the `violated` trace is physically causeable but not mediated.

The theorem deliberately makes the trace-to-transition encoding explicit:
E13 does not silently identify physical traces with semantic state
transitions.
-/
theorem agbypass_s2_exhibits_e13_coverage_failure :
    let causeable : CauseableTransition AGBypass.Witness.Tr :=
      fun x y =>
        x = AGBypass.Witness.Tr.ok ∧
        ∃ d : AGBypass.Witness.Ch,
          AGBypass.Witness.S2.physicalStep d y
    let mediated : CauseableTransition AGBypass.Witness.Tr :=
      fun x y =>
        x = AGBypass.Witness.Tr.ok ∧
        ∃ d : AGBypass.Witness.Ch,
          AGBypass.Witness.S2.physicalStep d y ∧
          AGBypass.Witness.S2.cov d
    ¬ MediatedCausalCoverage causeable mediated := by
  dsimp
  intro hCoverage

  have hCause :
      (AGBypass.Witness.Tr.ok = AGBypass.Witness.Tr.ok) ∧
      ∃ d : AGBypass.Witness.Ch,
        AGBypass.Witness.S2.physicalStep d
          AGBypass.Witness.Tr.violated := by
    constructor
    · rfl
    · exact ⟨AGBypass.Witness.Ch.d0, rfl⟩

  have hMediated :
      ∃ d : AGBypass.Witness.Ch,
        AGBypass.Witness.S2.physicalStep d
          AGBypass.Witness.Tr.violated ∧
        AGBypass.Witness.S2.cov d :=
    (hCoverage
      AGBypass.Witness.Tr.ok
      AGBypass.Witness.Tr.violated
      hCause).2

  obtain ⟨d, _hPhysical, hCovered⟩ := hMediated

  have hOnlyChannel :
      d = AGBypass.Witness.Ch.d0 := by
    cases d
    rfl

  subst hOnlyChannel

  exact AGBypass.Witness.bypass_unmediated_S2 hCovered

end E13CausalSemanticCorrespondence
end GRBS
