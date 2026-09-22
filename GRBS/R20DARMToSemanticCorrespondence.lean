/-
R20: DARM-to-Semantics Correspondence

PURPOSE

R19 and R19b established two deliberately separate layers:

  * R19 defines boundary-mediated semantic transfer.
  * R19b defines an explicit adequacy bridge from structural dependencies
    to semantic preservation.

R20 connects those layers to the canonical DARM transfer calculus.

The connection is intentionally conditional. DARM structural conditions do
not themselves prove that an abstract dependency corresponds to a semantic
transition. That correspondence is supplied by an explicit semantic
realization and adequacy interface.

ARCHITECTURE

  DARM dependency
        |
        | semantic realization
        v
  semantic dependency
        |
        | transition adequacy
        v
  boundary-mediated semantic step
        |
        | discharge adequacy
        v
  guarantee preservation

The intended conclusion is therefore:

  DARM transfer admissibility
      +
  semantic realization adequacy
      ->
  semantic target assurance.

No converse theorem is asserted.

NON-GOALS

This module does not establish:

  * physical completeness of the semantic model;
  * correctness of a hardware implementation;
  * correctness of a reference monitor;
  * validity of the semantic realization itself.

Those are separate assurance obligations.
-/

import DARMCoreCalculus

namespace GRBS.R20DARMToSemanticCorrespondence

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.DARMCoreCalculus

/-- Minimal semantic system interface required by R20. -/
structure SemanticSystem where
  State : Type
  Step : State → State → Prop

/-- A semantic guarantee over system states. -/
structure SemanticGuarantee (S : SemanticSystem) where
  property : S.State → Prop

/-- A semantic boundary identifying mediated transitions. -/
structure SemanticBoundary (S : SemanticSystem) where
  mediated : S.State → S.State → Prop

/-- A boundary-mediated semantic transition. -/
def BoundaryMediatedStep
    (S : SemanticSystem)
    (B : SemanticBoundary S)
    (x y : S.State) : Prop :=
  S.Step x y ∧ B.mediated x y

/-- A semantic dependency associated with a structural dependency and states. -/
structure SemanticDependency (D State : Type) where
  dependency : D
  source : State
  target : State

/--
A semantic realization maps each structural dependency to a semantic
dependency obligation.
-/
def SemanticRealization
    (D : Type)
    (S : SemanticSystem) :=
  D → SemanticDependency D S.State

/--
The realization is dependency-faithful when the semantic dependency
preserves the identity of the structural dependency.
-/
def RealizationFaithful
    {D : Type}
    {S : SemanticSystem}
    (realize : SemanticRealization D S) : Prop :=
  ∀ d, (realize d).dependency = d

/--
A realized dependency is transition-adequate when its source and target
states form an actual boundary-mediated semantic step.
-/
def RealizationTransitionAdequate
    {D : Type}
    (S : SemanticSystem)
    (B : SemanticBoundary S)
    (realize : SemanticRealization D S)
    (d : D) : Prop :=
  BoundaryMediatedStep S B
    (realize d).source
    (realize d).target

/--
Transition adequacy for every dependency that is semantically relevant.
-/
def RelevantRealizationsTransitionAdequate
    {D : Type}
    (S : SemanticSystem)
    (B : SemanticBoundary S)
    (realize : SemanticRealization D S)
    (relevant : SemanticDependency D S.State → Prop) : Prop :=
  ∀ d, relevant (realize d) →
    RealizationTransitionAdequate S B realize d

/--
A discharge predicate is semantically adequate when discharge of a
dependency establishes the guarantee at the realized target state whenever
the realized source state already satisfies the guarantee.
-/
def RealizationDischargeAdequate
    {D : Type}
    (S : SemanticSystem)
    (G : SemanticGuarantee S)
    (B : SemanticBoundary S)
    (realize : SemanticRealization D S)
    (discharge : D → Prop) : Prop :=
  ∀ d, discharge d →
    BoundaryMediatedStep S B
      (realize d).source
      (realize d).target →
    G.property (realize d).source →
    G.property (realize d).target

/--
Semantic realization adequacy combines the three distinct obligations required
to interpret a DARM transfer in the semantic system:

  1. dependency identity is preserved;
  2. relevant realized dependencies correspond to actual boundary-mediated
     semantic transitions;
  3. discharged dependencies preserve the semantic guarantee across those
     realized mediated steps.

DARM does not prove these obligations. They constitute the explicit semantic
adequacy interface between the structural assurance layer and the semantic
system.
-/
def SemanticRealizationAdequate
    {D : Type}
    (S : SemanticSystem)
    (G : SemanticGuarantee S)
    (B : SemanticBoundary S)
    (realize : SemanticRealization D S)
    (relevant : SemanticDependency D S.State → Prop)
    (discharge : D → Prop) : Prop :=
  RealizationFaithful realize ∧
  RelevantRealizationsTransitionAdequate S B realize relevant ∧
  RealizationDischargeAdequate S G B realize discharge

/--
A DARM-admissible transfer can establish semantic target assurance when the
structural delta is represented by a semantic realization whose relevant
dependencies are actual boundary-mediated transitions and whose discharged
transitions preserve the semantic guarantee.

The theorem deliberately keeps semantic realization adequacy explicit. DARM
supplies the structural transfer discipline; the semantic realization and its
adequacy remain separate proof obligations.
-/
theorem darm_delta_realizations_preserve_guarantee
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : DARMCoreCalculus.TransferCandidate F.Dependency)
    (S : SemanticSystem)
    (G : SemanticGuarantee S)
    (B : SemanticBoundary S)
    (realize : SemanticRealization F.Dependency S)
    (relevant : SemanticDependency F.Dependency S.State → Prop)
    (discharge : F.Dependency → Prop)
    (hAdmissible :
      DARMCoreCalculus.DARMTransferAdmissible F g s b l c)
    (hAdequate :
      SemanticRealizationAdequate S G B realize relevant discharge)
    (hDeltaSource :
      ∀ d,
        GRBS.R5AssuranceConservation.Delta
          F.Dependency c.source c.target d →
        c.property d →
        G.property (realize d).source)
    (hDeltaRelevant :
      ∀ d,
        GRBS.R5AssuranceConservation.Delta
          F.Dependency c.source c.target d →
        relevant (realize d))
    (hDeltaDischarge :
      ∀ d,
        GRBS.R5AssuranceConservation.Delta
          F.Dependency c.source c.target d →
        discharge d) :
    ∀ d,
      GRBS.R5AssuranceConservation.Delta
        F.Dependency c.source c.target d →
      G.property (realize d).target := by
  have hDeltaObligation :
      GRBS.R5AssuranceConservation.DeltaObligation
        F.Dependency c.source c.target c.property :=
    DARMCoreCalculus.darm_admissibility_discharges_delta
      F g s b l c hAdmissible
  rcases hAdequate with ⟨hFaithful, hTransition, hDischarge⟩
  intro d hDelta
  have hStructuralProperty : c.property d :=
    hDeltaObligation d hDelta
  have hSemanticSource : G.property (realize d).source :=
    hDeltaSource d hDelta hStructuralProperty
  have hStep :
      BoundaryMediatedStep S B
        (realize d).source
        (realize d).target :=
    hTransition d (hDeltaRelevant d hDelta)
  have hSemanticTarget :
      G.property (realize d).target :=
    hDischarge d
      (hDeltaDischarge d hDelta)
      hStep
      hSemanticSource
  exact hSemanticTarget


/--
The explicit linkage obligations connecting a structural DARM delta to its
semantic realization.

The three fields are intentionally separate:
1. structural delta properties establish semantic source safety;
2. structural delta dependencies are relevant realized dependencies;
3. structural delta dependencies are discharged.

This structure packages existing proof obligations without adding a new
semantic assumption.
-/
structure SemanticDeltaLinkage
    (F : Frame)
    (c : DARMCoreCalculus.TransferCandidate F.Dependency)
    (S : SemanticSystem)
    (G : SemanticGuarantee S)
    (realize : SemanticRealization F.Dependency S)
    (relevant : SemanticDependency F.Dependency S.State → Prop)
    (discharge : F.Dependency → Prop) : Prop where
  source :
    ∀ d,
      GRBS.R5AssuranceConservation.Delta
        F.Dependency c.source c.target d →
      c.property d →
      G.property (realize d).source
  relevant :
    ∀ d,
      GRBS.R5AssuranceConservation.Delta
        F.Dependency c.source c.target d →
      relevant (realize d)
  discharge :
    ∀ d,
      GRBS.R5AssuranceConservation.Delta
        F.Dependency c.source c.target d →
      discharge d

/--
Minimal semantic guarantee form of the R20 correspondence theorem.

The target-guarantee conclusion requires only transition adequacy and discharge
adequacy for the relevant realized dependencies. Realization faithfulness is
part of the stronger `SemanticRealizationAdequate` certificate, but is not
used by this particular preservation result.

The three delta-linkage obligations remain explicit:
1. structural delta properties establish semantic source safety;
2. structural delta dependencies are relevant realizations;
3. structural delta dependencies are discharged.
-/
theorem darm_delta_realizations_preserve_guarantee_minimal
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : DARMCoreCalculus.TransferCandidate F.Dependency)
    (S : SemanticSystem)
    (G : SemanticGuarantee S)
    (B : SemanticBoundary S)
    (realize : SemanticRealization F.Dependency S)
    (relevant : SemanticDependency F.Dependency S.State → Prop)
    (discharge : F.Dependency → Prop)
    (hAdmissible :
      DARMCoreCalculus.DARMTransferAdmissible F g s b l c)
    (hTransition :
      RelevantRealizationsTransitionAdequate
        S B realize relevant)
    (hDischarge :
      RealizationDischargeAdequate
        S G B realize discharge)
    (hDeltaSource :
      ∀ d,
        GRBS.R5AssuranceConservation.Delta
          F.Dependency c.source c.target d →
        c.property d →
        G.property (realize d).source)
    (hDeltaRelevant :
      ∀ d,
        GRBS.R5AssuranceConservation.Delta
          F.Dependency c.source c.target d →
        relevant (realize d))
    (hDeltaDischarge :
      ∀ d,
        GRBS.R5AssuranceConservation.Delta
          F.Dependency c.source c.target d →
        discharge d) :
    ∀ d,
      GRBS.R5AssuranceConservation.Delta
        F.Dependency c.source c.target d →
      G.property (realize d).target := by
  have hDeltaObligation :
      GRBS.R5AssuranceConservation.DeltaObligation
        F.Dependency c.source c.target c.property :=
    DARMCoreCalculus.darm_admissibility_discharges_delta
      F g s b l c hAdmissible
  intro d hDelta
  have hStructuralProperty : c.property d :=
    hDeltaObligation d hDelta
  have hSemanticSource : G.property (realize d).source :=
    hDeltaSource d hDelta hStructuralProperty
  have hStep :
      BoundaryMediatedStep S B
        (realize d).source
        (realize d).target :=
    hTransition d (hDeltaRelevant d hDelta)
  exact
    hDischarge d
      (hDeltaDischarge d hDelta)
      hStep
      hSemanticSource


/--
Convenience form of the minimal R20 semantic guarantee theorem using the
structured `SemanticDeltaLinkage` interface.
-/
theorem semantic_delta_linkage_implies_guarantee
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : DARMCoreCalculus.TransferCandidate F.Dependency)
    (S : SemanticSystem)
    (G : SemanticGuarantee S)
    (B : SemanticBoundary S)
    (realize : SemanticRealization F.Dependency S)
    (relevant : SemanticDependency F.Dependency S.State → Prop)
    (discharge : F.Dependency → Prop)
    (hAdmissible :
      DARMCoreCalculus.DARMTransferAdmissible F g s b l c)
    (hTransition :
      RelevantRealizationsTransitionAdequate
        S B realize relevant)
    (hDischarge :
      RealizationDischargeAdequate
        S G B realize discharge)
    (hLinkage :
      SemanticDeltaLinkage
        F c S G realize relevant discharge) :
    ∀ d,
      GRBS.R5AssuranceConservation.Delta
        F.Dependency c.source c.target d →
      G.property (realize d).target := by
  exact
    darm_delta_realizations_preserve_guarantee_minimal
      F g s b l c S G B realize relevant discharge
      hAdmissible
      hTransition
      hDischarge
      hLinkage.source
      hLinkage.relevant
      hLinkage.discharge


/--
Structural DARM coverage does not itself provide semantic realization
adequacy.

The theorem constructs a case where a dependency is covered but the
realized transition violates the guarantee.
-/
theorem covered_dependency_does_not_imply_realization_adequacy :
    ∃ (D : Type)
      (covered : D → Prop)
      (S : SemanticSystem)
      (realize : SemanticRealization D S)
      (G : SemanticGuarantee S)
      (B : SemanticBoundary S),
      (∀ d, covered d) ∧
      (∃ d,
        covered d ∧
        RealizationTransitionAdequate S B realize d ∧
        G.property (realize d).source ∧
        ¬ G.property (realize d).target) := by
  let D := Unit
  let State := Bool

  let S : SemanticSystem :=
    { State := State
      Step := fun x y => x = false ∧ y = true }

  let G : SemanticGuarantee S :=
    { property := fun x => x = false }

  let B : SemanticBoundary S :=
    { mediated := fun _ _ => True }

  let realize : SemanticRealization D S :=
    fun d =>
      { dependency := d
        source := false
        target := true }

  let covered : D → Prop := fun _ => True

  refine ⟨D, covered, S, realize, G, B, ?_, ?_⟩
  · intro d
    trivial
  · refine ⟨(), ?_, ?_, ?_, ?_⟩
    · trivial
    · constructor
      · constructor <;> rfl
      · trivial
    · rfl
    · simp [G]

/--
The structural DARM transfer condition is not sufficient for semantic
transfer unless a semantic realization/adequacy interface is supplied.

This is stated as a methodological negative result rather than as a claim
about any particular implementation.
-/
theorem darm_structure_requires_semantic_adequacy :
    ∃ (D : Type)
      (covered discharge : D → Prop)
      (S : SemanticSystem)
      (realize : SemanticRealization D S)
      (G : SemanticGuarantee S)
        (_B : SemanticBoundary S),
      (∀ d, covered d) ∧
      (∀ d, discharge d) ∧
      (∃ d,
        covered d ∧
        discharge d ∧
        G.property (realize d).source ∧
        ¬ G.property (realize d).target) := by
  let D := Unit
  let State := Bool

  let S : SemanticSystem :=
    { State := State
      Step := fun x y => x = false ∧ y = true }

  let G : SemanticGuarantee S :=
    { property := fun x => x = false }

  let B : SemanticBoundary S :=
    { mediated := fun _ _ => True }

  let realize : SemanticRealization D S :=
    fun d =>
      { dependency := d
        source := false
        target := true }

  let covered : D → Prop := fun _ => True
  let discharge : D → Prop := fun _ => True

  refine ⟨D, covered, discharge, S, realize, G, B, ?_, ?_, ?_⟩
  · intro d
    trivial
  · intro d
    trivial
  · refine ⟨(), ?_, ?_, ?_, ?_⟩
    · trivial
    · trivial
    · rfl
    · intro h
      exact Bool.noConfusion h

/--
R20-J1: semantic causal-domain coverage.

A causeable semantic transition is covered when some relevant realized
dependency has exactly that source and target and is therefore an actual
boundary-mediated semantic transition.

This isolates causal-domain coverage from realization faithfulness and
discharge adequacy.
-/
abbrev SemanticCauseableTransition (State : Type) :=
  State → State → Prop

def RelevantRealizationCausalCoverage
    {D : Type}
    (S : SemanticSystem)
    (B : SemanticBoundary S)
    (realize : SemanticRealization D S)
    (relevant : SemanticDependency D S.State → Prop)
    (causeable : SemanticCauseableTransition S.State) : Prop :=
  ∀ x y,
    causeable x y →
    ∃ d,
      relevant (realize d) ∧
      (realize d).source = x ∧
      (realize d).target = y

def SemanticMediatedCausalCoverage
    {D : Type}
    (S : SemanticSystem)
    (B : SemanticBoundary S)
    (realize : SemanticRealization D S)
    (relevant : SemanticDependency D S.State → Prop)
    (causeable : SemanticCauseableTransition S.State) : Prop :=
  ∀ x y,
    causeable x y →
    ∃ d,
      relevant (realize d) ∧
      BoundaryMediatedStep S B
        (realize d).source
        (realize d).target ∧
      (realize d).source = x ∧
      (realize d).target = y

/--
R20-J1:
Relevant realization causal-domain coverage plus transition adequacy
implies causal coverage by boundary-mediated semantic steps.
-/
theorem relevant_realization_causal_coverage_plus_transition_adequacy_implies_semantic_mediated_causal_coverage :
    ∀
      {D : Type}
      (S : SemanticSystem)
      (B : SemanticBoundary S)
      (realize : SemanticRealization D S)
      (relevant : SemanticDependency D S.State → Prop)
      (causeable : SemanticCauseableTransition S.State),
      RelevantRealizationCausalCoverage
        S B realize relevant causeable →
      RelevantRealizationsTransitionAdequate
        S B realize relevant →
      SemanticMediatedCausalCoverage
        S B realize relevant causeable := by
  intro D S B realize relevant causeable
  intro hCoverage hTransition
  intro x y hCause
  obtain ⟨d, hRelevant, hSource, hTarget⟩ :=
    hCoverage x y hCause
  have hStep :
      BoundaryMediatedStep S B
        (realize d).source
        (realize d).target :=
    hTransition d hRelevant
  exact ⟨d, hRelevant, hStep, hSource, hTarget⟩


/--
R20-J2 witness:
semantic realization adequacy does not imply causal-domain coverage.

The model is non-vacuous. A relevant realized dependency exists and is
transition-adequate, but the causeable domain contains an additional
source/target transition for which no relevant realization exists.
-/
theorem semantic_realization_adequacy_does_not_imply_relevant_realization_causal_coverage :
    ∃
      (D State : Type)
      (S : SemanticSystem)
      (G : SemanticGuarantee S)
      (B : SemanticBoundary S)
      (realize : SemanticRealization D S)
      (relevant : SemanticDependency D S.State → Prop)
      (discharge : D → Prop)
      (causeable : SemanticCauseableTransition S.State),
      SemanticRealizationAdequate S G B realize relevant discharge ∧
      ¬ RelevantRealizationCausalCoverage
        S B realize relevant causeable := by
  let D : Type := Unit
  let State : Type := Bool

  let S : SemanticSystem :=
    { State := State
      Step := fun x y => x = false ∧ y = false }

  let G : SemanticGuarantee S :=
    { property := fun _ => True }

  let B : SemanticBoundary S :=
    { mediated := fun x y => x = false ∧ y = false }

  let realize : SemanticRealization D S :=
    fun _ =>
      { dependency := ()
        source := false
        target := false }

  let relevant : SemanticDependency D S.State → Prop :=
    fun d => d.source = false ∧ d.target = false

  let discharge : D → Prop :=
    fun _ => True

  let causeable : SemanticCauseableTransition S.State :=
    fun x y => x = false ∧ y = true

  have hFaithful : RealizationFaithful realize := by
    intro d
    rfl

  have hTransition :
      RelevantRealizationsTransitionAdequate
        S B realize relevant := by
    intro d hRelevant
    unfold RealizationTransitionAdequate BoundaryMediatedStep
    constructor
    · constructor <;> rfl
    · constructor <;> rfl

  have hDischarge :
      RealizationDischargeAdequate S G B realize discharge := by
    intro d hDischarge hMediated hSource
    trivial

  have hAdequate :
      SemanticRealizationAdequate S G B realize relevant discharge :=
    ⟨hFaithful, hTransition, hDischarge⟩

  have hNotCoverage :
      ¬ RelevantRealizationCausalCoverage
        S B realize relevant causeable := by
    intro hCoverage
    obtain ⟨d, hRelevant, hSource, hTarget⟩ :=
      hCoverage false true (by
        constructor <;> rfl)
    have hTargetFalse : (realize d).target = false := by
      rfl
    have : true = false := by
      exact hTarget.symm.trans hTargetFalse
    cases this

  exact ⟨D, State, S, G, B, realize, relevant, discharge, causeable,
    hAdequate, hNotCoverage⟩

/--
R20-J3: causal-domain coverage plus semantic discharge adequacy lifts
semantic source safety to causeable target safety.

The causal-domain coverage obligation identifies a relevant realization for
each causeable transition. Discharge coverage then ensures that the selected
realization is actually discharged, while source and target correspondence
connect the realized transition back to the causeable transition.
-/
theorem relevant_causal_coverage_plus_discharge_coverage_implies_causeable_safety :
    ∀
      {D : Type}
      (S : SemanticSystem)
      (G : SemanticGuarantee S)
      (B : SemanticBoundary S)
      (realize : SemanticRealization D S)
      (relevant : SemanticDependency D S.State → Prop)
      (discharge : D → Prop)
      (causeable : SemanticCauseableTransition S.State),
      RelevantRealizationCausalCoverage
        S B realize relevant causeable →
      RelevantRealizationsTransitionAdequate
        S B realize relevant →
      RealizationDischargeAdequate
        S G B realize discharge →
      (∀ d,
        relevant (realize d) →
        discharge d) →
      ∀ x y,
        causeable x y →
        (∀ d,
          relevant (realize d) →
          (realize d).source = x →
          G.property x →
          G.property (realize d).source) →
        (∀ d,
          relevant (realize d) →
          (realize d).target = y →
          G.property (realize d).target →
          G.property y) →
        G.property x →
        G.property y := by
  intro D S G B realize relevant discharge causeable
  intro hCoverage hTransition hDischarge hDischargeCoverage
  intro x y hCause hSourceCorrespondence hTargetCorrespondence hSafeSource
  obtain ⟨d, hRelevant, hSource, hTarget⟩ :=
    hCoverage x y hCause
  have hDischargeD : discharge d :=
    hDischargeCoverage d hRelevant
  have hRealizedSource : G.property (realize d).source :=
    hSourceCorrespondence d hRelevant hSource hSafeSource
  have hMediated :
      BoundaryMediatedStep S B
        (realize d).source
        (realize d).target :=
    hTransition d hRelevant
  have hRealizedTarget :
      G.property (realize d).target :=
    hDischarge d hDischargeD hMediated hRealizedSource
  exact hTargetCorrespondence d hRelevant hTarget hRealizedTarget

/--
R20-J4: causal-domain coverage does not imply semantic realization
adequacy.

The causeable transition is fully represented by a relevant realization, so
causal-domain coverage holds. However, the realized transition is not an
actual boundary-mediated semantic step, so realization adequacy fails.
-/
theorem relevant_realization_causal_coverage_does_not_imply_semantic_realization_adequacy :
    ∃
      (D State : Type)
      (S : SemanticSystem)
      (G : SemanticGuarantee S)
      (B : SemanticBoundary S)
      (realize : SemanticRealization D S)
      (relevant : SemanticDependency D S.State → Prop)
      (discharge : D → Prop)
      (causeable : SemanticCauseableTransition S.State),
      RelevantRealizationCausalCoverage
        S B realize relevant causeable ∧
      ¬ SemanticRealizationAdequate
        S G B realize relevant discharge := by
  let D : Type := Unit
  let State : Type := Bool

  let S : SemanticSystem :=
    { State := State
      Step := fun _ _ => False }

  let G : SemanticGuarantee S :=
    { property := fun _ => True }

  let B : SemanticBoundary S :=
    { mediated := fun x y => x = false ∧ y = true }

  let realize : SemanticRealization D S :=
    fun _ =>
      { dependency := ()
        source := false
        target := true }

  let relevant : SemanticDependency D S.State → Prop :=
    fun _ => True

  let discharge : D → Prop :=
    fun _ => True

  let causeable : SemanticCauseableTransition S.State :=
    fun x y => x = false ∧ y = true

  have hCoverage :
      RelevantRealizationCausalCoverage
        S B realize relevant causeable := by
    intro x y hCause
    obtain ⟨hx, hy⟩ := hCause
    refine ⟨(), ?_, ?_, ?_⟩
    · trivial
    · simpa [realize] using hx.symm
    · simpa [realize] using hy.symm

  have hNotAdequate :
      ¬ SemanticRealizationAdequate
        S G B realize relevant discharge := by
    intro hAdequate
    rcases hAdequate with ⟨hFaithful, hTransition, hDischarge⟩
    have hRelevant : relevant (realize ()) := by
      trivial
    have hStep :
        BoundaryMediatedStep S B
          (realize ()).source
          (realize ()).target :=
      hTransition () hRelevant
    unfold BoundaryMediatedStep at hStep
    exact hStep.1

  exact ⟨D, State, S, G, B, realize, relevant, discharge,
    causeable, hCoverage, hNotAdequate⟩

end GRBS.R20DARMToSemanticCorrespondence
