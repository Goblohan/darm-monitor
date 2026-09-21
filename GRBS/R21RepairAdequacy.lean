import R20DARMToSemanticCorrespondence

namespace GRBS.R21RepairAdequacy

open GRBS
open GRBS.R20DARMToSemanticCorrespondence

/--
A representation refinement preserves the identity exposed by an older
representation through an explicit projection.
-/
def RepresentationRefines
    {R Old New : Type}
    (old : R → Old)
    (new : R → New)
    (project : New → Old) : Prop :=
  ∀ r, project (new r) = old r

/--
A semantic interpretation assigns the semantic state represented by a
request.
-/
def SemanticInterpretation
    (R : Type)
    (S : SemanticSystem) : Type :=
  R → S.State

/--
The semantic realization of the refined representation agrees with
the semantic state represented by the request.
-/
def RealizationAgreesWithInterpretation
    {R New : Type}
    {S : SemanticSystem}
    (new : R → New)
    (realize : SemanticRealization New S)
    (interpret : SemanticInterpretation R S) : Prop :=
  ∀ r,
    (realize (new r)).source = interpret r ∧
    (realize (new r)).target = interpret r

/--
Every causeable transition is represented by a request whose semantic
interpretation supplies both endpoints.
-/
def CauseableInterpretationComplete
    {R : Type}
    {S : SemanticSystem}
    (interpret : SemanticInterpretation R S)
    (causeable : SemanticCauseableTransition S.State) : Prop :=
  ∀ x y,
    causeable x y →
    ∃ r,
      interpret r = x ∧
      interpret r = y

/--
A non-circular repair certificate.

Representation refinement preserves the old abstraction. Semantic
realization agrees with the semantic interpretation of the refined
representation. The interpretation covers the causeable semantic
domain.
-/
structure RepairAdequacy
    {R Old New : Type}
    {S : SemanticSystem}
    (old : R → Old)
    (new : R → New)
    (project : New → Old)
    (realize : SemanticRealization New S)
    (interpret : SemanticInterpretation R S)
    (causeable : SemanticCauseableTransition S.State) : Prop where
  representation_refines :
    RepresentationRefines old new project
  realization_agrees :
    RealizationAgreesWithInterpretation new realize interpret
  causeable_complete :
    CauseableInterpretationComplete interpret causeable

/--
General R21 repair theorem:

a valid repair certificate establishes relevant realization causal
coverage.

Causal coverage is derived from independent semantic conditions. It is
not used to define RepairAdequacy.
-/
theorem repair_adequacy_implies_causal_coverage
    {R Old New : Type}
    {S : SemanticSystem}
    (old : R → Old)
    (new : R → New)
    (project : New → Old)
    (realize : SemanticRealization New S)
    (interpret : SemanticInterpretation R S)
    (causeable : SemanticCauseableTransition S.State)
    (hRepair :
      RepairAdequacy
        old
        new
        project
        realize
        interpret
        causeable) :
    RelevantRealizationCausalCoverage
      S
      { mediated := fun _ _ => True }
      realize
      (fun _ => True)
      causeable := by
  intro x y hCause

  obtain ⟨r, hrx, hry⟩ :=
    hRepair.causeable_complete x y hCause

  obtain ⟨hSource, hTarget⟩ :=
    hRepair.realization_agrees r

  refine ⟨new r, trivial, ?_, ?_⟩
  · exact hSource.trans hrx
  · exact hTarget.trans hry


/--
Independent mediation condition for a repaired representation.

Every semantic transition produced by the refined representation is
actually a boundary-mediated transition in the semantic system.
-/
def RepairMediation
    {R New : Type}
    {S : SemanticSystem}
    (new : R → New)
    (realize : SemanticRealization New S)
    (B : SemanticBoundary S) : Prop :=
  ∀ r,
    BoundaryMediatedStep S B
      (realize (new r)).source
      (realize (new r)).target

/--
A repair that is semantically adequate and whose realized transitions
are boundary-mediated establishes semantic mediated causal coverage.

Causal coverage is still derived, rather than being part of the
definition of either repair adequacy or repair mediation.
-/
theorem repair_adequacy_plus_mediation_implies_semantic_mediated_causal_coverage
    {R Old New : Type}
    {S : SemanticSystem}
    (old : R → Old)
    (new : R → New)
    (project : New → Old)
    (realize : SemanticRealization New S)
    (interpret : SemanticInterpretation R S)
    (causeable : SemanticCauseableTransition S.State)
    (B : SemanticBoundary S)
    (hRepair :
      RepairAdequacy
        old
        new
        project
        realize
        interpret
        causeable)
    (hMediation :
      RepairMediation new realize B) :
    SemanticMediatedCausalCoverage
      S
      B
      realize
      (fun _ => True)
      causeable := by
  intro x y hCause

  obtain ⟨r, hrx, hry⟩ :=
    hRepair.causeable_complete x y hCause

  obtain ⟨hSource, hTarget⟩ :=
    hRepair.realization_agrees r

  have hStep :
      BoundaryMediatedStep S B
        (realize (new r)).source
        (realize (new r)).target :=
    hMediation r

  refine ⟨new r, trivial, hStep, ?_, ?_⟩
  · exact hSource.trans hrx
  · exact hTarget.trans hry

/--
The mediation condition is independent of causal coverage: it speaks
only about the realized transition generated by each represented
request.
-/
theorem repair_mediation_is_not_defined_as_causal_coverage :
    ∀
      {R New : Type}
      {S : SemanticSystem}
      (new : R → New)
      (realize : SemanticRealization New S)
      (B : SemanticBoundary S),
      RepairMediation new realize B →
      True := by
  intro R New S new realize B hMediation
  trivial

/--
A repair is discharge-adequate when every discharged refined request
preserves the semantic guarantee across its realized boundary-mediated
transition.

This is deliberately an explicit repair obligation. It is not defined in
terms of DARM admissibility or the target assurance conclusion.
-/
def RepairDischargeAdequate
    {R New : Type}
    {S : SemanticSystem}
    (G : SemanticGuarantee S)
    (B : SemanticBoundary S)
    (new : R → New)
    (realize : SemanticRealization New S)
    (discharge : New → Prop) : Prop :=
  ∀ r,
    discharge (new r) →
    BoundaryMediatedStep S B
      (realize (new r)).source
      (realize (new r)).target →
    G.property (realize (new r)).source →
    G.property (realize (new r)).target

/--
Realization faithfulness, relevant transition adequacy, and discharge
adequacy jointly establish the semantic realization adequacy interface
required by R20.

The request-level RepairAdequacy and RepairMediation results remain
separate R21 results. This theorem composes the dependency-level semantic
obligations needed by the R20 assurance theorem.
-/
theorem repair_obligations_imply_semantic_realization_adequacy
    {D : Type}
    {S : SemanticSystem}
    {G : SemanticGuarantee S}
    (realize : SemanticRealization D S)
    (B : SemanticBoundary S)
    (relevant : SemanticDependency D S.State → Prop)
    (discharge : D → Prop)
    (hFaithful :
      RealizationFaithful realize)
    (hTransition :
      RelevantRealizationsTransitionAdequate
        S
        B
        realize
        relevant)
    (hDischarge :
      RealizationDischargeAdequate
        S
        G
        B
        realize
        discharge) :
    SemanticRealizationAdequate
      S
      G
      B
      realize
      relevant
      discharge := by
  exact ⟨hFaithful, hTransition, hDischarge⟩

end GRBS.R21RepairAdequacy


#print axioms
  GRBS.R21RepairAdequacy.repair_adequacy_plus_mediation_implies_semantic_mediated_causal_coverage

#print axioms
  GRBS.R21RepairAdequacy.repair_adequacy_implies_causal_coverage

#print axioms
  GRBS.R21RepairAdequacy.repair_obligations_imply_semantic_realization_adequacy
