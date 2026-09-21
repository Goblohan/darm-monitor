import R22RuntimeSemanticCorrespondence

namespace GRBS.R22PositiveRepair

open GRBS
open GRBS.R20DARMToSemanticCorrespondence
open GRBS.R21RepairAdequacy
open GRBS.R22RuntimeSemanticCorrespondence

/--
R22-K positive semantic repair model.

The repaired representation carries enough information to identify the
semantic transition, and the mediated transition preserves the semantic
guarantee.
-/
structure SafeState where
  argument : Nat

def safeAuthorized (s : SafeState) : Prop :=
  s.argument = 0

def safeSystem : SemanticSystem where
  State := SafeState
  Step := fun x y =>
    x.argument = 0 ∧ y.argument = 0

def safeGuarantee : SemanticGuarantee safeSystem where
  property := safeAuthorized

def safeBoundary : SemanticBoundary safeSystem where
  mediated := fun x y =>
    x.argument = 0 ∧ y.argument = 0

inductive SafeDependency where
  | demoSafe
deriving DecidableEq

def safeRealize :
    SemanticRealization SafeDependency safeSystem :=
  fun d =>
    match d with
    | .demoSafe =>
        {
          dependency := d
          source := { argument := 0 }
          target := { argument := 0 }
        }

def safeRelevant
    (d : SemanticDependency SafeDependency safeSystem.State) : Prop :=
  d.dependency = .demoSafe

def safeDischarge (_ : SafeDependency) : Prop :=
  True


theorem safe_realization_is_faithful :
    RealizationFaithful safeRealize := by
  intro d
  rfl

theorem safe_realization_is_transition_adequate :
    RelevantRealizationsTransitionAdequate
      safeSystem
      safeBoundary
      safeRealize
      safeRelevant := by
  intro d hRelevant
  cases d with
  | demoSafe =>
      constructor
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩

theorem safe_realization_is_discharge_adequate :
    RealizationDischargeAdequate
      safeSystem
      safeGuarantee
      safeBoundary
      safeRealize
      safeDischarge := by
  intro d hDischarge hMediated hSource
  cases d with
  | demoSafe =>
      simp [safeRealize, safeGuarantee, safeAuthorized] at hSource ⊢

theorem safe_semantic_realization_is_adequate :
    SemanticRealizationAdequate
      safeSystem
      safeGuarantee
      safeBoundary
      safeRealize
      safeRelevant
      safeDischarge :=
  ⟨
    safe_realization_is_faithful,
    safe_realization_is_transition_adequate,
    safe_realization_is_discharge_adequate
  ⟩


/--
Minimal structural DARM frame for the positive repair.

The semantic obligations are carried by the R20 model above. The
structural DARM frame is intentionally permissive so that this experiment
isolates the semantic correspondence question rather than introducing
another structural counterexample.
-/
def D : Type := SafeDependency

def darmFrame : Frame where
  Trace := Unit
  Guarantee := Unit
  System := Unit
  Boundary := Unit
  Locus := Unit
  Dependency := D
  Environment := Unit
  Safe := fun _ _ => True
  dep := fun _ _ _ => True
  cov := fun _ _ _ _ => True
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def darmCandidate :
    DARMCoreCalculus.TransferCandidate darmFrame.Dependency where
  source := fun _ => False
  target := fun _ => True
  property := fun _ => True

theorem r22_delta_is_nonempty :
    R5AssuranceConservation.Delta
      darmFrame.Dependency
      darmCandidate.source
      darmCandidate.target
      .demoSafe := by
  simp [R5AssuranceConservation.Delta, darmCandidate]

theorem darm_frame_grbs :
    GRBS darmFrame () () () () := by
  intro d hDependency
  trivial

theorem darm_delta_is_represented :
    R6GRBSDeltaBridge.DeltaSubsetDependency
      darmFrame
      ()
      ()
      darmCandidate.source
      darmCandidate.target := by
  intro d hDelta
  trivial

theorem darm_delta_is_discharged :
    R6GRBSDeltaBridge.CoveredDischargesProperty
      darmFrame
      ()
      ()
      ()
      ()
      darmCandidate.property := by
  intro d hProperty hCovered
  trivial

theorem darm_transfer_is_admissible :
    DARMCoreCalculus.DARMTransferAdmissible
      darmFrame
      ()
      ()
      ()
      ()
      darmCandidate := by
  constructor
  · exact darm_delta_is_represented
  · constructor
    · exact darm_frame_grbs
    · exact darm_delta_is_discharged


/--
The DARM delta property implies the semantic source guarantee for the
realized dependency.
-/
theorem r22_delta_source_correspondence :
    ∀ d,
      R5AssuranceConservation.Delta
        darmFrame.Dependency
        darmCandidate.source
        darmCandidate.target
        d →
      darmCandidate.property d →
      safeGuarantee.property
        (safeRealize d).source := by
  intro d hDelta hProperty
  cases d with
  | demoSafe =>
      simp [safeRealize, safeGuarantee, safeAuthorized]

/--
Every DARM delta dependency is relevant to the repaired semantic
realization.
-/
theorem r22_delta_relevance_correspondence :
    ∀ d,
      R5AssuranceConservation.Delta
        darmFrame.Dependency
        darmCandidate.source
        darmCandidate.target
        d →
      safeRelevant (safeRealize d) := by
  intro d hDelta
  cases d with
  | demoSafe =>
      rfl

/--
Every DARM delta dependency is discharged by the repaired semantic
realization.
-/
theorem r22_delta_discharge_correspondence :
    ∀ d,
      R5AssuranceConservation.Delta
        darmFrame.Dependency
        darmCandidate.source
        darmCandidate.target
        d →
      safeDischarge d := by
  intro d hDelta
  trivial

/--
R22-K positive repair closes through the existing R20 theorem.

The repaired semantic representation, realization, mediation, and
discharge obligations are sufficient for the semantic target guarantee.
-/
theorem r22_positive_repair_preserves_semantic_guarantee :
    ∀ d,
      R5AssuranceConservation.Delta
        darmFrame.Dependency
        darmCandidate.source
        darmCandidate.target
        d →
      safeGuarantee.property
        (safeRealize d).target := by
  apply darm_delta_realizations_preserve_guarantee
    darmFrame
    ()
    ()
    ()
    ()
    darmCandidate
    safeSystem
    safeGuarantee
    safeBoundary
    safeRealize
    safeRelevant
    safeDischarge
  · exact darm_transfer_is_admissible
  · exact safe_semantic_realization_is_adequate
  · exact r22_delta_source_correspondence
  · exact r22_delta_relevance_correspondence
  · exact r22_delta_discharge_correspondence


theorem r22_demoSafe_target_is_guaranteed :
    safeGuarantee.property
      (safeRealize .demoSafe).target := by
  apply r22_positive_repair_preserves_semantic_guarantee
  exact r22_delta_is_nonempty

#print axioms r22_delta_is_nonempty
#print axioms darm_transfer_is_admissible
#print axioms safe_semantic_realization_is_adequate
#print axioms r22_delta_source_correspondence
#print axioms r22_delta_relevance_correspondence
#print axioms r22_delta_discharge_correspondence
#print axioms r22_positive_repair_preserves_semantic_guarantee
#print axioms r22_demoSafe_target_is_guaranteed
