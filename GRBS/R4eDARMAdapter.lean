import R4eBoundaryComposition
import R5R4Correspondence
import DARMCoreCalculus

namespace GRBS.R4eDARMAdapter

open GRBS
open GRBS.DARMCoreCalculus
open GRBS.R6GRBSDeltaBridge

/-- Minimal DARM frame faithfully representing the R4e dependency/coverage
    counterexample.

    The DARM property being transferred here is the R4e structural coverage
    predicate `CovAB`. This adapter does not identify structural coverage
    with semantic safety `G_AB`.
-/
def r4eFrame : Frame where
  Trace := GRBS.R4eBoundaryComposition.Tr
  Guarantee := Unit
  System := Unit
  Boundary := Unit
  Locus := Unit
  Dependency := GRBS.R4eBoundaryComposition.Dependency
  Environment := Unit
  Safe := fun _ t => GRBS.R4eBoundaryComposition.G_AB t
  dep := fun _ _ d => GRBS.R4eBoundaryComposition.DepAB d
  cov := fun _ _ _ d => GRBS.R4eBoundaryComposition.CovAB d
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

/-- The R4e delta is represented by the frame dependency relation. -/
theorem r4e_delta_is_represented :
    DeltaSubsetDependency
      r4eFrame
      ()
      ()
      GRBS.R5R4Correspondence.R4eCorrespondence.R4eSourceDomain
      GRBS.R5R4Correspondence.R4eCorrespondence.R4eTargetDomain := by
  intro d hd
  exact hd.1

/-- The composed boundary's coverage predicate is exactly the frame's
    coverage relation. -/
theorem r4e_property_is_frame_coverage :
    ∀ d : r4eFrame.Dependency,
      r4eFrame.cov () () () d ↔
        GRBS.R4eBoundaryComposition.CovAB d := by
  intro d
  rfl

/-- The R4e interaction is a represented R5 delta whose required property
    fails. -/
theorem r4e_interaction_is_undischarged :
    GRBS.R5AssuranceConservation.Delta
        r4eFrame.Dependency
        GRBS.R5R4Correspondence.R4eCorrespondence.R4eSourceDomain
        GRBS.R5R4Correspondence.R4eCorrespondence.R4eTargetDomain
        GRBS.R4eBoundaryComposition.Dependency.interactionAB
    ∧
    ¬ GRBS.R4eBoundaryComposition.CovAB
        GRBS.R4eBoundaryComposition.Dependency.interactionAB := by
  exact
    ⟨
      GRBS.R5R4Correspondence.R4eCorrespondence.interaction_is_r5_delta,
      GRBS.R4eBoundaryComposition.interaction_uncovered_composition
    ⟩

/-- The R4e composed boundary is not GRBS because its interaction dependency
    is structurally required but uncovered. -/
theorem r4e_frame_not_grbs :
    ¬ GRBS r4eFrame () () () () := by
  intro hGRBS
  have hDep :
      r4eFrame.dep () () GRBS.R4eBoundaryComposition.Dependency.interactionAB := by
    trivial
  have hCov :
      r4eFrame.cov () () ()
        GRBS.R4eBoundaryComposition.Dependency.interactionAB :=
    hGRBS
      GRBS.R4eBoundaryComposition.Dependency.interactionAB
      hDep
  exact
    GRBS.R4eBoundaryComposition.interaction_uncovered_composition hCov

/-- The canonical R4e transfer candidate, expressed through DARM Core. -/
def r4eTransferCandidate :
    TransferCandidate r4eFrame.Dependency where
  source :=
    GRBS.R5R4Correspondence.R4eCorrespondence.R4eSourceDomain
  target :=
    GRBS.R5R4Correspondence.R4eCorrespondence.R4eTargetDomain
  property :=
    GRBS.R4eBoundaryComposition.CovAB

/-- The R4e counterexample cannot satisfy DARM transfer admissibility.

    The failure is structural: DARM's `DeltaCovered` conjunct is `GRBS`,
    while the R4e interaction dependency is required by the composed
    boundary but is not covered.
-/
theorem r4e_transfer_not_admissible :
    ¬ DARMTransferAdmissible
        r4eFrame
        ()
        ()
        ()
        ()
        r4eTransferCandidate := by
  intro hAdmissible
  exact r4e_frame_not_grbs hAdmissible.2.1

/-- The three-part R16 transfer condition, when expanded through the
    underlying R6 predicates, is definitionally the same transfer condition
    used by DARM Core. -/
theorem r16_style_transfer_is_darm
    (c : TransferCandidate r4eFrame.Dependency) :
    (
      GRBS r4eFrame () () () () ∧
      DeltaSubsetDependency
        r4eFrame
        ()
        ()
        c.source
        c.target ∧
      CoveredDischargesProperty
        r4eFrame
        ()
        ()
        ()
        ()
        c.property
    ) ↔
    DARMTransferAdmissible
      r4eFrame
      ()
      ()
      ()
      ()
      c := by
  constructor
  · intro h
    rcases h with ⟨hGRBS, hDelta, hDischarge⟩
    exact ⟨hDelta, hGRBS, hDischarge⟩
  · intro h
    rcases h with ⟨hDelta, hGRBS, hDischarge⟩
    exact ⟨hGRBS, hDelta, hDischarge⟩

end GRBS.R4eDARMAdapter
