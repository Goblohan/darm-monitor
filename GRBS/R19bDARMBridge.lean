import DARMCoreCalculus
import R19bSemanticDependencyBridge

namespace GRBS.R19bDARMBridge

open GRBS
open GRBS.DARMCoreCalculus
open GRBS.R6GRBSDeltaBridge
open GRBS.R19bSemanticDependencyBridge

/--
The structural dependencies covered by DARM at a boundary and locus.
A dependency is covered only when it is both guarantee-relative and
covered by the applicable boundary/locus.
-/
def DARMCoveredDependencies
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus) : F.Dependency → Prop :=
  fun d => F.dep g s d ∧ F.cov b l s d

/--
DARM's semantic discharge predicate for a transfer candidate.
-/
def DARMDischarge
    {F : Frame}
    (c : TransferCandidate F.Dependency) : F.Dependency → Prop :=
  c.property

/--
DARM's discharge condition induces the R19b structural discharge
condition over dependencies that are both relevant and boundary-covered.
-/
theorem darm_deltaDischarged_implies_r19b_coveredDependenciesDischarged
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency)
    (hDischarged : DeltaDischarged F g s b l c) :
    CoveredDependenciesDischarged
      (DARMCoveredDependencies F g s b l)
      (DARMDischarge c) := by
  intro d hCovered
  exact hDischarged d hCovered.1 hCovered.2

/--
If DARM discharges the structural dependencies and the assurance
producer supplies the R19b adequacy relation, semantic preservation
follows for every relevant semantic dependency.
-/
theorem darm_transfer_plus_discharge_adequacy_implies_semantic_preservation
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency)
    (State : Type)
    (relevant :
      SemanticDependency F.Dependency State → Prop)
    (preserves :
      SemanticDependency F.Dependency State → Prop)
    (hAdmissible :
      DARMTransferAdmissible F g s b l c)
    (hAdequate :
      DischargeAdequate
        (DARMDischarge c)
        preserves)
    (hRelevantCovered :
      RelevantDependenciesCovered
        relevant
        (DARMCoveredDependencies F g s b l)) :
    SemanticPreservation relevant preserves := by
  exact
    covered_and_discharged_imply_semantic_preservation
      relevant
      (DARMCoveredDependencies F g s b l)
      (DARMDischarge c)
      preserves
      hRelevantCovered
      (darm_deltaDischarged_implies_r19b_coveredDependenciesDischarged
        F g s b l c
        hAdmissible.2.2)
      hAdequate

end GRBS.R19bDARMBridge
