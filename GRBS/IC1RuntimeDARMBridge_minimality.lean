import DARMCoreCalculus

namespace GRBS.IC1RuntimeDARMBridge

open GRBS
open GRBS.DARMCoreCalculus
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge

/--
IC-1B runtime admission.

This is deliberately abstract. It represents an implementation-level
decision that a runtime request has been admitted.
-/
def RuntimeAdmitted : Prop :=
  True

/--
Runtime-level evidence that is sufficient to establish the
DARM representation obligation.
-/
def RuntimeRepresentationAdequacy
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (c : TransferCandidate F.Dependency) : Prop :=
  DeltaRepresented F g s c

/--
Runtime-level evidence that is sufficient to establish the
DARM boundary-coverage obligation.
-/
def RuntimeCoverageAdequacy
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus) : Prop :=
  DeltaCovered F g s b l

/--
Runtime-level evidence that is sufficient to establish the
DARM semantic-discharge obligation.
-/
def RuntimeDischargeAdequacy
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency) : Prop :=
  DeltaDischarged F g s b l c

/--
The implementation-level correspondence is now explicitly decomposed
into three independently removable adequacy conditions.
-/
structure RuntimeDARMAdequacy
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency) : Prop where

  represented :
    RuntimeRepresentationAdequacy F g s c

  covered :
    RuntimeCoverageAdequacy F g s b l

  discharged :
    RuntimeDischargeAdequacy F g s b l c

/--
IC-1B conditional refinement theorem.

Once the implementation supplies correspondence evidence for all three
DARM transfer obligations, the runtime admission can legitimately
refine to DARMTransferAdmissible.

The theorem deliberately does not infer the correspondence obligations
from the runtime admission itself.
-/
theorem runtime_admission_refines_to_darm
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency)
    (hCorrespondence : RuntimeDARMAdequacy F g s b l c) :
    DARMTransferAdmissible F g s b l c := by

  exact ⟨
    hCorrespondence.represented,
    hCorrespondence.covered,
    hCorrespondence.discharged
  ⟩

/--
All three independently stated runtime adequacy conditions are sufficient
for DARM transfer admissibility.
-/
theorem adequacy_all_three_implies_darm
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency)
    (hRepresentation :
      RuntimeRepresentationAdequacy F g s c)
    (hCoverage :
      RuntimeCoverageAdequacy F g s b l)
    (hDischarge :
      RuntimeDischargeAdequacy F g s b l c) :
    DARMTransferAdmissible F g s b l c := by

  exact ⟨hRepresentation, hCoverage, hDischarge⟩

/--
Removing representation adequacy leaves DARM admissibility
unjustified in the general case.
-/
theorem representation_adequacy_is_necessary :
    ¬ (
      ∀
        (F : Frame)
        (g : F.Guarantee)
        (s : F.System)
        (b : F.Boundary)
        (l : F.Locus)
        (c : TransferCandidate F.Dependency),
        RuntimeCoverageAdequacy F g s b l →
        RuntimeDischargeAdequacy F g s b l c →
        DARMTransferAdmissible F g s b l c
    ) := by

  intro hUniversal

  let F : Frame :=
    { Trace := Unit
      Guarantee := Unit
      System := Unit
      Boundary := Unit
      Locus := Unit
      Dependency := Bool
      Environment := Unit
      Safe := fun _ _ => True
      dep := fun _ _ d => d
      cov := fun _ _ _ _ => True
      Envs := fun _ _ => True
      Traces := fun _ _ _ _ => True
      Perturbs := fun _ _ => True }

  let c : TransferCandidate F.Dependency :=
    { source := fun _ => False
      target := fun _ => True
      property := fun _ => True }

  have hCoverage :
      RuntimeCoverageAdequacy F () () () () := by
    simp [RuntimeCoverageAdequacy, DeltaCovered, GRBS, F]

  have hDischarge :
      RuntimeDischargeAdequacy F () () () () c := by
    intro d hDep hCov
    simp [RuntimeDischargeAdequacy, DeltaDischarged,
      CoveredDischargesProperty, F, c]

  have hDARM :
      DARMTransferAdmissible F () () () () c :=
    hUniversal F () () () () c hCoverage hDischarge

  have hRep :
      DeltaRepresented F () () c :=
    hDARM.1

  have hDeltaFalse :
      Delta F.Dependency c.source c.target false := by
    simp [Delta, F, c]

  have hDepFalse :
      F.dep () () false :=
    hRep false hDeltaFalse

  simp [F] at hDepFalse

/--
Removing coverage adequacy leaves DARM admissibility
unjustified in the general case.
-/
theorem coverage_adequacy_is_necessary :
    ¬ (
      ∀
        (F : Frame)
        (g : F.Guarantee)
        (s : F.System)
        (b : F.Boundary)
        (l : F.Locus)
        (c : TransferCandidate F.Dependency),
        RuntimeRepresentationAdequacy F g s c →
        RuntimeDischargeAdequacy F g s b l c →
        DARMTransferAdmissible F g s b l c
    ) := by

  intro hUniversal

  let F : Frame :=
    { Trace := Unit
      Guarantee := Unit
      System := Unit
      Boundary := Unit
      Locus := Unit
      Dependency := Unit
      Environment := Unit
      Safe := fun _ _ => True
      dep := fun _ _ _ => True
      cov := fun _ _ _ _ => False
      Envs := fun _ _ => True
      Traces := fun _ _ _ _ => True
      Perturbs := fun _ _ => True }

  let c : TransferCandidate F.Dependency :=
    { source := fun _ => False
      target := fun _ => True
      property := fun _ => True }

  have hRepresentation :
      RuntimeRepresentationAdequacy F () () c := by
    intro d
    simp [RuntimeRepresentationAdequacy, DeltaSubsetDependency,
      Delta, F, c]

  have hDischarge :
      RuntimeDischargeAdequacy F () () () () c := by
    intro d hDep hCov
    exact True.intro

  have hDARM :
      DARMTransferAdmissible F () () () () c :=
    hUniversal F () () () () c hRepresentation hDischarge

  have hCoverageDARM :
      DeltaCovered F () () () () :=
    hDARM.2.1

  have hFalse : False := by
    have h := hCoverageDARM ()
    exact h (by simp [F])

  exact hFalse

/--
Consequent assurance theorem.

If the source is assured and the runtime admission has a complete
DARM correspondence, the existing DARM conservation theorem yields
the target assurance.
-/
theorem runtime_admission_preserves_assurance
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency)
    (hSource :
      SourceAssured F.Dependency c.source c.property)
    (hCorrespondence :
      RuntimeDARMAdequacy F g s b l c) :
    TargetAssured F.Dependency c.target c.property := by

  have hDARM :
      DARMTransferAdmissible F g s b l c :=
    runtime_admission_refines_to_darm
      F g s b l c
      hCorrespondence

  exact darm_admissibility_preserves_assurance
    F g s b l c
    hSource
    hDARM

theorem discharge_adequacy_is_necessary :
    ¬ (
      ∀
        (F : Frame)
        (g : F.Guarantee)
        (s : F.System)
        (b : F.Boundary)
        (l : F.Locus)
        (c : TransferCandidate F.Dependency),
        RuntimeRepresentationAdequacy F g s c →
        RuntimeCoverageAdequacy F g s b l →
        DARMTransferAdmissible F g s b l c
    ) := by

  intro hUniversal

  let F : Frame :=
    { Trace := Unit
      Guarantee := Unit
      System := Unit
      Boundary := Unit
      Locus := Unit
      Dependency := Unit
      Environment := Unit
      Safe := fun _ _ => False
      dep := fun _ _ _ => True
      cov := fun _ _ _ _ => True
      Envs := fun _ _ => True
      Traces := fun _ _ _ _ => True
      Perturbs := fun _ _ => True }

  let c : TransferCandidate F.Dependency :=
    { source := fun _ => False
      target := fun _ => True
      property := fun _ => False }

  have hRepresentation :
      RuntimeRepresentationAdequacy F () () c := by
    intro d
    simp [RuntimeRepresentationAdequacy, DeltaSubsetDependency,
      Delta, F, c]

  have hCoverage :
      RuntimeCoverageAdequacy F () () () () := by
    intro d
    simp [RuntimeCoverageAdequacy, DeltaCovered, GRBS, F]

  have hDARM :
      DARMTransferAdmissible F () () () () c :=
    hUniversal F () () () () c hRepresentation hCoverage

  have hDischarge :
      DeltaDischarged F () () () () c :=
    hDARM.2.2

  have hFalse : False := by
    have h := hDischarge ()
    exact h (by simp [F]) (by simp [F])

  exact hFalse

end GRBS.IC1RuntimeDARMBridge


#print axioms GRBS.IC1RuntimeDARMBridge.representation_adequacy_is_necessary

#print axioms GRBS.IC1RuntimeDARMBridge.adequacy_all_three_implies_darm
#print axioms GRBS.IC1RuntimeDARMBridge.representation_adequacy_is_necessary
#print axioms GRBS.IC1RuntimeDARMBridge.coverage_adequacy_is_necessary
#print axioms GRBS.IC1RuntimeDARMBridge.discharge_adequacy_is_necessary
