import DARMCoreCalculus

namespace GRBS.IC1RuntimeDARMBridge

open GRBS
open GRBS.DARMCoreCalculus
open GRBS.R5AssuranceConservation

/--
IC-1B runtime admission.

This is deliberately abstract. It represents an implementation-level
decision that a runtime request has been admitted.
-/
def RuntimeAdmitted : Prop :=
  True

/--
Implementation-to-DARM correspondence obligations.

Each component corresponds directly to one conjunct of
DARMTransferAdmissible:

  represented  -> DeltaRepresented
  covered      -> DeltaCovered
  discharged   -> DeltaDischarged

No implication from runtime admission to these obligations is assumed
here. They are explicit correspondence hypotheses.
-/
structure RuntimeDARMCorrespondence
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency) : Prop where

  represented :
    DeltaRepresented F g s c

  covered :
    DeltaCovered F g s b l

  discharged :
    DeltaDischarged F g s b l c

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
    (hCorrespondence : RuntimeDARMCorrespondence F g s b l c) :
    DARMTransferAdmissible F g s b l c := by

  exact ⟨
    hCorrespondence.represented,
    hCorrespondence.covered,
    hCorrespondence.discharged
  ⟩

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
      RuntimeDARMCorrespondence F g s b l c) :
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

end GRBS.IC1RuntimeDARMBridge
