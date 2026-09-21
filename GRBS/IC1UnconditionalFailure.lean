import DARMCoreCalculus

namespace GRBS.IC1UnconditionalFailure

open GRBS
open GRBS.DARMCoreCalculus
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge

/--
A runtime admission decision, deliberately abstracted away from
the DARM semantic obligations.
-/
def RuntimeAdmitted : Prop :=
  True

/--
A concrete frame in which the semantic discharge condition fails.

The single dependency is represented and covered, but the property
required by semantic discharge is false.
-/
def FailureFrame : Frame where
  Trace := Unit
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

  Perturbs := fun _ _ => True

/--
The transfer candidate introduces the single dependency.
-/
def candidate : TransferCandidate FailureFrame.Dependency where
  source := fun _ => False
  target := fun _ => True
  property := fun _ => False

/--
The structural representation obligation holds.
-/
theorem representation_holds :
    DeltaRepresented
      FailureFrame
      ()
      ()
      candidate := by
  intro d
  simp [DeltaRepresented, DeltaSubsetDependency, Delta, candidate, FailureFrame]

/--
Boundary coverage holds.
-/
theorem coverage_holds :
    DeltaCovered
      FailureFrame
      ()
      ()
      ()
      () := by
  intro d
  simp [DeltaCovered, GRBS, FailureFrame]

/--
Semantic discharge fails because the required property is false
for the covered dependency.
-/
theorem discharge_fails :
    ¬ DeltaDischarged
      FailureFrame
      ()
      ()
      ()
      ()
      candidate := by
  intro hDischarged
  have hProperty :
      candidate.property () :=
    hDischarged ()
      (by simp [FailureFrame])
      (by simp [FailureFrame])
  exact hProperty

/--
Therefore runtime admission can hold while DARM transfer
admissibility fails.
-/
theorem runtime_admitted_but_darm_not_admissible :
    RuntimeAdmitted ∧
      ¬ DARMTransferAdmissible
        FailureFrame
        ()
        ()
        ()
        ()
        candidate := by

  constructor
  · trivial

  · intro hAdmissible
    exact discharge_fails hAdmissible.2.2

/--
The unconditional runtime-to-DARM bridge is impossible in general:
runtime admission alone does not entail DARM transfer admissibility.
-/
theorem no_unconditional_runtime_to_darm_bridge :
    ¬ (
      ∀
        (F : Frame)
        (g : F.Guarantee)
        (s : F.System)
        (b : F.Boundary)
        (l : F.Locus)
        (c : TransferCandidate F.Dependency),
        RuntimeAdmitted →
        DARMTransferAdmissible F g s b l c
    ) := by

  intro hUniversal

  have hAdmissible :
      DARMTransferAdmissible
        FailureFrame
        ()
        ()
        ()
        ()
        candidate :=
    hUniversal
      FailureFrame
      ()
      ()
      ()
      ()
      candidate
      trivial

  exact discharge_fails hAdmissible.2.2

end GRBS.IC1UnconditionalFailure

#print axioms GRBS.IC1UnconditionalFailure.representation_holds
#print axioms GRBS.IC1UnconditionalFailure.coverage_holds
#print axioms GRBS.IC1UnconditionalFailure.discharge_fails
#print axioms GRBS.IC1UnconditionalFailure.runtime_admitted_but_darm_not_admissible

#print axioms GRBS.IC1UnconditionalFailure.no_unconditional_runtime_to_darm_bridge
