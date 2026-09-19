import GRBS.E23TMCRefinement

namespace GRBS.E23TMCPhysicalComposition

open GRBS.E17ProposalAuthoritySeparation
open GRBS.E23TMCRefinement

/-
  Physical-to-implementation correspondence.

  This is deliberately an explicit premise. It says that every
  physical transition relevant to the implementation is represented
  by the implementation transition relation.
-/
def PhysicalImplementationCorrespondence
    (physicalStep implementationStep : St → St → Prop) : Prop :=
  ∀ s s', physicalStep s s' → implementationStep s s'

/-
  TMC composition.

  If every physical transition is represented by an implementation
  transition, and every implementation transition is permitted,
  then every physical transition is permitted.
-/
theorem physical_tmc_of_correspondence_and_implementation_tmc
    (physicalStep implementationStep permittedStep : St → St → Prop)
    (hPhysical :
      PhysicalImplementationCorrespondence physicalStep implementationStep)
    (hTMC :
      TMC implementationStep permittedStep) :
    TMC physicalStep permittedStep := by
  intro s s' hPhysicalStep
  exact hTMC s s' (hPhysical s s' hPhysicalStep)

/-
  Concrete physical transition relation for the mediated implementation.

  Here we deliberately model the physical layer as corresponding
  exactly to the gated implementation. This is a positive control:
  the composition theorem should recover physical TMC.
-/
def mediatedPhysicalStep (s s' : St) : Prop :=
  gatedActualStep s s'

theorem mediated_physical_implementation_correspondence :
    PhysicalImplementationCorrespondence
      mediatedPhysicalStep gatedActualStep := by
  intro s s' h
  exact h

theorem mediated_physical_tmc :
    TMC mediatedPhysicalStep permittedStep := by
  apply physical_tmc_of_correspondence_and_implementation_tmc
    mediatedPhysicalStep gatedActualStep permittedStep
    mediated_physical_implementation_correspondence
    gated_implementation_satisfies_tmc

/-
  Negative control.

  Define a physical transition that can directly execute the
  unauthorized action. This transition is not contained in the
  gated implementation relation.
-/
def bypassPhysicalStep (s s' : St) : Prop :=
  step s (resolve Proposal.execCode) = s'

theorem bypass_physical_not_implementation_correspondent :
    Not (PhysicalImplementationCorrespondence
      bypassPhysicalStep gatedActualStep) := by
  intro h
  have hCorrespond :=
    h St.safe St.compromised
      (by simp [bypassPhysicalStep, resolve, step])
  rcases hCorrespond with ⟨p, hp⟩
  cases p <;> simp [GatedStep, resolve, authorized, step] at hp

/-
  The bypass physical transition also violates TMC.
-/
theorem bypass_physical_fails_tmc :
    Not (TMC bypassPhysicalStep permittedStep) := by
  intro h
  have htmc :=
    h St.safe St.compromised
      (by simp [bypassPhysicalStep, resolve, step])
  rcases htmc with hpermitted | hstutter
  · rcases hpermitted with ⟨p, hAuth, hStep⟩
    cases p <;> simp [resolve, authorized, step] at hAuth hStep
  · simp at hstutter

/-
  E23-B result.

  Positive control:
    physical correspondence + implementation TMC -> physical TMC.

  Negative control:
    a physical bypass need not correspond to the mediated
    implementation and can violate TMC.
-/
theorem e23b_physical_composition_experiment :
    TMC mediatedPhysicalStep permittedStep
    ∧ Not (
        PhysicalImplementationCorrespondence
          bypassPhysicalStep gatedActualStep)
    ∧ Not (TMC bypassPhysicalStep permittedStep) :=
  ⟨mediated_physical_tmc,
   bypass_physical_not_implementation_correspondent,
   bypass_physical_fails_tmc⟩

end GRBS.E23TMCPhysicalComposition
