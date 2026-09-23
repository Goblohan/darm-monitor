import E23TMCPhysicalComposition
import AGBypass

namespace GRBS.E23AGBypassCorrespondence

open GRBS.E17ProposalAuthoritySeparation
open GRBS.E23TMCRefinement
open GRBS.E23TMCPhysicalComposition
open GRBS.AGBypass
open GRBS.AGBypass.Witness

/-
  E23-C: AGBypass physical realization boundary.

  AGBypass supplies physical channel -> trace behavior.
  E23 TMC requires state -> state transitions.

  Therefore the missing physical realization must explicitly
  contain both a source state and a target state. The source state
  is NOT supplied by AGBypass itself; it is therefore part of the
  realization object rather than silently inferred.
-/

/-- Explicit realization of one physical observation as a state transition. -/
structure PhysicalTransitionRealization where
  source : St
  channel : Ch
  trace : Tr
  target : St

/-
  Trace realization supplied by E23.

  This maps an observed physical trace into the modeled state
  reached by that observation.
-/
def TraceStateRealization : Tr → St
  | Tr.ok => St.safe
  | Tr.violated => St.compromised

/-
  Physical realization evidence.

  Notice that AGBypass can establish the physical trace and E23 can
  establish the trace-to-state target, but neither supplies a
  source-state transition semantics.
-/
def PhysicallyRealizes (r : PhysicalTransitionRealization) : Prop :=
  AGBypass.Witness.S2.physicalStep r.channel r.trace
  ∧ TraceStateRealization r.trace = r.target

/-
  State-transition relation induced by the explicitly supplied
  physical realization records.
-/
def agPhysicalRealizedTransition (s s' : St) : Prop :=
  ∃ r : PhysicalTransitionRealization,
    r.source = s
    ∧ r.target = s'
    ∧ PhysicallyRealizes r

/-
  A concrete physical realization record assigning the AGBypass
  violation to a safe -> compromised transition.
-/
def s2BypassRealization : PhysicalTransitionRealization :=
  { source := St.safe
    channel := Ch.d0
    trace := Tr.violated
    target := St.compromised }

/-
  The AGBypass witness establishes the physical part and the
  trace-to-state realization establishes the target.
-/
theorem s2_bypass_realization_holds :
    PhysicallyRealizes s2BypassRealization := by
  constructor
  · rfl
  · rfl

/-
  Therefore the explicitly supplied realization induces the
  safe -> compromised transition.
-/
theorem s2_physical_bypass_reaches_compromised :
    agPhysicalRealizedTransition St.safe St.compromised := by
  refine ⟨s2BypassRealization, rfl, rfl, ?_⟩
  exact s2_bypass_realization_holds

/-
  The gated implementation cannot produce the corresponding
  safe -> compromised transition.
-/
theorem gated_implementation_blocks_s2_bypass :
    ¬ gatedActualStep St.safe St.compromised := by
  intro h
  rcases h with ⟨p, hp⟩
  cases p <;>
    simp [GatedStep, resolve, authorized, step] at hp

/-
  Consequently, the explicitly realized AGBypass transition is
  not contained in the mediated implementation transition relation.
-/
theorem agPhysical_not_implementation_correspondent :
    ¬ PhysicalImplementationCorrespondence
      agPhysicalRealizedTransition gatedActualStep := by
  intro h
  have hc :=
    h St.safe St.compromised
      s2_physical_bypass_reaches_compromised
  exact gated_implementation_blocks_s2_bypass hc

/-
  The same explicitly realized physical transition violates TMC.
-/
theorem agPhysical_fails_tmc :
    ¬ TMC agPhysicalRealizedTransition permittedStep := by
  intro h
  have hp :=
    h St.safe St.compromised
      s2_physical_bypass_reaches_compromised
  rcases hp with hpermitted | hstutter
  · rcases hpermitted with ⟨p, hAuth, hStep⟩
    cases p <;>
      simp [resolve, authorized, step] at hAuth hStep
  · simp at hstutter

/-
  E23-C result.

  The AGBypass model supplies a physical channel -> trace witness.
  After an explicit, source-aware trace-to-state realization is
  supplied, that witness yields a transition not represented by
  the gated implementation.

  The source state is deliberately explicit because AGBypass
  itself does not provide source-state transition semantics.
  Therefore the physical -> implementation correspondence remains
  a separate assurance obligation.
-/
theorem e23c_agbypass_exposes_missing_correspondence :
    agPhysicalRealizedTransition St.safe St.compromised
    ∧ ¬ PhysicalImplementationCorrespondence
        agPhysicalRealizedTransition gatedActualStep
    ∧ ¬ TMC agPhysicalRealizedTransition permittedStep :=
  ⟨s2_physical_bypass_reaches_compromised,
   agPhysical_not_implementation_correspondent,
   agPhysical_fails_tmc⟩

end GRBS.E23AGBypassCorrespondence
