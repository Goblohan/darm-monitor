/-
  2a — the ABOVE-INTERFACE REDUCTION theorem, and the characterization pair.

  Companion to R3b-2b (AGBypass.lean, the below-interface separation). Together
  they characterize, WITHIN THE EXPLICITLY DEFINED OBSERVATIONAL MODEL, whether a
  coverage difference is behaviorally exposed to assume-guarantee reasoning.

  KEY HONESTY FIX (parameterized mediation semantics):
    Coverage's behavioral effect is NOT baked into the trace semantics. Instead a
    mediation semantics
        M : RawBehavior -> Coverage -> ObservableBehavior
    is a PARAMETER, and `CoverageSensitive M d` is an EXPLICIT HYPOTHESIS. The
    theorem then says: FOR ANY mediation semantics sensitive to `d`, a coverage
    difference on an interface-reachable `d` is observably exposed. This is a
    derivation, not a stipulation. It does NOT claim "AG subsumes DARM above the
    interface" — only that a coverage-sensitive effect on a reachable channel is
    AG-recoverable.

  DISTINCT PREDICATES (never collapsed):
    ReachI d            — d is drivable by some interface action
    CoverageDiff s1 s2 d — the two systems differ on covering d
    CoverageSensitive M d — M's observable output depends on d's coverage
    TraceVisible ...    — the systems produce different observable traces
    AGDistinguishable   — some AG assumption separates them

  PRIMARY FRAMING (the harder-to-attack claim): two systems can be
  indistinguishable under the software-contract observation boundary while
  differing in physical authority structure. Interface reachability is what
  determines which side of that boundary a coverage difference falls on.

  NOT a biconditional "GRBS reduces iff interface-reachable" — that is stronger
  than proved. This is a characterization over the specified model.
-/

namespace GRBS
namespace AGReduction

abbrev Action := Nat
abbrev Channel := Nat

/-- Raw (pre-mediation) physical behavior: which channel an environment drives,
    abstractly. `raw e` is the channel the environment's actions target (if any).
    We keep it minimal: an environment raw-drives a channel. -/
abbrev RawBehavior := Action → Channel → Prop

/-- Observable behavior: a predicate producing an observable trace value. We use
    a two-valued observable (safe / violation) for the characterization; the
    point is that M MAY or MAY NOT let coverage affect it. -/
inductive Obs where
  | safe
  | violation
deriving DecidableEq

/-- A **mediation semantics** maps (was the channel driven?, is it covered?) to an
    observable outcome. This is the PARAMETER. Different M encode different
    mediation disciplines; `CoverageSensitive` picks out those where coverage
    actually changes the observable. -/
abbrev Mediation := (driven : Prop) → (covered : Prop) → Obs

/-- `ReachI iface d`: channel `d` is reachable through the interface — there is an
    interface action `a` (in `iface`) that drives `d`. -/
def ReachI (iface : Action → Prop) (drives : RawBehavior) (d : Channel) : Prop :=
  ∃ a : Action, iface a ∧ drives a d

/-- The observable trace of a system under environment `e`, given a mediation
    semantics `M`, coverage `cov`, and raw behavior `drives`: for channel `d`,
    apply `M` to (whether `e` drives `d`) and (whether `d` is covered). We phrase
    the observable at a fixed channel of interest. -/
def observeAt
    (M : Mediation) (drives : RawBehavior) (cov : Channel → Prop)
    (e : Action) (d : Channel) : Obs :=
  M (drives e d) (cov d)

/-- **CoverageSensitive M d (at a driven channel).** When the channel IS driven,
    M's observable differs between covered and uncovered. This is the explicit
    hypothesis that coverage has a real mediation EFFECT — supplied, not assumed
    globally. -/
def CoverageSensitive (M : Mediation) : Prop :=
  M True True ≠ M True False

/-- **Above-interface reduction theorem.**
    Given a mediation semantics `M` that is coverage-sensitive, an interface
    action `a` that drives channel `d` (so `d` is interface-reachable and the
    driving environment is admissible), and two coverage assignments differing on
    `d` (`cov1 d` true, `cov2 d` false), the observable traces differ:
        observeAt M drives cov1 a d ≠ observeAt M drives cov2 a d.
    Hence an AG observation model over interface behavior distinguishes the two
    systems. The trace difference is DERIVED from `CoverageSensitive`, not
    stipulated. -/
theorem above_interface_reduction
    (M : Mediation) (drives : RawBehavior)
    (d : Channel) (a : Action)
    (hDrives : drives a d)
    (hSens : CoverageSensitive M)
    (cov1 cov2 : Channel → Prop)
    (hcov1 : cov1 d) (hcov2 : ¬ cov2 d) :
    observeAt M drives cov1 a d ≠ observeAt M drives cov2 a d := by
  simp only [observeAt]
  have e1 : drives a d = True := propext ⟨fun _ => trivial, fun _ => hDrives⟩
  have e2 : cov1 d = True := propext ⟨fun _ => trivial, fun _ => hcov1⟩
  have e3 : cov2 d = False := propext ⟨fun h => hcov2 h, fun h => h.elim⟩
  rw [e1, e2, e3]
  exact hSens

/-- Corollary framing: interface reachability supplies the admissible driving
    action, so under a coverage-sensitive mediation the two systems are
    observationally distinguished through the interface. -/
theorem reachable_coverage_is_observable
    (M : Mediation) (drives : RawBehavior) (iface : Action → Prop)
    (d : Channel)
    (hReach : ReachI iface drives d)
    (hSens : CoverageSensitive M)
    (cov1 cov2 : Channel → Prop)
    (hcov1 : cov1 d) (hcov2 : ¬ cov2 d) :
    ∃ a : Action, iface a ∧
      observeAt M drives cov1 a d ≠ observeAt M drives cov2 a d := by
  obtain ⟨a, hIface, hDrives⟩ := hReach
  exact ⟨a, hIface, above_interface_reduction M drives d a hDrives hSens cov1 cov2 hcov1 hcov2⟩

end AGReduction
end GRBS
