import DarmMonitor.Minimality

/-
  Interference — noninterference as a property of an arbitrary transition
  system, instantiated on BOTH discrete models.

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`.

  THE PROBLEM THIS SOLVES. `Influence.lean` claims to address registered
  assumption A4 from `Basic.lean`. It does not, formally: the two modules
  share no types. `Influence` has its own `Event`, its own `step`, its own
  `isAgent`, and a bespoke three-element `WorldState`. `Basic` has
  `State CapId ActionId`, `Event`, `step`, `actor`. No function maps between
  them and no theorem relates them. The A4 claim was an analogy.

  WHY NOT A SIMULATION BRIDGE. The obvious repair — define
  `interp : State → Sys` and prove a commuting diagram — is expected to fail
  for a reason already recorded. `worldStep _ .actA = .stateA` collapses
  regardless of source state; `Basic.step` does not collapse that way.
  Reconciling a collapsing dynamics with a non-collapsing one is structurally
  the obstruction of Negative Result 2, one level up. Not attempted here.

  WHAT IS DONE INSTEAD. `Influence`'s noninterference definitions are already
  parametric in the observation map and the ratifier; only the STEP FUNCTION is
  hard-wired. Abstracting that one parameter makes the predicate applicable to
  any transition system, including `Basic`'s. The negative results then do not
  need a bespoke world model: a witness over `State`/`step` suffices, and
  `Influence`'s three-element machine becomes a minimal example rather than
  the A4 discharge.

  CONSEQUENCE. A4 and `capInvariant` can now be stated in ONE model, which is
  what cell C4 needed and could not have.
-/

namespace DARM
namespace Interference

/-! ## 1. The general predicate

  Generalizes `DARM.A4.NoninterferingAll` by abstracting the transition
  function, and adds an admissibility predicate so that "the agent's actions"
  can be a strict subset of all actions — which it is in `Basic`, where
  ratification and external suspension are not agent events. -/

/-- **Noninterference, generally.** The ratifier's verdict does not vary
    across anything an admissible actor can cause. -/
def Noninterfering {σ α ω ρ : Type}
    (stp : σ → α → σ) (adm : α → Prop) (obs : σ → ω) (r : ω → ρ) : Prop :=
  ∀ s a₁ a₂, adm a₁ → adm a₂ → r (obs (stp s a₁)) = r (obs (stp s a₂))

/-- The admissible image of `s`: states an admissible action can produce. -/
def AdmImage {σ α : Type} (stp : σ → α → σ) (adm : α → Prop) (s : σ) : Set σ :=
  {y | ∃ a, adm a ∧ stp s a = y}

/-- **Characterization.** Noninterference is exactly constancy of `r ∘ obs`
    on each admissible image. Generalizes
    `DARM.A4.noninterferingAll_iff_constant_on_image`. -/
theorem noninterfering_iff_constant_on_admImage {σ α ω ρ : Type}
    (stp : σ → α → σ) (adm : α → Prop) (obs : σ → ω) (r : ω → ρ) :
    Noninterfering stp adm obs r ↔
      ∀ s, ∀ x ∈ AdmImage stp adm s, ∀ y ∈ AdmImage stp adm s,
        r (obs x) = r (obs y) := by
  constructor
  · intro h s x hx y hy
    obtain ⟨a₁, h₁, rfl⟩ := hx
    obtain ⟨a₂, h₂, rfl⟩ := hy
    exact h s a₁ a₂ h₁ h₂
  · intro h s a₁ a₂ h₁ h₂
    exact h s _ ⟨a₁, h₁, rfl⟩ _ ⟨a₂, h₂, rfl⟩

/-! ## 2. `Influence.lean` is an instance

  Its `NoninterferingAll` is the special case where every action is
  admissible. Stated as an `iff` so the existing negative results transfer. -/

theorem influence_eq_instance :
    DARM.A4.NoninterferingAll DARM.A4.obs DARM.A4.ratify ↔
      Noninterfering DARM.A4.worldStep (fun _ => True)
        DARM.A4.obs DARM.A4.ratify := by
  constructor
  · intro h s a₁ a₂ _ _
    exact h s a₁ a₂
  · intro h s a₁ a₂
    exact h s a₁ a₂ trivial trivial

/-! ## 3. `Basic.lean` is also an instance — and it interferes

  The witness needs no world model. `autonomousPropose` shrinks `policy` when
  the proposal is a subset, so from `policy = {0}` the two agent events
  `autonomousPropose ∅` and `autonomousPropose {0}` land in states an observer
  of `policy` can distinguish. -/

/-- Observation: does the monitor currently permit nothing? -/
def obsPolicyEmpty (s : State Unit (Fin 1)) : Bool := decide (s.policy = ∅)

/-- The concrete monitor used below: one action, one capability, all tokens
    valid. Capability gating is vacuous here (`CapId = Unit`), which is
    deliberate — the interference must not be attributable to capabilities. -/
abbrev stepW : State Unit (Fin 1) → Event Unit (Fin 1) Unit → State Unit (Fin 1) :=
  step (fun _ : Fin 1 => ()) (∅ : Finset Unit) (fun _ : Unit => True)

/-- Agent events of the concrete monitor. -/
abbrev admAgent (e : Event Unit (Fin 1) Unit) : Prop := actor e = Actor.agent

/-- The witness state: one action permitted, no capabilities held. -/
def sW : State Unit (Fin 1) :=
  { cap := ∅, policy := {0}, opState := OpState.active, lastExecuted := none }

/-- **A4 fails on `Basic`'s machine.** Two agent events produce states an
    observer of `policy` distinguishes, so the ratifier's verdict is not
    invariant across what the agent can cause.

    This is `DARM.A4.not_noninterfering_all` restated over the reference
    monitor itself rather than over a separate three-element world model. -/
theorem not_noninterfering_basic :
    ¬ Noninterfering stepW admAgent obsPolicyEmpty (id : Bool → Bool) := by
  intro h
  have hne := h sW (Event.autonomousPropose ∅) (Event.autonomousPropose {0})
    rfl rfl
  simp [stepW, sW, obsPolicyEmpty, step] at hne

/-! ## 4. Cell C4 — capability confinement is independent of A4

  Both properties now live in one model, so the cell is statable. -/

/-- **Independence cell.** Capability confinement holds at the witness state
    — no capabilities are held and the TCB bound is empty — while
    noninterference fails for the same monitor.

    So bounding capability does not bound influence. The two are independent
    dimensions of the monitor's behaviour, and A2 buys nothing towards A4.

    This is the `Basic`-side analogue of
    `DARM.A4.core_integrity_does_not_imply_noninterference`, and unlike that
    theorem it is stated about the reference monitor rather than a separate
    model. The stronger form — confinement holding along every trace — follows
    from `step_preserves_capInvariant` and is not restated here. -/
theorem cap_confinement_independent_of_noninterference :
    capInvariant (∅ : Finset Unit) sW ∧
      ¬ Noninterfering stepW admAgent obsPolicyEmpty (id : Bool → Bool) := by
  refine ⟨?_, not_noninterfering_basic⟩
  unfold capInvariant sW
  exact Finset.Subset.refl _

/-! ## Registered status

  DONE:  Noninterference generalized over the transition function. Both
         discrete models shown to be instances. A4 shown to fail on `Basic`'s
         machine directly. C4 proved: capability confinement and
         noninterference are independent.

  OPEN:  `Influence.lean`'s `WorldState`/`worldStep`/`Sys` are now redundant
         for the A4 claim — kept as a minimal example. Its docstring still
         says it addresses A4 in `Basic.lean`; that should be amended to point
         here.

  NOT ATTEMPTED: the simulation bridge `interp : State → Sys`. See the header
         for why it is expected to be degenerate.
-/

end Interference
end DARM

#print axioms DARM.Interference.noninterfering_iff_constant_on_admImage
#print axioms DARM.Interference.influence_eq_instance
#print axioms DARM.Interference.not_noninterfering_basic
#print axioms DARM.Interference.cap_confinement_independent_of_noninterference
