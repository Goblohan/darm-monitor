import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic

/-
  A4 — Direct Authority Separation vs. Ratification Influence.

  STATUS: [SPEC] until `lake build` exits 0.

  A4 IS DISCHARGED IN DarmMonitor/Interference.lean. This module shares no
types with Basic.lean; the earlier claim to address A4 was an analogy, not
a reduction. Retained as a minimal example of the observation channel.
Original claim followed: it addresses registered assumption A4 from
DarmMonitor/Basic.lean:
  that nothing in the capability model bounds the agent's causal influence over
  whoever holds the ratification authority.

  It establishes, within a finite model:
    (1) Core integrity is structural, not stipulated: agent events have no
        constructor that writes CoreValue, and no agent-only trace changes it.
    (2) That property does NOT imply noninterference. The agent's actions can
        still determine the ratification verdict through the observation channel.

  SCOPE LIMITS — this module does NOT claim:
    - to model human cognition, deliberation, or persuadability
    - that causal relevance constitutes manipulation
    - anything about real ratifiers outside the modeled observation channel

  Causal chain modeled:
      Action -> WorldState -> Observation -> Ratification
-/

namespace DARM.A4

/-! ## A4.1  Types -/

inductive Action
  | noop
  | actA
  | actB
deriving DecidableEq, Repr

inductive WorldState
  | neutral
  | stateA
  | stateB
deriving DecidableEq, Repr

inductive Observation
  | quiet
  | signalA
  | signalB
deriving DecidableEq, Repr

inductive Ratification
  | reject
  | accept
deriving DecidableEq, Repr

/-- The protected value. Participates in the state; not dead syntax. -/
inductive CoreValue
  | original
  | modified
deriving DecidableEq, Repr

/-- Full system state. `core` is the protected component. -/
structure Sys where
  world : WorldState
  core : CoreValue
deriving DecidableEq, Repr

/-! ## A4.2  Events

  The separation is structural: `AgentEvent` has no constructor carrying a
  `CoreValue`. Core modification is reachable only via `Event.ratifyCore`,
  which is not an agent event. -/

inductive AgentEvent
  | act : Action → AgentEvent
deriving DecidableEq, Repr

inductive Event
  | ofAgent : AgentEvent → Event
  | ratifyCore : CoreValue → Event
deriving DecidableEq, Repr

def isAgent : Event → Bool
  | .ofAgent _ => true
  | .ratifyCore _ => false

/-! ## A4.3  Transition functions -/

def worldStep : WorldState → Action → WorldState
  | s, .noop => s
  | _, .actA => .stateA
  | _, .actB => .stateB

def obs : WorldState → Observation
  | .neutral => .quiet
  | .stateA => .signalA
  | .stateB => .signalB

/-- The ratifier's decision function. Named `ratify`, not `decide`,
    to avoid collision with Lean's `decide`. -/
def ratify : Observation → Ratification
  | .quiet => .reject
  | .signalA => .accept
  | .signalB => .reject

def agentStep (s : Sys) : AgentEvent → Sys
  | .act a => { s with world := worldStep s.world a }

def step (s : Sys) : Event → Sys
  | .ofAgent e => agentStep s e
  | .ratifyCore v => { s with core := v }

/-! ## A4.4  Structural core integrity

  Not `¬ False`. The claim is that no agent-only trace, of any length,
  changes `core` — because `agentStep` has no branch that touches it. -/

theorem agentStep_preserves_core (s : Sys) (e : AgentEvent) :
    (agentStep s e).core = s.core := by
  cases e with
  | act a => rfl

theorem agent_trace_preserves_core (es : List AgentEvent) :
    ∀ s : Sys, (es.foldl agentStep s).core = s.core := by
  induction es with
  | nil => intro s; rfl
  | cons e es ih =>
      intro s
      simp only [List.foldl_cons]
      rw [ih (agentStep s e), agentStep_preserves_core]

/-- Same result stated over the full event type, restricted to agent events. -/
theorem core_unchanged_under_agent_events
    (es : List Event) (hAll : ∀ e ∈ es, isAgent e = true) :
    ∀ s : Sys, (es.foldl step s).core = s.core := by
  induction es with
  | nil => intro s; rfl
  | cons e es ih =>
      intro s
      simp only [List.foldl_cons]
      have hStep : (step s e).core = s.core := by
        cases e with
        | ofAgent ae => exact agentStep_preserves_core s ae
        | ratifyCore v => simp [isAgent] at hAll
      rw [ih (fun e' he' => hAll e' (by simp [he'])) (step s e), hStep]

/-! ## A4.5  Noninterference

  Two versions, differing in quantifier domain. The distinction is not
  cosmetic — see the note below. -/

/-- Strong form: the verdict is invariant across agent actions from **any**
    modeled world state, including states the agent may be unable to reach. -/
def NoninterferingAll
    (obs : WorldState → Observation) (r : Observation → Ratification) : Prop :=
  ∀ s a₁ a₂, r (obs (worldStep s a₁)) = r (obs (worldStep s a₂))

/-- States reachable from `s₀` by some finite sequence of actions. -/
def ReachableFrom (s₀ : WorldState) (s : WorldState) : Prop :=
  ∃ as : List Action, as.foldl worldStep s₀ = s

/-- Deployment-relative form: invariance only from states the agent can
    actually reach from `s₀`. This is the weaker and more useful property. -/
def NoninterferingFrom (s₀ : WorldState)
    (obs : WorldState → Observation) (r : Observation → Ratification) : Prop :=
  ∀ s, ReachableFrom s₀ s → ∀ a₁ a₂,
    r (obs (worldStep s a₁)) = r (obs (worldStep s a₂))

/-! ## A4.6  The counterexample, as an instance of the general predicate -/

theorem not_noninterfering_all : ¬ NoninterferingAll obs ratify := by
  intro h
  have := h .neutral .actA .noop
  simp [obs, ratify, worldStep] at this

/-- The stronger version: it fails even from the initial state, so this is
    not an artifact of quantifying over unreachable states. -/
theorem not_noninterfering_from_neutral :
    ¬ NoninterferingFrom .neutral obs ratify := by
  intro h
  have hReach : ReachableFrom .neutral .neutral := ⟨[], rfl⟩
  have := h .neutral hReach .actA .noop
  simp [obs, ratify, worldStep] at this

/-! ## A4.7  Characterization

  Noninterference is exactly constancy of `r ∘ obs` on the image of
  `worldStep s`. This is the design constraint: the ratifier's verdict must
  not vary across anything the agent can cause. -/

theorem noninterferingAll_iff_constant_on_image
    (obs : WorldState → Observation) (r : Observation → Ratification) :
    NoninterferingAll obs r ↔
      ∀ s, ∀ x ∈ Set.range (worldStep s), ∀ y ∈ Set.range (worldStep s),
        r (obs x) = r (obs y) := by
  constructor
  · intro h s x hx y hy
    obtain ⟨a₁, rfl⟩ := hx
    obtain ⟨a₂, rfl⟩ := hy
    exact h s a₁ a₂
  · intro h s a₁ a₂
    exact h s _ ⟨a₁, rfl⟩ _ ⟨a₂, rfl⟩

/-- Reachability-relative characterization. -/
theorem noninterferingFrom_iff_constant_on_reachable_image (s₀ : WorldState)
    (obs : WorldState → Observation) (r : Observation → Ratification) :
    NoninterferingFrom s₀ obs r ↔
      ∀ s, ReachableFrom s₀ s →
        ∀ x ∈ Set.range (worldStep s), ∀ y ∈ Set.range (worldStep s),
          r (obs x) = r (obs y) := by
  constructor
  · intro h s hs x hx y hy
    obtain ⟨a₁, rfl⟩ := hx
    obtain ⟨a₂, rfl⟩ := hy
    exact h s hs a₁ a₂
  · intro h s hs a₁ a₂
    exact h s hs _ ⟨a₁, rfl⟩ _ ⟨a₂, rfl⟩

/-! ## A4.8  The A4 result

  Structural core integrity and ratification noninterference are independent.
  The first holds; the second fails. -/

theorem core_integrity_does_not_imply_noninterference :
    (∀ (es : List AgentEvent) (s : Sys), (es.foldl agentStep s).core = s.core)
    ∧ ¬ NoninterferingAll obs ratify := by
  constructor
  · intro es s; exact agent_trace_preserves_core es s
  · exact not_noninterfering_all

/-! ## Registered open problems (unchanged by this module)

  O1. Whether any ratification protocol with a non-degenerate verdict can be
      noninterfering. The characterization above suggests a tension: a verdict
      that never varies with agent-caused world states may be uninformative.
  O2. Quantitative influence bounds. This module is qualitative — it shows
      influence exists, not how much.
  O3. Everything about real human ratifiers. Out of scope by construction. -/

end DARM.A4

#print axioms DARM.A4.agentStep_preserves_core
#print axioms DARM.A4.agent_trace_preserves_core
#print axioms DARM.A4.core_unchanged_under_agent_events
#print axioms DARM.A4.not_noninterfering_all
#print axioms DARM.A4.not_noninterfering_from_neutral
#print axioms DARM.A4.noninterferingAll_iff_constant_on_image
#print axioms DARM.A4.noninterferingFrom_iff_constant_on_reachable_image
#print axioms DARM.A4.core_integrity_does_not_imply_noninterference
