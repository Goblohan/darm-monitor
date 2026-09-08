/-
  R3 — Structural model for the GRBS novelty gate.

  Makes concrete what the R1 kernel (`GRBS.lean`) left opaque: `dep`, `Safe`,
  `Perturbs`, `cov`. The goal is to ATTEMPT to prove `structural_exploitability`
  from a genuinely structural `dep`, and let the proof reveal which outcome
  (see R3-SPEC.md) we are in.

  Model:
    Component : finite state variables (the `Dependency` type)
    Val       : Bool  (each component holds a bit)
    State     : Component -> Val
    Step      : writes one component to a value
    Trace     : List Step, run from an initial state
    Guarantee : a predicate on the RESULT state, plus its mentioned components,
                with the discipline that the predicate depends only on mentions.

  DISCIPLINE: `depS` is structural (mentions x writable). `safeS` is semantic
  (the predicate on the resulting state). No definition bridges them; the bridge
  is exactly what `structural_exploitability` must PROVE.
-/

namespace GRBS
namespace Structural

/-- Finite components: three state variables suffices to exhibit the phenomenon
    (a mentioned+writable+uncovered one, plus others). -/
abbrev Component := Fin 3

/-- Values are bits. -/
abbrev Val := Bool

/-- A state assigns a bit to each component. -/
abbrev State := Component → Val

/-- A step writes one component to a given value. -/
structure Step where
  comp : Component
  val  : Val
deriving DecidableEq

/-- Apply a step to a state (functional update on one component). -/
def applyStep (st : State) (stp : Step) : State :=
  fun c => if c = stp.comp then stp.val else st c

/-- Run a trace (list of steps) from an initial state, left to right. -/
def run (init : State) : List Step → State
  | [] => init
  | stp :: rest => run (applyStep init stp) rest

/-- A system: an initial state and the set of components its admissible steps
    may write (`writable`). This is the system's structural write-footprint. -/
structure System where
  init : State
  writable : Component → Prop
  /-- Decidability of the write-footprint, so environments can be built. -/
  writableDec : DecidablePred writable

/-- A guarantee: a predicate on the RESULT state, plus the components it
    mentions, with the discipline that the predicate is determined by the
    mentioned components (`predRespectsMentions`). -/
structure Guarantee where
  pred : State → Prop
  mentions : Component → Prop
  /-- The predicate depends only on mentioned components: two states agreeing on
      all mentioned components are indistinguishable to `pred`. This is what
      makes `mentions` an honest structural over-approximation of `pred`'s
      dependencies. -/
  predRespectsMentions :
    ∀ s1 s2 : State, (∀ c, mentions c → s1 c = s2 c) → (pred s1 ↔ pred s2)

/-- **Structural dependency.** `d` is a dependency of `g` in `s` iff `g` mentions
    `d` AND `s` can write `d`. Purely structural: mentions ∩ writable. Never
    refers to `safeS`. -/
def depS (g : Guarantee) (s : System) (d : Component) : Prop :=
  g.mentions d ∧ s.writable d

end Structural
end GRBS

namespace GRBS
namespace Structural

/-- **Semantic safety.** A trace is safe for `g` iff the state it produces from
    the system's initial state satisfies `g.pred`. Semantic — refers to `pred`
    and `run`, never to `depS`/`mentions`. -/
def safeS (s : System) (g : Guarantee) (t : List Step) : Prop :=
  g.pred (run s.init t)

/-- **Perturbation.** A trace perturbs `d` iff it contains a step writing `d`. -/
def perturbsS (t : List Step) (d : Component) : Prop :=
  ∃ stp ∈ t, stp.comp = d

/-- **The extra hypothesis R3 exposes.**
    `FalsifiableVia g s d` : there is a value `v` such that writing `v` to `d`
    from the initial state makes `g` false. This is STRICTLY MORE than
    `depS g s d` (mentions ∩ writable): a guarantee can mention `d` yet be
    insensitive to it (`predRespectsMentions` allows vacuous mention). So the
    structural dependency alone does NOT entail falsifiability — this is the
    content the proof needs beyond structure.

    Reporting this honestly is R3 Outcome 2: the distinguishing hypothesis is
    "the guarantee is genuinely sensitive to the uncovered dependency", not
    merely "structurally depends on it". -/
def FalsifiableVia (g : Guarantee) (s : System) (d : Component) : Prop :=
  ∃ v : Val, ¬ g.pred (applyStep s.init ⟨d, v⟩)

/-- **Structural exploitability (the R3 target), with the exposed hypothesis.**

    From: `d` is a structural dependency of `g` in `s` (mentions ∩ writable),
    `d` is uncovered, AND `g` is genuinely falsifiable via `d`
    (`FalsifiableVia`) — construct a single-step adversarial trace that writes
    the falsifying value to `d`. That trace perturbs `d` and is unsafe.

    We do NOT quantify over environments/`cov` here (that layer is the R1
    Frame's; this lemma is the structural core the Frame's `Exploitability`
    would be instantiated from). The `¬cov` premise is carried for fidelity to
    the calculus but is not USED in the construction — which is itself a finding
    (see note below). -/
theorem structural_exploitability
    (g : Guarantee) (s : System) (d : Component)
    (_hdep : depS g s d)
    (hfals : FalsifiableVia g s d) :
    ∃ t : List Step, perturbsS t d ∧ ¬ safeS s g t := by
  obtain ⟨v, hv⟩ := hfals
  -- the single-step trace writing v to d
  refine ⟨[⟨d, v⟩], ?_, ?_⟩
  · -- perturbs d: the trace contains a step writing d
    exact ⟨⟨d, v⟩, List.mem_singleton.mpr rfl, rfl⟩
  · -- unsafe: run init [⟨d,v⟩] = applyStep init ⟨d,v⟩, and g.pred of that is false
    show ¬ g.pred (run s.init [⟨d, v⟩])
    -- run init [⟨d,v⟩] reduces to applyStep init ⟨d,v⟩
    simpa [safeS, run] using hv

end Structural
end GRBS

