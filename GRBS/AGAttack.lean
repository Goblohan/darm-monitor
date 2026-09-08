/-
  AG-ATTACK-1 (R3b): is the GRBS transfer judgment reducible to ordinary
  assume-guarantee reasoning?

  DISCIPLINE (agreed before writing):
  * AGSatisfies and GRBS are SEMANTICALLY INDEPENDENT. The AG contract sees only
    the system's trace semantics and the fixed guarantee. GRBS also sees coverage.
  * cov is NOT a function of traces: separate System fields, no definitional link.
  * TraceEq -> CovEq is a THEOREM TO BE TESTED, never an axiom.
  * DepEq for the witness is PROVED of the particular systems, not assumed.

  DECISIVE EXPERIMENT (G fixed; no guarantee-indexing escape hatch): construct
  S1,S2 with TraceEq, DepEq, but different coverage flipping GRBS. Trace identity
  then forces AGSatisfies A g S1 <-> AGSatisfies A g S2 for every A.
  Verdict is whatever the proof yields: separation if the witness builds,
  reduction if TraceEq -> CovEq turns out forced.
-/

namespace GRBS
namespace AGAttack

/-- A guarantee is a predicate on traces (its safe set). -/
abbrev Guarantee (Trace : Type) := Trace → Prop

/-- System: two INDEPENDENT fields. `traces` is the transition/trace semantics;
    `cov` is the coverage topology. No field relates them; any link is a theorem. -/
structure System (Environment Trace Dependency : Type) where
  traces : Environment → Trace → Prop
  cov : Dependency → Prop

/-- GRBS: every dependency of `g` in `s` is covered. References `dep` and `s.cov`. -/
def GRBS {Environment Trace Dependency : Type}
    (dep : Guarantee Trace → System Environment Trace Dependency → Dependency → Prop)
    (g : Guarantee Trace) (s : System Environment Trace Dependency) : Prop :=
  ∀ d : Dependency, dep g s d → s.cov d

/-- AG assumption: a predicate on the ENVIRONMENT only (AG-0). Behaviorally
    grounded; sees environments, not coverage, not dep. -/
abbrev AGAssumption (Environment : Type) := Environment → Prop

/-- AG satisfaction (ordinary, untuned): under every environment admitted by `A`,
    every trace of `s` satisfies `g`. Sees `s.traces` and `g`; never `s.cov`. -/
def AGSatisfies {Environment Trace Dependency : Type}
    (A : AGAssumption Environment) (g : Guarantee Trace)
    (s : System Environment Trace Dependency) : Prop :=
  ∀ e : Environment, A e → ∀ t : Trace, s.traces e t → g t

/-- Behavioral (trace) equivalence: identical executions under every environment.
    All the AG side can observe. -/
def TraceEq {Environment Trace Dependency : Type}
    (s1 s2 : System Environment Trace Dependency) : Prop :=
  ∀ (e : Environment) (t : Trace), s1.traces e t ↔ s2.traces e t

/-- Coverage equivalence: identical coverage topology. -/
def CovEq {Environment Trace Dependency : Type}
    (s1 s2 : System Environment Trace Dependency) : Prop :=
  ∀ d : Dependency, s1.cov d ↔ s2.cov d

/-- **Lemma 1.** AG is blind to any difference invisible in traces. Unconditional,
    for every A and g; does NOT reference coverage. The AG side of the separation. -/
theorem agSatisfies_congr_of_traceEq {Environment Trace Dependency : Type}
    (s1 s2 : System Environment Trace Dependency)
    (h : TraceEq s1 s2)
    (A : AGAssumption Environment) (g : Guarantee Trace) :
    AGSatisfies A g s1 ↔ AGSatisfies A g s2 := by
  constructor
  · intro hsat e hA t ht
    exact hsat e hA t ((h e t).mpr ht)
  · intro hsat e hA t ht
    exact hsat e hA t ((h e t).mp ht)

/-- A separation witness IS the decisive experiment: two systems trace-equal,
    dependency-equal, coverage-different in a way that flips GRBS. -/
structure SeparationWitness {Environment Trace Dependency : Type}
    (dep : Guarantee Trace → System Environment Trace Dependency → Dependency → Prop)
    (g : Guarantee Trace) where
  s1 : System Environment Trace Dependency
  s2 : System Environment Trace Dependency
  htrace : TraceEq s1 s2
  hdep   : ∀ d, dep g s1 d ↔ dep g s2 d
  hGRBS1 : GRBS dep g s1
  hGRBS2 : ¬ GRBS dep g s2

/-- **Separation theorem.** If a separation witness exists, GRBS is not equivalent
    to any behaviorally-grounded AG contract: a fixed `g` and two systems every AG
    contract treats identically (Lemma 1) while GRBS distinguishes them. -/
theorem grbs_not_reducible_to_AG {Environment Trace Dependency : Type}
    {dep : Guarantee Trace → System Environment Trace Dependency → Dependency → Prop}
    {g : Guarantee Trace} (w : SeparationWitness dep g)
    (A : AGAssumption Environment) :
    (AGSatisfies A g w.s1 ↔ AGSatisfies A g w.s2)
    ∧ (GRBS dep g w.s1 ∧ ¬ GRBS dep g w.s2) := by
  refine ⟨?_, ?_, ?_⟩
  · exact agSatisfies_congr_of_traceEq w.s1 w.s2 w.htrace A g
  · exact w.hGRBS1
  · exact w.hGRBS2

/-! ## Concrete witness: separation is honestly constructible.

    Two systems LITERALLY trace-identical (same `traces` function), `dep` provably
    equal (it reads the guarantee and traces, never `cov`), yet coverage-different.
    Succeeds precisely because `cov` was kept independent of `traces` and `dep`. -/

inductive E where | e0
inductive T where | t0
inductive D where | d0
deriving DecidableEq

/-- Fixed guarantee; content irrelevant to the separation. -/
def g : Guarantee T := fun _ => True

/-- Structural dependency map reading ONLY the guarantee and trace behavior, never
    `cov`: `d0` is a dependency when the system produces `t0` under `e0`. -/
def depW : Guarantee T → System E T D → D → Prop :=
  fun _ s _ => s.traces E.e0 T.t0

def sharedTraces : E → T → Prop := fun _ _ => True

/-- System 1: shared traces, `d0` covered. -/
def S1 : System E T D where
  traces := sharedTraces
  cov := fun _ => True

/-- System 2: SAME traces, `d0` NOT covered. -/
def S2 : System E T D where
  traces := sharedTraces
  cov := fun _ => False

theorem traceEq_S1_S2 : TraceEq (Dependency := D) S1 S2 := by
  intro e t; rfl

theorem depEq_S1_S2 : ∀ d, depW g S1 d ↔ depW g S2 d := by
  intro d; rfl

theorem dep_holds_S2 : depW g S2 D.d0 := trivial

theorem GRBS_S1 : GRBS depW g S1 := by
  intro d _hd; trivial

theorem not_GRBS_S2 : ¬ GRBS depW g S2 := by
  intro h
  exact h D.d0 dep_holds_S2

/-- The fully-proved separation witness. -/
def witness : SeparationWitness depW g where
  s1 := S1
  s2 := S2
  htrace := traceEq_S1_S2
  hdep := depEq_S1_S2
  hGRBS1 := GRBS_S1
  hGRBS2 := not_GRBS_S2

/-- **AG-ATTACK-1 VERDICT (AG-0): SEPARATION.** For fixed `g` and every
    behaviorally-grounded AG assumption `A`, the two systems get the identical AG
    verdict while GRBS distinguishes them. Coverage is behaviorally invisible in
    this model: trace-equality does NOT force coverage-equality. Diagnostic only;
    strengthened adversarial version (option 2) is the decisive experiment. -/
theorem separation (A : AGAssumption E) :
    (AGSatisfies A g S1 ↔ AGSatisfies A g S2) ∧ (GRBS depW g S1 ∧ ¬ GRBS depW g S2) :=
  grbs_not_reducible_to_AG witness A

end AGAttack
end GRBS
