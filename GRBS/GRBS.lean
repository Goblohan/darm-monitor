/-
  GRBS — Guarantee-Relative Boundary-coverage Sufficiency (R1 kernel)

  A machine-checked kernel for the DARM assurance-transfer calculus.

  Central result: the *necessity* theorem `transfer_fails_of_uncovered` —
  if a guarantee's dependency set is not covered by the boundary, the guarantee
  does not transfer. Its content lies entirely in two named bridging
  hypotheses, Exploitability and Dependence. The theorem is a constructive
  consequence of them; the concrete instance (`Concrete` section) proves both
  hypotheses are satisfiable, so the theorem is not vacuous.

  DESIGN DISCIPLINE (what keeps `¬GRBS → ¬Transfer` from degenerating to A→A):
    * `Transfer` is semantic (∀ admissible environments, ∀ their traces) and
      NEVER mentions `cov`.
    * `dep` is structural — a map from (guarantee, system) — and NEVER mentions
      `Safe` or trace satisfaction.
    * `GRBS` is the ONLY predicate that references both `dep` and `cov`.
  Violating any separation collapses the theorem to a tautology.

  THE TWO SEAMS (where the theorem's real content — and its attack surface —
  lives):
    * Exploitability: an uncovered dependency admits an admissible environment
      whose composite execution perturbs that dependency.
    * Dependence: perturbing a *structural* dependency of `g` permits a trace
      that violates `g`. This is the seam that, in a stronger development, one
      would PROVE from the structural definition of `dep` rather than assume;
      leaving it explicit is deliberate.
-/

namespace GRBS

/-- Abstract carriers. Opaque type parameters so the kernel commits to no
    particular representation. -/
structure Frame where
  Trace : Type
  Guarantee : Type
  System : Type
  Boundary : Type
  Locus : Type
  Dependency : Type
  Environment : Type
  /-- Safe-trace denotation of a guarantee. Used ONLY by `Transfer`. -/
  Safe : Guarantee → Trace → Prop
  /-- Structural dependency map. Takes ONLY `g` and `s` — never `Safe`. -/
  dep : Guarantee → System → Dependency → Prop
  /-- Boundary coverage: dependencies mediated by `b` via `l` in `s`. -/
  cov : Boundary → Locus → System → Dependency → Prop
  /-- Admissible environments for a boundary. -/
  Envs : Boundary → Environment → Prop
  /-- Composite execution traces of `s` against `e` across `b`. -/
  Traces : System → Environment → Boundary → Trace → Prop
  /-- **Perturbation.** `t` perturbs dependency `d` — the trace `t` exercises,
      drives, or exploits the channel/authority/state component `d`. A
      structural/observational relation on traces, independent of `Safe`. It is
      the vocabulary shared by the two seams: Exploitability produces a
      perturbing trace, Dependence consumes one. -/
  Perturbs : Trace → Dependency → Prop

variable (F : Frame)

/-- **Guarantee-Relative Boundary-coverage Sufficiency.**
    Every dependency of `g` in `s` is covered by `b` via `l`. The ONLY
    predicate mentioning both `dep` and `cov`. -/
def GRBS (g : F.Guarantee) (s : F.System) (b : F.Boundary) (l : F.Locus) : Prop :=
  ∀ d : F.Dependency, F.dep g s d → F.cov b l s d

/-- **Transfer (semantic).**
    Every admissible environment across `b` yields only safe composite traces.
    Mentions `Safe`, `Envs`, `Traces`; NEVER `cov`. -/
def Transfer (g : F.Guarantee) (s : F.System) (b : F.Boundary) : Prop :=
  ∀ e : F.Environment, F.Envs b e →
    ∀ t : F.Trace, F.Traces s e b t → F.Safe g t

/-- **Exploitability.**
    Every uncovered dependency of `g` in `s` admits an admissible environment
    whose composite execution produces a trace that perturbs that dependency.
    Depends on `dep`, `cov`, `Envs`, `Traces`, `Perturbs` — NOT on `Safe`. -/
def Exploitability
    (g : F.Guarantee) (s : F.System) (b : F.Boundary) (l : F.Locus) : Prop :=
  ∀ d : F.Dependency,
    F.dep g s d → ¬ F.cov b l s d →
      ∃ e : F.Environment, F.Envs b e ∧
        ∃ t : F.Trace, F.Traces s e b t ∧ F.Perturbs t d

/-- **Dependence (coverage-relative).**
    If `d` is a structural dependency of `g` in `s` that is *uncovered* by the
    boundary, and `t` perturbs `d`, then `t` violates `g`.

    The `¬ cov` premise scopes this to uncovered dependencies only: coverage
    neutralizes a dependency's perturbation, so `Dependence` says nothing about
    covered ones. This formalizes GUARANTEE-RELATIVE VULNERABILITY — failure is
    driven strictly by `dep g s \ cov b l s`.

    Non-circularity is preserved: `Transfer` never mentions `cov`; here `cov`
    appears only as a scope-guard on `Dependence`'s own premise, supplied in the
    necessity proof by the uncovered dependency extracted from `¬ GRBS`. -/
def Dependence
    (g : F.Guarantee) (s : F.System) (b : F.Boundary) (l : F.Locus) : Prop :=
  ∀ (t : F.Trace) (d : F.Dependency),
    F.dep g s d → ¬ F.cov b l s d → F.Perturbs t d → ¬ F.Safe g t

/-- **Necessity of coverage.**
    Given Exploitability and Dependence, if some dependency of `g` in `s` is
    uncovered (¬GRBS), then `g` does not transfer.

    Constructive proof: from ¬GRBS extract an uncovered `d`; Exploitability
    yields an admissible environment `e` and a composite trace `t` perturbing
    `d`; Dependence turns "perturbs `d`" into "¬ Safe g t"; that trace refutes
    Transfer. -/
theorem transfer_fails_of_uncovered
    (g : F.Guarantee) (s : F.System) (b : F.Boundary) (l : F.Locus)
    (hExploit : Exploitability F g s b l)
    (hDep : Dependence F g s b l)
    (hUncovered : ¬ GRBS F g s b l) :
    ¬ Transfer F g s b := by
  rw [GRBS] at hUncovered
  have ⟨d, hd⟩ := Classical.not_forall.mp hUncovered
  have hdep : F.dep g s d := Classical.byContradiction fun hnd => hd (fun hdd => absurd hdd hnd)
  have hncov : ¬ F.cov b l s d := fun hc => hd (fun _ => hc)
  obtain ⟨e, hEnv, t, hTr, hPert⟩ := hExploit d hdep hncov
  intro hTransfer
  exact hDep t d hdep hncov hPert (hTransfer e hEnv t hTr)

/-- **Contrapositive.** If `g` transfers (and the two seams hold), every
    dependency is covered. -/
theorem covered_of_transfer
    (g : F.Guarantee) (s : F.System) (b : F.Boundary) (l : F.Locus)
    (hExploit : Exploitability F g s b l)
    (hDep : Dependence F g s b l)
    (hTransfer : Transfer F g s b) :
    GRBS F g s b l := by
  apply Classical.byContradiction
  intro hUncovered
  exact transfer_fails_of_uncovered F g s b l hExploit hDep hUncovered hTransfer

end GRBS

namespace GRBS
namespace Concrete

/-!
  ## Non-vacuity: a concrete 2-authority instance

  Two authorities `authA` (mediated) and `authB` (unmediated). A single
  guarantee that structurally depends on both. A boundary covering only
  `authA`. An environment that drives the unmediated authority `authB`,
  producing an unsafe trace.

  We instantiate `Frame`, then DISCHARGE both seams (`Exploitability`,
  `Dependence`) and derive `¬ Transfer` from the necessity theorem — proving
  the abstract theorem ranges over a nonempty set of models.

  The separations are respected concretely:
    * `depC` looks only at the guarantee/authority pairing.
    * `covC` looks only at which authority the boundary mediates.
    * `safeC` looks only at which authority a trace exercised.
  Their alignment is a fact ABOUT this model, consumed by the theorem, not an
  assumption baked into the abstract definitions.
-/

/-- The two authorities. `authA` is mediated by the boundary; `authB` is not. -/
inductive Auth where
  | authA
  | authB
deriving DecidableEq

/-- A trace records which authority it exercised (or none — the clean trace).
    A trace exercising `authB` is the unmediated bypass. -/
inductive Tr where
  | clean
  | usedA
  | usedB
deriving DecidableEq

/-- One guarantee, one system, one boundary, one locus, one relevant
    environment. We use `Unit`-like singletons where only one inhabitant
    matters, and a two-element environment type to have a genuine "adversary". -/
inductive Env where
  | benign      -- produces only the clean trace
  | bypassB     -- drives the unmediated authority authB
deriving DecidableEq

/-- Safe traces of the (single) guarantee: exercising the unmediated authority
    `authB` is the violation; everything else is safe. Depends ONLY on the
    trace. -/
def safeC : Unit → Tr → Prop
  | _, Tr.clean => True
  | _, Tr.usedA => True
  | _, Tr.usedB => False

/-- Structural dependency: the guarantee depends on BOTH authorities. Depends
    ONLY on guarantee/authority — never on traces or `safeC`. -/
def depC : Unit → Unit → Auth → Prop
  | _, _, _ => True

/-- Coverage: the boundary (via its single locus) mediates `authA` only.
    Depends ONLY on which authority — never on `depC` or `safeC`. -/
def covC : Unit → Unit → Unit → Auth → Prop
  | _, _, _, Auth.authA => True
  | _, _, _, Auth.authB => False

/-- Admissible environments: both are admissible across the boundary. (The
    bypass environment is admissible precisely because `authB` is NOT mediated
    — the boundary does not exclude it.) -/
def envsC : Unit → Env → Prop
  | _, _ => True

/-- Composite execution. `benign` yields the clean trace; `bypassB` yields the
    `authB`-exercising trace. -/
def tracesC : Unit → Env → Unit → Tr → Prop
  | _, Env.benign,  _, Tr.clean => True
  | _, Env.benign,  _, _        => False
  | _, Env.bypassB, _, Tr.usedB => True
  | _, Env.bypassB, _, _        => False

/-- Perturbation: a trace perturbs an authority iff it exercised that authority.
    Structural/observational; independent of `safeC`. -/
def perturbsC : Tr → Auth → Prop
  | Tr.usedA, Auth.authA => True
  | Tr.usedB, Auth.authB => True
  | _,        _          => False

/-- The concrete frame. -/
def F : Frame where
  Trace := Tr
  Guarantee := Unit
  System := Unit
  Boundary := Unit
  Locus := Unit
  Dependency := Auth
  Environment := Env
  Safe := safeC
  dep := depC
  cov := covC
  Envs := envsC
  Traces := tracesC
  Perturbs := perturbsC

/-- GRBS FAILS in this model: `authB` is a dependency but uncovered. -/
theorem grbs_fails : ¬ GRBS F () () () () := by
  intro h
  -- h : ∀ d, dep g s d → cov b l s d ; instantiate at authB
  have hcov : F.cov () () () Auth.authB := h Auth.authB trivial
  -- F.cov () () () authB reduces to `covC () () () authB = False`
  have hncov : ¬ F.cov () () () Auth.authB := by intro hc; simp only [F, covC] at hc
  exact hncov hcov

/-- Exploitability holds: the uncovered authority `authB` has an admissible
    environment (`bypassB`) producing a trace (`usedB`) that perturbs it. -/
theorem exploitability_holds : Exploitability F () () () () := by
  intro d _hdep hncov
  -- the only uncovered dependency is authB
  cases d with
  | authA =>
      -- authA is covered, so hncov : ¬ True is impossible
      exact absurd (by simp only [F, covC] : F.cov () () () Auth.authA) hncov
  | authB =>
      exact ⟨Env.bypassB, trivial, Tr.usedB, trivial, trivial⟩

/-- Dependence (coverage-relative) holds. The `¬ cov` premise restricts to
    uncovered dependencies. In this model the only uncovered dependency is
    `authB`; a trace perturbing `authB` must be `usedB`, which is unsafe. The
    covered authority `authA` cannot trigger this obligation, because its
    `¬ cov` premise is `¬ True`. -/
theorem dependence_holds : Dependence F () () () () := by
  intro t d _hdep hncov hpert
  -- goal: ¬ safeC () t
  cases d with
  | authA =>
      -- authA is covered: covC .. authA = True, so hncov : ¬ True is false.
      exact absurd (by simp only [F, covC] : F.cov () () () Auth.authA) hncov
  | authB =>
      -- d = authB. Only `usedB` perturbs authB, and safeC () usedB = False.
      cases t with
      | clean =>
          -- perturbsC clean authB = False
          simp only [F, perturbsC] at hpert
      | usedA =>
          -- perturbsC usedA authB = False
          simp only [F, perturbsC] at hpert
      | usedB =>
          -- goal ¬ F.Safe () usedB ; F.Safe () usedB reduces to False
          intro hs
          simp only [F, safeC] at hs

/-- **Non-vacuity capstone.**
    The concrete model satisfies both seams (`exploitability_holds`,
    `dependence_holds`) and fails GRBS (`grbs_fails`). Applying the abstract
    necessity theorem yields a concrete failure of transfer: the guarantee does
    NOT transfer in this model, witnessed by the `authB` bypass.

    This proves `transfer_fails_of_uncovered` is not vacuously true: its
    hypotheses are jointly inhabited, and its conclusion has real force in at
    least one model. -/
theorem transfer_fails_concretely : ¬ Transfer F () () () := by
  exact transfer_fails_of_uncovered F () () () ()
    exploitability_holds dependence_holds grbs_fails

/-- The dual: in this model, `Transfer` would force coverage — but coverage
    fails, so this is another route to the same negative conclusion. Recorded to
    exercise `covered_of_transfer` on the concrete frame. -/
theorem no_transfer_since_uncovered : ¬ Transfer F () () () := by
  intro hTransfer
  exact grbs_fails
    (covered_of_transfer F () () () () exploitability_holds dependence_holds hTransfer)

end Concrete
end GRBS

#print axioms GRBS.transfer_fails_of_uncovered
#print axioms GRBS.covered_of_transfer
#print axioms GRBS.Concrete.transfer_fails_concretely
