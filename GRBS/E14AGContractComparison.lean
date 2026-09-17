/-
  E14 — AG CONTRACT COMPARISON

  QUESTION: Is the E13/R20 causal assurance structure genuinely different
  from assume-guarantee reasoning, or can ordinary AG already express it?

  THREE TESTS:
  1. AG satisfaction WITHOUT causal coverage -> safety gap exists
  2. AG satisfaction WITH causal coverage -> causal safety restored
  3. CausalCoverage is invisible to AG's observation

  THREE POSSIBLE OUTCOMES:
  Outcome 1: Ordinary AG expresses everything -> DARM novelty weak
  Outcome 2: AG + explicit causal coverage -> E13/R20 -> DARM is a discipline
  Outcome 3: Enriched AG cannot express the obligation -> genuine primitive

  ADVERSARIAL DISCIPLINE: The model is not rigged. AG is given a fair
  observation model. CausalCoverage is defined independently of DARM.
  The experiment tests what AG can and cannot see.
-/

namespace GRBS.E14AGContractComparison

-- Minimal carriers: two states, safe and compromised.
inductive St where
  | safe
  | compromised
deriving DecidableEq

-- Modeled transitions: what AG reasons about.
-- Only safe -> safe is modeled. The bypass is unmodeled.
def modeledStep : St -> St -> Prop
  | St.safe, St.safe => True
  | _, _ => False

-- Causeable transitions: physical reality.
-- Includes safe -> compromised (the bypass), which is
-- physically possible but absent from the model.
def causeableStep : St -> St -> Prop
  | St.safe, St.safe => True
  | St.safe, St.compromised => True
  | _, _ => False

-- The guarantee.
def G : St -> Prop
  | St.safe => True
  | St.compromised => False

-- AG satisfaction: all MODELED transitions preserve G.
def AGSafe : Prop :=
  forall s s', modeledStep s s' -> G s -> G s'

-- Causal coverage (E13 A1 analog): every causeable transition is modeled.
def CausalCoverage : Prop :=
  forall s s', causeableStep s s' -> modeledStep s s'

-- Causal safety: all CAUSEABLE transitions preserve G.
def CausalSafe : Prop :=
  forall s s', causeableStep s s' -> G s -> G s'

-- ====================================================
-- TEST 1: AG safe but causally unsafe
-- ====================================================

theorem ag_is_satisfied : AGSafe := by
  intro s s' h hg
  cases s with
  | safe => cases s' with
    | safe => trivial
    | compromised => simp [modeledStep] at h
  | compromised => simp [G] at hg

theorem causal_coverage_fails : Not CausalCoverage := by
  intro h
  have := h St.safe St.compromised trivial
  simp [modeledStep] at this

theorem causal_safety_fails : Not CausalSafe := by
  intro h
  have := h St.safe St.compromised trivial trivial
  simp [G] at this

theorem test1_ag_without_causal_coverage :
    AGSafe
    ∧ Not CausalCoverage
    ∧ Not CausalSafe :=
  ⟨ag_is_satisfied, causal_coverage_fails, causal_safety_fails⟩

-- ====================================================
-- TEST 2: AG + CausalCoverage -> CausalSafe
-- ====================================================

theorem ag_plus_coverage_implies_causal_safe
    (hAG : AGSafe) (hCov : CausalCoverage) : CausalSafe := by
  intro s s' hcause hg
  exact hAG s s' (hCov s s' hcause) hg

-- ====================================================
-- TEST 3: CausalCoverage is invisible to AG
-- ====================================================

-- Two systems with identical AG observation (same modeledStep, same G)
-- but different causal structure. AG cannot distinguish them.
-- CausalCoverage gives different answers.

-- System A: causeable = modeled (coverage holds)
def causeableA : St -> St -> Prop := modeledStep

-- System B: causeable includes the bypass (coverage fails)
def causeableB : St -> St -> Prop := causeableStep

theorem same_ag_view_different_coverage :
    -- Same AG observation
    (forall s s', modeledStep s s' ↔ modeledStep s s')
    -- System A has coverage
    ∧ (forall s s', causeableA s s' -> modeledStep s s')
    -- System B does NOT have coverage
    ∧ Not (forall s s', causeableB s s' -> modeledStep s s') := by
  refine ⟨fun _ _ => Iff.rfl, ?_, ?_⟩
  · intro s s' h; exact h
  · exact causal_coverage_fails

-- ====================================================
-- E14 VERDICT
-- ====================================================

/-
  OUTCOME 2 CONFIRMED.

  AG satisfaction is not sufficient for causal safety (Test 1).
  AG + CausalCoverage is sufficient (Test 2).
  CausalCoverage is not visible within AG's observation (Test 3).

  Therefore: the safety CONCLUSION is AG-recoverable (R3e established this).
  The causal COVERAGE CONDITION is not. An AG framework that needs causal
  safety must import the distinction between "modeled transitions" and
  "causeable transitions" -- which is the boundary concept.

  DARM's contribution is making CausalCoverage explicit and first-class.
  This is not a new safety logic (R3e). It is a specific assurance
  discipline that names and checks a condition AG leaves implicit.

  Connection to E13: CausalCoverage is A1 (Causeable subset Represented).
  The MissingA1 witness showed A1 is independently necessary for the
  full causal lift. E14 shows it is also independently invisible to AG.
  Those two results together characterize DARM's precise contribution:
  a necessary condition that the standard observation model cannot state.
-/

theorem e14_verdict :
    AGSafe
    ∧ Not CausalSafe
    ∧ (AGSafe -> CausalCoverage -> CausalSafe)
    ∧ Not CausalCoverage :=
  ⟨ag_is_satisfied, causal_safety_fails,
   ag_plus_coverage_implies_causal_safe, causal_coverage_fails⟩

end GRBS.E14AGContractComparison
