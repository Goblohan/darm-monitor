import DarmMonitor.StratumComposition

/-
  Ratification — the one transition that can break cross-stratum coherence,
  and what happens if you try to guard it.

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`. Do not describe as verified before both.

  CONTEXT. `StratumComposition.coherence_preserved_under_agent_event` shows
  coherence survives every agent event paired with a Z-safe update.
  `Basic.step` has exactly one branch not covered: `authenticatedRatification`,
  which assigns `policy := newPolicy` outright. This module isolates it.

  THE TRILEMMA (recorded, not resolved):
    (a) Unguarded ratification breaks coherence.        -- ratification_breaks_coherence
    (b) Guarding by `newPolicy ⊆ active δ w` forces the reference monitor to
        evaluate real comparisons, destroying the compute isolation that
        motivated the set-theoretic bridge in the first place.
    (c) Certificate-checking relocates (b) rather than removing it.

  THE INFLUENCE-TRANSFER RESULT. Under (b), the ratifiable policies are exactly
  `(active δ w).powerset`. But `active` is downstream of `reweight η loss w`,
  and `loss` is the agent-synthesized signal. So guarding hands the agent
  control over what the human is permitted to grant. Worse, the direction is
  asymmetric: `transportSupp` forbids the agent from shrinking the active set
  while remaining Z-safe, but permits growth (resurrection). A fully Z-safe
  agent can therefore only ever EXPAND the ratifiable set.
  See `safe_update_expands_ratifiable_set`.

  This is a negative result about the guard, not an argument against guarding.
  It says the guard relocates influence rather than eliminating it, and that
  the relocation favours the agent.
-/

namespace DARM.Ratification

open DARM.Boundary DARM.Composition

/-! ## 1. Unguarded ratification breaks coherence

  Concrete witness. One coordinate, weight 0, margin 1, so the active set is
  empty; a ratifier with a valid token grants `{0}` anyway. -/

theorem ratification_breaks_coherence :
    ∃ (s : State Unit (Fin 1)) (δ : ℝ) (w : Fin 1 → ℝ)
      (t : Unit) (p : Finset (Fin 1)),
      IsCoherent s δ w ∧
      ¬ IsCoherent
          (step (∅ : Finset Unit) (fun _ : Unit => True) s
            (Event.authenticatedRatification t p)) δ w := by
  refine ⟨{ cap := ∅, policy := ∅, opState := OpState.active, lastExecuted := none },
          1, (fun _ => 0), (), {0}, ?_, ?_⟩
  · exact Finset.empty_subset _
  · intro h
    have hmem : (0 : Fin 1) ∈ active (1 : ℝ) (fun _ : Fin 1 => (0 : ℝ)) := by
      apply h
      simp [step]
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    linarith

/-! ## 2. The guarded rule

  Stated as a side-condition rather than a change to `Basic.step`, so that
  `Basic.lean` stays computable and untouched. -/

/-- The ratifier's proposed policy is backed by the weight vector. -/
def GuardedRatification (δ : ℝ) {n : ℕ} (w : Fin n → ℝ) (p : Finset (Fin n)) : Prop :=
  p ⊆ active δ w

/-- Under the guard, ratification preserves coherence. Note what this proves:
    the guard is *sufficient*, and the whole risk of the ratification branch
    reduces to this single predicate holding at each ratification event. -/
theorem guarded_ratification_preserves_coherence
    {n : ℕ} {CapId Token : Type} [DecidableEq CapId] [DecidableEq Token]
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop) [DecidablePred validToken]
    (s : State CapId (Fin n)) (t : Token) (p : Finset (Fin n))
    (δ : ℝ) (w : Fin n → ℝ)
    (hcoh : IsCoherent s δ w)
    (hguard : GuardedRatification δ w p) :
    IsCoherent
      (step allowedCapLimit validToken s (Event.authenticatedRatification t p)) δ w := by
  unfold IsCoherent at hcoh ⊢
  simp only [step]
  split
  · exact hguard
  · exact hcoh

/-! ## 3. Influence transfer: the guard favours the agent

  Under the guarded rule the ratifiable policies are exactly the powerset of
  the active set. A Z-safe update can only grow that set. -/

/-- Policies a guarded ratifier may legitimately grant. -/
noncomputable def Ratifiable (δ : ℝ) {n : ℕ} (w : Fin n → ℝ) : Finset (Finset (Fin n)) :=
  (active δ w).powerset

/-- **Negative result.** A Z-safe continuous update — one fully satisfying the
    monitor's certificate — monotonically expands what a guarded ratifier is
    permitted to grant. Safety constrains the agent from revoking authority;
    it does not constrain the agent from enabling it. -/
theorem safe_update_expands_ratifiable_set
    {n : ℕ} (δ η : ℝ) (loss w : Fin n → ℝ)
    (hZ : 0 < Z (reweight η loss w))
    (hsafe : is_safe_signal_Z δ η loss w) :
    Ratifiable δ w
      ⊆ Ratifiable δ (normalize (reweight η loss w) (Z (reweight η loss w))) := by
  unfold Ratifiable
  exact Finset.powerset_mono.mpr (transportSupp δ η loss w hZ hsafe)

/-! ## Registered open problems

  R1. QUANTITATIVE REACH. `safe_update_expands_ratifiable_set` shows the
      ratifiable set can only grow. It does NOT show how far. The open
      question is whether an agent choosing `loss` can drive `active δ w` to
      an arbitrary superset of the current active set while keeping
      `is_safe_signal_Z`. Since `reweight η loss w i = w i * exp (-η * loss i)`
      and `exp` is surjective onto the positives, the answer is plausibly yes
      whenever `w i > 0` — but this requires real analysis not attempted here,
      and the Z-bound may obstruct it. NOT PROVEN EITHER WAY.

  R2. THE TRILEMMA HAS NO PROVEN RESOLUTION. Options (a), (b), (c) in the
      header are recorded as a design space, not a theorem. Nothing here shows
      the space is exhaustive.

  R3. RELATION TO A4. `Influence.lean` proves the agent can influence the
      ratifier through the observation channel (`not_noninterfering_all`).
      This module shows a guard would give it a second channel. The two have
      NOT been formally composed — `Influence.lean` and `Basic.lean` still
      share no types. That bridge remains unbuilt.
-/

end DARM.Ratification

#print axioms DARM.Ratification.ratification_breaks_coherence
#print axioms DARM.Ratification.guarded_ratification_preserves_coherence
#print axioms DARM.Ratification.safe_update_expands_ratifiable_set
