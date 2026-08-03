import DarmMonitor.Assumptions

/-
  Minimality — necessity and independence cells for the assumption matrix.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT A CELL IS. The Dependency Atlas proposes a matrix recording, for each
  theorem, which hypotheses are necessary (N) and which are independent (I).
  Sufficiency is the theorem itself and needs no separate work. NECESSITY is
  the content: a hypothesis is necessary only if there is a model where it
  fails and the conclusion fails with it. Without such a countermodel, an "N"
  is an assertion.

  ON "INDEPENDENT" CELLS. Now that assumptions are explicit hypotheses rather
  than prose, independence is usually visible in the signature: A1 does not
  appear in `execution_confined_by_cap_bound`, so it is trivially independent
  of it. Such cells are real but carry no information beyond the statement.
  Only cells where an assumption is *implicitly* in play — via a shared model
  rather than a hypothesis — are worth a theorem. Recorded here so the matrix
  does not inflate its count with signature-reading.

  CELLS PROVED IN THE KERNEL SO FAR:
    N  A5 (non-negativity) for the capacity bound
         -- Assumptions.A5_nonneg_necessary
    I  A1 for coherence preservation
         -- Assumptions.A1_insufficient_for_coherence
         Non-trivial: A1 does not appear as a hypothesis, but one might
         expect the ratification counterexample to depend on the degenerate
         token predicate. It does not.
    N  is_safe_signal_Z for support transport
         -- this module
    N  actor e = Actor.agent for coherence preservation
         -- this module
    NOT-N  massPos (A5, second half) for the capacity bound
         -- this module; the hypothesis is droppable
-/

namespace DARM
namespace Minimality

open DARM.Boundary

private lemma Z_eval :
    Z (reweight (0 : ℝ) ![0, 0] (![3, 1] : Fin 2 → ℝ)) = 4 := by
  rw [DARM.StrictExpansion.reweight_zero_eta]
  norm_num [Z, Fin.sum_univ_two]

private lemma one_active_before :
    (1 : Fin 2) ∈ active (1/2 : ℝ) (![3, 1] : Fin 2 → ℝ) := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  norm_num

/-- **Necessity cell: the safety certificate cannot be dropped from
    `transportSupp`.**

    Witness: `w = (3, 1)`, `δ = 1/2`, `η = 0` (so the update is pure
    renormalization). Both coordinates start above the floor. Total mass is 4,
    so after normalization they are `3/4` and `1/4`, and coordinate 1 falls
    below `δ`. Support is not preserved.

    Safety fails for exactly the same reason it must: it demands
    `δ * Z ≤ W i` for every active `i`, and here `δ * Z = 2 > 1 = W 1`.

    Note the contrast with A5. Non-negativity is NOT necessary for
    `transportSupp` — that theorem carries no sign hypothesis, because
    post-update membership `δ ≤ W i / Z` is literally the safety condition
    `δ * Z ≤ W i` once `Z > 0`. Non-negativity only becomes load-bearing
    where the active coordinates are SUMMED, which is the capacity bound. -/
theorem safety_necessary_for_transport :
    ∃ (δ η : ℝ) (loss w : Fin 2 → ℝ),
      0 < Z (reweight η loss w) ∧
      ¬ is_safe_signal_Z δ η loss w ∧
      ¬ (active δ w ⊆
          active δ (DARM.Boundary.normalize
            (reweight η loss w) (Z (reweight η loss w)))) := by
  refine ⟨1/2, 0, ![0, 0], ![3, 1], ?_, ?_, ?_⟩
  · -- total mass is 4
    rw [Z_eval]; norm_num
  · -- safety fails at coordinate 1: it demands 2 ≤ 1
    intro hs
    have h := hs 1 one_active_before
    rw [Z_eval, DARM.StrictExpansion.reweight_zero_eta] at h
    norm_num at h
  · -- and support is genuinely lost: coordinate 1 drops to 1/4 < 1/2
    intro hsub
    have h := hsub one_active_before
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at h
    unfold DARM.Boundary.normalize at h
    rw [Z_eval, DARM.StrictExpansion.reweight_zero_eta] at h
    norm_num at h


/-! ## C2 — the agent hypothesis -/

private lemma Z2 : Z (reweight (0 : ℝ) ![0, 0] (![1, 0] : Fin 2 → ℝ)) = 1 := by
  rw [DARM.StrictExpansion.reweight_zero_eta]
  norm_num [Z, Fin.sum_univ_two]

/-- **Necessity cell: `actor e = Actor.agent` cannot be dropped from
    `coherence_preserved_under_agent_event`.**

    Witness: `δ = 1`, `w = (1, 0)`, `η = 0`. The active set is `{0}`; the
    state starts with empty policy, so it is coherent; total mass is 1 and
    the safety certificate holds. A human then ratifies `{1}` — a coordinate
    sitting at weight zero, far below the floor. Coherence fails.

    `actor (authenticatedRatification _ _) = .human`, so this is precisely an
    event outside the theorem's hypothesis.

    NOTE ON CONFOUNDING. Tokens here are `Bool` with `validToken = (· = true)`,
    so A1 (token unforgeability) HOLDS in this model and the ratifier presents
    a valid token. The failure is attributable to the actor hypothesis alone,
    not to weak authentication. Compare
    `Assumptions.A1_insufficient_for_coherence`, which makes the dual point. -/
theorem agent_hypothesis_necessary_for_coherence :
    ∃ (s : State Unit (Fin 2)) (e : Event Unit (Fin 2) Bool)
      (δ η : ℝ) (loss w : Fin 2 → ℝ),
      actor e ≠ Actor.agent ∧
      0 < Z (reweight η loss w) ∧
      is_safe_signal_Z δ η loss w ∧
      DARM.Composition.IsCoherent s δ w ∧
      ¬ DARM.Composition.IsCoherent
          (step (fun _ : Fin 2 => ()) (∅ : Finset Unit)
            (fun b : Bool => b = true) s e) δ
          (DARM.Boundary.normalize (reweight η loss w) (Z (reweight η loss w))) := by
  refine ⟨{ cap := ∅, policy := ∅, opState := OpState.active, lastExecuted := none },
          Event.authenticatedRatification true {1},
          1, 0, ![0, 0], ![1, 0], ?_, ?_, ?_, ?_, ?_⟩
  · -- ratification is a human event
    simp [actor]
  · -- total mass is 1
    rw [Z2]; norm_num
  · -- safety: the only active coordinate is 0, and 1 * 1 ≤ 1
    intro i hi
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [Z2, DARM.StrictExpansion.reweight_zero_eta]
    linarith
  · -- the starting state has empty policy
    exact Finset.empty_subset _
  · -- but the ratified policy {1} is not backed: w 1 = 0 < 1
    intro h
    unfold DARM.Composition.IsCoherent at h
    have h1 : (1 : Fin 2) ∈
        (step (fun _ : Fin 2 => ()) (∅ : Finset Unit) (fun b : Bool => b = true)
          { cap := ∅, policy := ∅, opState := OpState.active,
            lastExecuted := none }
          (Event.authenticatedRatification true {1})).policy := by
      simp [step]
    have hmem := h h1
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    unfold DARM.Boundary.normalize at hmem
    rw [Z2, DARM.StrictExpansion.reweight_zero_eta] at hmem
    norm_num at hmem


/-! ## C3 — the positive-mass hypothesis is NOT necessary -/

/-- **Negative cell: `massPos` can be dropped from the capacity bound.**

    `Reachability.active_card_mul_delta_le_one` assumes `0 < Z v`. It does not
    need to. Given non-negativity, `Z v ≥ 0`, so the only case the hypothesis
    excludes is `Z v = 0`, and there the bound holds anyway:

      * `δ > 0`  — `normalize v 0 i = v i / 0 = 0`, so nothing clears the
                   floor and the active set is empty;
      * `δ ≤ 0`  — the product of a non-negative cardinality and a
                   non-positive `δ` is at most 0.

    So A5 splits: its non-negativity half is necessary
    (`Assumptions.A5_nonneg_necessary`), its positive-mass half is not.

    CAVEAT — READ BEFORE CITING. This depends on Lean's total division, where
    `x / 0 = 0`. In ordinary mathematics `normalize v 0` is undefined and the
    question does not arise. The honest reading is that `massPos` is not
    needed *for this formalization*, not that positive mass is mathematically
    irrelevant to normalization. Recorded as a cell because a minimality
    matrix that silently carries an unnecessary hypothesis is overstating what
    the theorem requires — but the reason it is unnecessary is a convention,
    not a discovery. -/
theorem massPos_not_necessary_for_capacity
    {n : ℕ} (δ : ℝ) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ((active δ (DARM.Boundary.normalize v (Z v))).card : ℝ) * δ ≤ 1 := by
  have hZnn : 0 ≤ Z v := by
    simp only [Z]
    exact Finset.sum_nonneg (fun i _ => hv i)
  rcases hZnn.eq_or_lt with h | h
  · -- degenerate case: total mass is zero
    rw [← h]
    by_cases hd : δ ≤ 0
    · have hc : (0 : ℝ) ≤ ((active δ (DARM.Boundary.normalize v 0)).card : ℝ) :=
        Nat.cast_nonneg _
      nlinarith
    · have hd' : 0 < δ := not_le.mp hd
      have hempty : active δ (DARM.Boundary.normalize v 0) = ∅ := by
        ext i
        simp only [active, Finset.mem_filter, Finset.mem_univ, true_and,
                   Finset.notMem_empty, iff_false]
        unfold DARM.Boundary.normalize
        rw [div_zero]
        exact not_le.mpr hd'
      rw [hempty]
      simp
  · -- the hypothesis actually held
    exact DARM.Reachability.active_card_mul_delta_le_one δ v hv h

/-! ## Next cells, in order of expected cost

  C4. A4 versus capability confinement. Blocked: `Influence.lean` and
      `Basic.lean` share no types, so there is no single model in which both
      A4 and `capInvariant` can be stated. This is the standing structural
      gap, not a missing proof.
-/

end Minimality
end DARM

#print axioms DARM.Minimality.safety_necessary_for_transport
#print axioms DARM.Minimality.agent_hypothesis_necessary_for_coherence
#print axioms DARM.Minimality.massPos_not_necessary_for_capacity
