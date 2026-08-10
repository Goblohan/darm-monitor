import DarmMonitor.Ratification

/-!
  StrictExpansion — a concrete witness that `safe_update_expands_ratifiable_set`
  is not vacuous.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.
  `sorryAx`. Do not describe as verified before both.

  THE VACUITY WORRY. `Ratification.safe_update_expands_ratifiable_set` proves
      Ratifiable δ w ⊆ Ratifiable δ w'
  under the Z-safety condition. If the safety condition secretly forced
      active δ w' = active δ w
  for every admissible update, that inclusion would be an equality and the
  "negative result" would say nothing. This module refutes that by exhibiting
  a safe update under which the active set strictly grows.

  THE WITNESS.  n = 2, δ = 1/4, η = 0, loss = 0, w = (3/10, 1/5).
    Z = 1/2.
    active δ w = {0}          (1/4 ≤ 3/10; 1/4 > 1/5)
    safety:  δ·Z = 1/8 ≤ 3/10 ✓
    after normalizing by Z:  (3/5, 2/5), both ≥ 1/4
    active δ w' = {0, 1}      -- coordinate 1 resurrected

  WHY δ < 1/2 IS FORCED. For strict expansion we need w₀ ≥ δ, w₁ < δ, and
  w₁/Z ≥ δ. The last two give δ·Z ≤ w₁ < δ, hence Z < 1. And Z = w₀ + w₁ ≥
  δ + δZ gives Z ≥ δ/(1-δ). Both together require δ/(1-δ) < 1, i.e. δ < 1/2.
  At δ = 1/2 exactly, no witness of this shape exists.

  SCOPE — READ THIS BEFORE CITING THE RESULT.
  With η = 0 the reweighting is the identity map, so this witness exercises
  ONLY the normalization channel: expansion comes from Z < 1 inflating every
  coordinate, not from any asymmetry in `loss`. Two consequences:
    (i)  It DOES kill the vacuity worry. Strict expansion is possible under
         a fully satisfied Z-certificate. That is what it was written for.
    (ii) It does NOT show the agent can STEER expansion. With η = 0 the agent
         has no influence over the update at all — `loss` is annihilated.
         Whether an agent choosing `loss` can drive the active set to a chosen
         superset remains open (Ratification.R1), and this witness is evidence
         for neither side of that question.
-/

namespace DARM.StrictExpansion

open DARM.Boundary DARM.Ratification

/-- With `η = 0` the multiplicative-weights update is the identity: every
    factor is `exp 0 = 1`. Stated separately because it is the engine of the
    witness below and worth being able to cite on its own. -/
lemma reweight_zero_eta {n : ℕ} (loss w : Fin n → ℝ) :
    reweight (0 : ℝ) loss w = w := by
  funext i
  simp [reweight]

/-- **Non-vacuity.** There is a weight vector and a Z-safe update under which
    the active set strictly grows. Hence the inclusion in
    `safe_update_expands_ratifiable_set` is not an equality in general. -/
theorem strict_expansion_witness :
    ∃ (δ η : ℝ) (loss w : Fin 2 → ℝ),
      0 < Z (reweight η loss w) ∧
      is_safe_signal_Z δ η loss w ∧
      active δ w ⊂
        active δ (normalize (reweight η loss w) (Z (reweight η loss w))) := by
  refine ⟨1/4, 0, ![0, 0], ![3/10, 1/5], ?_, ?_, ?_⟩
  · -- 0 < Z = 1/2
    rw [reweight_zero_eta]
    simp [Z, Fin.sum_univ_two]
    norm_num
  · -- safety: for every active i, δ·Z ≤ w i.  δ·Z = 1/8 and active ⇒ 1/4 ≤ w i.
    intro i hi
    rw [reweight_zero_eta] at *
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hZ : Z (![3/10, 1/5] : Fin 2 → ℝ) = 1/2 := by
      simp [Z, Fin.sum_univ_two]; norm_num
    rw [hZ]
    linarith
  · -- strict: coordinate 1 is inactive before and active after
    have hZpos : 0 < Z (reweight (0:ℝ) ![0,0] (![3/10, 1/5] : Fin 2 → ℝ)) := by
      rw [reweight_zero_eta]
      simp [Z, Fin.sum_univ_two]
      norm_num
    have hsafe : is_safe_signal_Z (1/4) 0 ![0,0] (![3/10, 1/5] : Fin 2 → ℝ) := by
      intro i hi
      rw [reweight_zero_eta] at *
      simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hZ : Z (![3/10, 1/5] : Fin 2 → ℝ) = 1/2 := by
        simp [Z, Fin.sum_univ_two]; norm_num
      rw [hZ]
      linarith
    have hsub := transportSupp (1/4) 0 ![0,0] (![3/10, 1/5] : Fin 2 → ℝ) hZpos hsafe
    rw [Finset.ssubset_def]
    refine ⟨hsub, ?_⟩
    intro hcon
    -- coordinate 1 IS active after the update: w₁/Z = (1/5)/(1/2) = 2/5 ≥ 1/4
    have hafter : (1 : Fin 2) ∈
        active (1/4) (normalize (reweight (0:ℝ) ![0,0] (![3/10, 1/5] : Fin 2 → ℝ))
          (Z (reweight (0:ℝ) ![0,0] (![3/10, 1/5] : Fin 2 → ℝ)))) := by
      simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      unfold DARM.Boundary.normalize
      rw [reweight_zero_eta]
      have hZ : Z (![3/10, 1/5] : Fin 2 → ℝ) = 1/2 := by
        simp [Z, Fin.sum_univ_two]; norm_num
      rw [hZ]
      norm_num
    -- but coordinate 1 is NOT active before: 1/4 > 1/5
    have hbefore := hcon hafter
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hbefore
    norm_num at hbefore

end DARM.StrictExpansion

#print axioms DARM.StrictExpansion.reweight_zero_eta
#print axioms DARM.StrictExpansion.strict_expansion_witness
