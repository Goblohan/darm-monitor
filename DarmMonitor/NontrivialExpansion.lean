import DarmMonitor.StrictExpansion

/-
  NontrivialExpansion — strict expansion of the active set under a Z-SAFE
  update with η ≠ 0 and loss ≠ 0.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHY THIS EXISTS. `StrictExpansion.strict_expansion_witness` used η = 0,
  which annihilates `loss` (every factor is exp 0 = 1) and reduces the update
  to pure renormalization. It killed the vacuity worry but said nothing about
  whether the loss channel can drive expansion.

  STATEMENT CHANGE (deliberate, flag this in review). The previous skeleton
  omitted `is_safe_signal_Z` from the conjunction. Without it the theorem is
  near-trivial: an arbitrary reweighting can move coordinates anywhere, so
  expansion is unsurprising and says nothing about the monitor's certificate.
  The safety conjunct is added here. The witness below satisfies it, so this
  is a strengthening rather than a weakening.

  THE WITNESS.  δ = 1/4, η = 1, loss = (0, -1), w = (3/10, 1/10).
    reweight = (3/10, e/10)          -- exp(-1 * 0) = 1, exp(-1 * -1) = e
    Z        = 3/10 + e/10 ≈ 0.5718
    active δ w  = {0}                 -- 1/4 ≤ 3/10; 1/4 > 1/10
    after normalizing: (0.5247, 0.4754), both ≥ 1/4
    active δ w' = {0, 1}              -- coordinate 1 resurrected

  WHY THE TRANSCENDENTALS CANCEL. Every obligation reduces to a crude bound:
    coordinate 1 crosses:  (1/4)(3/10 + e/10) ≤ e/10  ⟺  3/40 ≤ 3e/40  ⟺  1 ≤ e
    coordinate 0 stays:    (1/4)(3/10 + e/10) ≤ 3/10  ⟺  e ≤ 9
    safety (i = 0 only):   same as coordinate 0 staying — e ≤ 9
  So `2 ≤ e ≤ 3` suffices throughout; no decimal expansion of e is needed.

  WHAT THIS DOES AND DOES NOT SETTLE.
    Settles: a Z-safe update with a genuinely non-constant loss vector can
    strictly enlarge the active set, hence the ratifiable policy space. The
    expansion is not an artifact of renormalization alone.
    Does NOT settle: R1, reachability. Whether an agent choosing `loss` can
    drive the active set to a CHOSEN superset is untouched. This is one
    witness, not a characterization. There is still no agent in the model.
-/

namespace DARM
namespace NontrivialExpansion

open DARM.Boundary

/-! ## Bounds on e

  Only `2 ≤ e ≤ 3` is needed. Both come from standard Mathlib facts. -/

private lemma two_le_e : (2 : ℝ) ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  linarith

private lemma e_le_three : Real.exp 1 ≤ 3 := by
  have h := Real.exp_one_lt_d9
  norm_num at h
  linarith

/-! ## Evaluating the update at the witness -/

private lemma rw_eval :
    reweight (1 : ℝ) ![0, -1] (![3/10, 1/10] : Fin 2 → ℝ)
      = ![3/10, (1/10) * Real.exp 1] := by
  funext i
  fin_cases i <;> simp [reweight]

private lemma Z_eval :
    Z (reweight (1 : ℝ) ![0, -1] (![3/10, 1/10] : Fin 2 → ℝ))
      = 3/10 + (1/10) * Real.exp 1 := by
  rw [rw_eval]
  simp [Z, Fin.sum_univ_two]

private lemma Z_pos :
    0 < Z (reweight (1 : ℝ) ![0, -1] (![3/10, 1/10] : Fin 2 → ℝ)) := by
  rw [Z_eval]
  have := two_le_e
  linarith

private lemma denom_pos : (0 : ℝ) < 3/10 + (1/10) * Real.exp 1 := by
  have := two_le_e
  linarith

/-! ## The active set before the update is exactly {0} -/

private lemma active_before :
    active (1/4 : ℝ) (![3/10, 1/10] : Fin 2 → ℝ) = {0} := by
  ext i
  fin_cases i <;>
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_singleton] <;>
    norm_num

/-! ## Both coordinates are active after the update -/

private lemma mem_zero_after :
    (0 : Fin 2) ∈ active (1/4 : ℝ)
      (DARM.Boundary.normalize (reweight (1 : ℝ) ![0, -1] (![3/10, 1/10] : Fin 2 → ℝ))
        (Z (reweight (1 : ℝ) ![0, -1] (![3/10, 1/10] : Fin 2 → ℝ)))) := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold DARM.Boundary.normalize
  rw [Z_eval, rw_eval, le_div_iff₀ denom_pos]
  simp only [Matrix.cons_val_zero]
  have := e_le_three
  linarith

private lemma mem_one_after :
    (1 : Fin 2) ∈ active (1/4 : ℝ)
      (DARM.Boundary.normalize (reweight (1 : ℝ) ![0, -1] (![3/10, 1/10] : Fin 2 → ℝ))
        (Z (reweight (1 : ℝ) ![0, -1] (![3/10, 1/10] : Fin 2 → ℝ)))) := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold DARM.Boundary.normalize
  rw [Z_eval, rw_eval, le_div_iff₀ denom_pos]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  have := two_le_e
  linarith

/-! ## Main result -/

theorem nontrivial_reweight_strict_expansion :
    ∃ (δ η : ℝ) (loss w : Fin 2 → ℝ),
      η ≠ 0 ∧
      loss ≠ 0 ∧
      reweight η loss w ≠ w ∧
      0 < Z (reweight η loss w) ∧
      is_safe_signal_Z δ η loss w ∧
      active δ w ⊂
        active δ
          (DARM.Boundary.normalize
            (reweight η loss w)
            (Z (reweight η loss w))) := by
  refine ⟨1/4, 1, ![0, -1], ![3/10, 1/10], ?_, ?_, ?_, Z_pos, ?_, ?_⟩
  · -- η ≠ 0
    norm_num
  · -- loss ≠ 0
    intro h
    have h1 := congrFun h 1
    norm_num at h1
  · -- reweight ≠ w : coordinate 1 would force e = 1
    rw [rw_eval]
    intro h
    have h1 := congrFun h 1
    -- `norm_num` reduces this to `Real.exp 1 = 1`, hence `1 = 0`, closing the goal.
    norm_num at h1
  · -- safety: active before is {0}, and (1/4) * Z ≤ 3/10 reduces to e ≤ 9
    intro i hi
    rw [active_before] at hi
    simp only [Finset.mem_singleton] at hi
    subst hi
    rw [Z_eval, rw_eval]
    simp only [Matrix.cons_val_zero]
    have := e_le_three
    linarith
  · -- strict expansion
    rw [active_before, Finset.ssubset_def]
    constructor
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      subst hi
      exact mem_zero_after
    · intro hcon
      have h := hcon mem_one_after
      simp only [Finset.mem_singleton] at h
      exact absurd h (by decide)

end NontrivialExpansion
end DARM

#print axioms DARM.NontrivialExpansion.nontrivial_reweight_strict_expansion
