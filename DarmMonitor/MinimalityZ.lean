import DarmMonitor.MinimalityGuard

/-
  MinimalityZ — `hZ` is necessary for `safe_signal_equiv`, and redundant under A5.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  THE CELL. `BoundaryMargin.safe_signal_equiv` carries `hZ : 0 < Z (reweight η loss w)`.
  Drop it and the biconditional fails, because Lean's division is total: with
  `Z = 0` the two sides say different things.

      Z-form     δ * Z ≤ w' i        becomes   0 ≤ w' i
      post-form  δ ≤ w' i / Z        becomes   δ ≤ 0     (since x / 0 = 0)

  At `η = 0` — so `reweight` is the identity — weights `(1, -1)`, and `δ = 1`,
  the active set is `{0}`, `Z = 0`, the Z-form holds (`0 ≤ 1`) and the post-form
  fails (`1 ≤ 0`). So `hZ` cannot be dropped.

  THE MORE INTERESTING HALF, stated but not proved here. That witness needs a
  NEGATIVE weight, which A5 (`WellFormedWeights`) forbids. Under A5, with
  `δ > 0` and a nonempty active set, some coordinate satisfies `w i ≥ δ > 0`;
  since `exp` is positive and the other weights are non-negative,
  `Z (reweight η loss w) > 0` follows. So `hZ` is:

      NECESSARY   for the theorem as stated, which assumes nothing about signs
      REDUNDANT   for any deployment satisfying A5 — see `A5Redundancy.lean`

  That is a real distinction and worth keeping separate. The theorem is stated
  more generally than any deployment needs, and `hZ` is the price of that
  generality rather than a constraint on users. Proving the redundancy would
  need `Real.exp_pos` and a sum-positivity argument; it is registered below as
  the natural follow-up, not claimed here.
-/

namespace DARM
namespace MinimalityZ

open DARM.Boundary

/-! ## The countermodel -/

/-- Weights summing to zero: `reweight` at `η = 0` leaves them unchanged. -/
def mixedWeights : Fin 2 → ℝ := ![1, -1]

/-- At `η = 0` the update is the identity, because `exp 0 = 1`. -/
theorem reweight_zero_eq (loss : Fin 2 → ℝ) (i : Fin 2) :
    reweight 0 loss mixedWeights i = mixedWeights i := by
  unfold reweight
  simp

/-- The total mass vanishes. -/
theorem Z_mixed_zero (loss : Fin 2 → ℝ) :
    Z (reweight 0 loss mixedWeights) = 0 := by
  unfold Z
  rw [Fin.sum_univ_two]
  rw [reweight_zero_eq, reweight_zero_eq]
  unfold mixedWeights
  simp

/-- **`hZ` is necessary for `safe_signal_equiv`.**

    At the witness the Z-form holds and the post-form fails, so the
    biconditional is false without the positivity hypothesis. -/
theorem hZ_necessary_for_equiv :
    is_safe_signal_Z 1 0 (fun _ => 0) mixedWeights
      ∧ ¬ is_safe_signal_post 1 0 (fun _ => 0) mixedWeights := by
  constructor
  · -- Z-form: δ * Z = 1 * 0 = 0, and the active coordinate carries weight 1
    intro i hi
    rw [Z_mixed_zero, reweight_zero_eq]
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    unfold mixedWeights at hi ⊢
    fin_cases i <;> simp_all <;> linarith
  · -- post-form: δ ≤ w' i / 0 = 0, i.e. 1 ≤ 0, false
    intro h
    have h0 : (0 : Fin 2) ∈ active (1 : ℝ) mixedWeights := by
      simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      unfold mixedWeights
      simp
    have := h 0 h0
    unfold DARM.Boundary.normalize at this
    rw [Z_mixed_zero, reweight_zero_eq] at this
    unfold mixedWeights at this
    simp at this
    linarith

/-! ## Registered status

  DONE: the `hZ` cell. Eleven cells now proved.

 DONE ELSEWHERE. `A5Redundancy.hZ_of_A5` proves the redundancy. It needs LESS
  than this file originally claimed: not a positive margin, not a nonempty
  active set, just A5's `massPos`. A non-negative vector with positive mass has
  a positive coordinate, `exp` is positive everywhere, so the reweighted sum is
  positive. The extra conditions stated here were an over-hypothesis.

  WHY BOTH MATTER. A hypothesis can be necessary for a theorem and yet never
  bind in practice, because the theorem is stated more generally than any
  deployment requires. Recording only the necessity would suggest `hZ` is a
  constraint users must check; recording only the redundancy would suggest it
  could be deleted from the statement. Neither alone is the whole picture.
-/

end MinimalityZ
end DARM

#print axioms DARM.MinimalityZ.reweight_zero_eq
#print axioms DARM.MinimalityZ.Z_mixed_zero
#print axioms DARM.MinimalityZ.hZ_necessary_for_equiv
