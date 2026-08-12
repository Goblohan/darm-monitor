import DarmMonitor.GuardStability

/-!
  A5Redundancy — `hZ` follows from A5 alone.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT THIS COMPLETES. `MinimalityZ` proved `hZ : 0 < Z (reweight η loss w)` is
  NECESSARY for `safe_signal_equiv` — the witness uses a negative weight, which
  A5 forbids. It registered the other half as a follow-up: that under A5 the
  hypothesis is automatic. This is that half.

  A CORRECTION TO MY OWN PROSE. `MinimalityZ`'s registered status says the
  redundancy holds "under A5 with a positive margin and a nonempty active set".
  Neither extra condition is needed. A5's `massPos` — `0 < Z w` — suffices on
  its own: a non-negative vector with positive total mass has some coordinate
  strictly positive, `exp` is positive everywhere, so the reweighted sum has all
  terms non-negative and one strictly positive.

  The over-hypothesis was harmless but it was there, and stating the weaker
  sufficient condition is the point of the exercise.

  THE DISTINCTION THIS COMPLETES. `hZ` is:

      NECESSARY   for `safe_signal_equiv` as stated — the statement permits
                  negative weights and the equivalence fails on one
      REDUNDANT   for any A5-satisfying deployment — no such weights exist there

  Both are true. Recording only the first suggests users must check something;
  only the second suggests the hypothesis could be deleted. It is the price of
  stating the theorem more generally than any deployment needs.
-/

namespace DARM
namespace A5Redundancy

open DARM.Boundary DARM.Assumptions

/-! ## A non-negative vector with positive mass has a positive coordinate -/

private lemma exists_pos_of_wellFormed {n : ℕ} {w : Fin n → ℝ}
    (hw : WellFormedWeights w) : ∃ j, 0 < w j := by
  by_contra h
  push Not at h
  have hall : ∀ j, w j = 0 := fun j => le_antisymm (h j) (hw.nonneg j)
  have hzero : Z w = 0 := by
    unfold Z
    simp [hall]
  have := hw.massPos
  linarith

/-! ## The redundancy -/

/-- **A5 implies `hZ`.** For any learning rate and any loss, a well-formed
    weight vector reweights to positive total mass.

    No condition on `δ`, and no condition on the active set. `exp` is positive
    everywhere, so the reweighting cannot destroy mass that A5 guarantees is
    there. -/
theorem hZ_of_A5 {n : ℕ} (η : ℝ) (loss : Fin n → ℝ) {w : Fin n → ℝ}
    (hw : WellFormedWeights w) :
    0 < Z (reweight η loss w) := by
  obtain ⟨j, hj⟩ := exists_pos_of_wellFormed hw
  unfold Z reweight
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hw.nonneg i) (Real.exp_pos _).le
  · exact ⟨j, Finset.mem_univ j, mul_pos hj (Real.exp_pos _)⟩

/-- **`safe_signal_equiv` under A5**, with the positivity hypothesis discharged.
    This is the form a deployment uses: supply well-formed weights and the
    equivalence holds, with nothing further to check. -/
theorem safe_signal_equiv_of_A5 {n : ℕ} (δ η : ℝ) (loss : Fin n → ℝ)
    {w : Fin n → ℝ} (hw : WellFormedWeights w) :
    is_safe_signal_Z δ η loss w ↔ is_safe_signal_post δ η loss w :=
  safe_signal_equiv δ η loss w (hZ_of_A5 η loss hw)

/-! ## Registered status

  DONE: the redundancy, and with it the full picture for `hZ`. Necessary for
  the general statement, automatic under A5, and `safe_signal_equiv_of_A5` is
  the form with nothing left to check.

  WHAT THIS SUGGESTS FOR THE OTHER HYPOTHESES. Several kernel theorems carry
  `hZ` or sign conditions inline rather than deriving them from A5 —
  `Assumptions.lean`'s registered status already lists re-parameterizing them as
  NEXT. This module is one instance done. Whether the others are equally
  immediate has not been checked; `hZ` was easy because `exp` is positive
  unconditionally, and a hypothesis depending on `δ` or the active set would
  not be.
-/

end A5Redundancy
end DARM

#print axioms DARM.A5Redundancy.hZ_of_A5
#print axioms DARM.A5Redundancy.safe_signal_equiv_of_A5
