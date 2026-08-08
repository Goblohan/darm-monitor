import DarmMonitor.A5Redundancy
import DarmMonitor.RationalInstance

/-
  A5RedundancyRational — the rational update's `hZ` needs more than A5.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  THE ASYMMETRY. `A5Redundancy.hZ_of_A5` discharges `hZ` for the exponential
  update from A5 alone, because `exp` is positive for every argument. The
  rational update is different:

      ratReweight η loss w i = w i / (1 + η * loss i)

  The denominator can be negative. A5 constrains the weights and says nothing
  about `η * loss`, so a well-formed weight vector can reweight to zero or
  negative total mass.

  BOTH DIRECTIONS ARE PROVED HERE.

    * `hZ_of_A5_rat` — with the domain condition `∀ i, -1 < η * loss i`, the
      redundancy holds exactly as it does for `exp`.

    * `A5_insufficient_for_rat` — without it, A5 does NOT suffice. The witness
      is `w = (1, 1)` (non-negative, total mass 2, so A5 holds), `η = 1`,
      `loss = (0, -2)`. Then the second denominator is `-1`, the reweighted
      vector is `(1, -1)`, and `Z = 0`.

  WHY THIS IS WORTH PROVING RATHER THAN NOTING. `BoundaryCore` already records
  two ways the rational surrogate is weaker than `exp` — it does not compose,
  and it is not globally positive. This is a third, and it is the one that
  bites a caller: under the exponential update a deployment satisfying A5 has
  nothing further to check, and under the rational update it does. That is a
  difference in obligations, not just in properties.
-/

namespace DARM
namespace A5RedundancyRational

open DARM.Boundary DARM.Assumptions DARM.RationalInstance

/-! ## 1. With the domain condition, the redundancy holds -/

/-- **A5 plus the domain condition implies `hZ`** for the rational update.

    Same shape as `A5Redundancy.hZ_of_A5`: some coordinate is strictly positive
    by `massPos`, every denominator is positive by hypothesis, so the sum is
    positive. -/
theorem hZ_of_A5_rat {n : ℕ} (η : ℝ) (loss : Fin n → ℝ) {w : Fin n → ℝ}
    (hw : WellFormedWeights w)
    (hdom : ∀ i, -1 < η * loss i) :
    0 < Z (ratReweight η loss w) := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < w j := by
    by_contra h
    push_neg at h
    have hall : ∀ j, w j = 0 := fun j => le_antisymm (h j) (hw.nonneg j)
    have hzero : Z w = 0 := by unfold Z; simp [hall]
    have := hw.massPos
    linarith
  unfold Z ratReweight
  apply Finset.sum_pos'
  · intro i _
    have hden : 0 < 1 + η * loss i := by linarith [hdom i]
    exact div_nonneg (hw.nonneg i) hden.le
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    have hden : 0 < 1 + η * loss j := by linarith [hdom j]
    exact div_pos hj hden

/-! ## 2. Without it, A5 is not enough -/

/-- Non-negative, total mass 2 — A5 holds. -/
def goodWeights : Fin 2 → ℝ := ![1, 1]

/-- But the second denominator is `1 + 1 * (-2) = -1`. -/
def badLoss : Fin 2 → ℝ := ![0, -2]

theorem goodWeights_wellFormed : WellFormedWeights goodWeights := by
  constructor
  · intro i
    fin_cases i <;> simp [goodWeights]
  · unfold Z goodWeights
    rw [Fin.sum_univ_two]
    norm_num

/-- **A5 alone does not discharge `hZ` for the rational update.**

    The weights are well-formed and the reweighted total mass is zero. So the
    exponential instance's unconditional redundancy has no analogue here — the
    domain condition is doing real work, not bookkeeping. -/
theorem A5_insufficient_for_rat :
    WellFormedWeights goodWeights
      ∧ Z (ratReweight 1 badLoss goodWeights) = 0 := by
  refine ⟨goodWeights_wellFormed, ?_⟩
  unfold Z ratReweight goodWeights badLoss
  rw [Fin.sum_univ_two]
  norm_num

/-! ## Registered status

  DONE: both directions. The rational update's `hZ` follows from A5 given the
  domain condition, and does not follow from A5 alone.

  THE PICTURE FOR THE TWO INSTANCES, now complete on this axis:

      exponential   `hZ` redundant under A5, unconditionally
      rational      `hZ` redundant under A5 AND `∀ i, -1 < η * loss i`;
                    A5 alone is insufficient, with a witness

  Together with `BoundaryCore.rational_not_semigroup` and
  `BoundaryCore.ratUpdate_neg_below`, that is three proved respects in which the
  exactly-computable surrogate is weaker than the transcendental one. None of
  them makes it useless — they delimit where it may be used.
-/

end A5RedundancyRational
end DARM

#print axioms DARM.A5RedundancyRational.hZ_of_A5_rat
#print axioms DARM.A5RedundancyRational.goodWeights_wellFormed
#print axioms DARM.A5RedundancyRational.A5_insufficient_for_rat
