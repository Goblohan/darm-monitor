import DarmMonitor.NontrivialExpansion

/-
  Reachability — the capacity bound on the active set (registered problem R1).

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`.

  THE QUESTION (Ratification.R1). `safe_update_expands_ratifiable_set` shows a
  Z-safe update cannot shrink the active set. `StrictExpansion` and
  `NontrivialExpansion` show it can strictly grow it, under renormalization
  alone and under genuine reweighting respectively. The open question was
  whether growth is UNBOUNDED — whether a chosen `loss` can drive the active
  set to an arbitrary superset, and hence the ratifiable policy space to an
  arbitrary superset.

  THE ANSWER: NO, and the obstruction is a cardinality bound.

    |active δ w'| * δ ≤ 1

  after any normalization of a non-negative weight vector. At most 1/δ
  coordinates can sit at or above the margin floor once the vector is
  normalized to unit mass, because each active coordinate consumes δ of the
  total and the total is 1.

  SCOPE — note what the hypotheses do NOT include.
  This holds for ANY non-negative weight vector. It does not require
  `is_safe_signal_Z`, does not mention `reweight`, and does not depend on η or
  `loss`. So it is not a fact about safe updates or about agents: it is a
  structural property of the margin floor under normalization. No update rule
  preserving non-negativity can exceed it.

  TIGHTNESS. The bound is close to exact. Taking v = 1 on a target set B and
  v = ε off it, and letting ε → 0, gives active = B whenever δ|B| < 1. So
  reachable sets are characterized by δ|B| < 1, against a proven bound of
  δ|B| ≤ 1 — the two differ only at the boundary. The construction requires
  `Real.log` to invert `exp` and is NOT formalized here; see R1b below.
-/

namespace DARM
namespace Reachability

open DARM.Boundary

/-- **Capacity bound.** After normalizing a non-negative weight vector to
    unit mass, at most `1/δ` coordinates can lie at or above the margin
    floor `δ`.

    Proof: each active coordinate has `v i ≥ δ * Z`; summing over the active
    set and bounding by the total mass gives `|S| * δ * Z ≤ Z`; divide by
    `Z > 0`. -/
theorem active_card_mul_delta_le_one
    {n : ℕ} (δ : ℝ) (v : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hZ : 0 < Z v) :
    ((active δ (DARM.Boundary.normalize v (Z v))).card : ℝ) * δ ≤ 1 := by
  set S := active δ (DARM.Boundary.normalize v (Z v)) with hSdef
  -- every active coordinate carries at least δ * Z of the mass
  have key : ∀ i ∈ S, δ * Z v ≤ v i := by
    intro i hi
    rw [hSdef] at hi
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    unfold DARM.Boundary.normalize at hi
    exact (le_div_iff₀ hZ).mp hi
  -- so the active set consumes at least |S| * δ * Z
  have h1 : (S.card : ℝ) * (δ * Z v) ≤ ∑ i ∈ S, v i := by
    calc (S.card : ℝ) * (δ * Z v)
        = ∑ _i ∈ S, (δ * Z v) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, v i := Finset.sum_le_sum key
  -- but the whole vector only has Z of it
  have h2 : ∑ i ∈ S, v i ≤ Z v := by
    simp only [Z]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => hv i)
  have h3 : ((S.card : ℝ) * δ) * Z v ≤ 1 * Z v := by
    rw [mul_assoc, one_mul]
    exact le_trans h1 h2
  exact le_of_mul_le_mul_right h3 hZ

/-- The same bound in the setting that matters: an arbitrary multiplicative
    reweighting of a non-negative vector, followed by normalization. No
    hypothesis on `η`, on `loss`, or on the safety certificate.

    This is the negative answer to R1: whatever signal is synthesised, the
    post-update active set has at most `1/δ` elements. -/
theorem reweight_active_card_bounded
    {n : ℕ} (δ η : ℝ) (loss w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hZ : 0 < Z (reweight η loss w)) :
    ((active δ (DARM.Boundary.normalize (reweight η loss w)
      (Z (reweight η loss w)))).card : ℝ) * δ ≤ 1 := by
  refine active_card_mul_delta_le_one δ (reweight η loss w) ?_ hZ
  intro i
  simp only [reweight]
  exact mul_nonneg (hw i) (Real.exp_pos _).le

/-! ## Registered status of R1

  R1a — UPPER BOUND: CLOSED (negatively).
    Reach is not arbitrary. `reweight_active_card_bounded` caps the active set,
    and hence the guarded-ratifiable policy space, at `1/δ` coordinates
    independent of the synthesised signal.

  R1b — EXACT CHARACTERIZATION: OPEN.
    Conjecture: for A = active δ w and B ⊇ A with B ≠ ∅, B is reachable by a
    Z-safe update iff δ|B| < 1. The forward direction follows from the bound
    above; the converse needs the ε-construction and `Real.log` to invert
    `exp`, and is not formalized. The boundary cases B = ∅ and B = univ behave
    differently and would need separate treatment.

  R1c — STILL NOT AN AGENT RESULT.
    There is no actor, objective, or choice anywhere in this development.
    `loss` is a universally quantified parameter. Statements about what "an
    agent can do" remain interpretation, not theorem.
-/

end Reachability
end DARM

#print axioms DARM.Reachability.active_card_mul_delta_le_one
#print axioms DARM.Reachability.reweight_active_card_bounded
