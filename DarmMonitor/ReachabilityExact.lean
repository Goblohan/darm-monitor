import DarmMonitor.Reachability

/-
  ReachabilityExact — progress on registered problem R1b.

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`.

  R1b CONJECTURE. For `A = active δ w` and a target `B ⊇ A` with `B ≠ ∅`, `B`
  is reachable by a Z-safe update iff `δ * |B| < 1`.

  THIS MODULE PROVES THE TWO HALVES THAT DO NOT NEED THE ε-CONSTRUCTION.

  1. THE CHANNEL IS SURJECTIVE.
     `reweight_surjective_on_positive`: for any strictly positive source `w`
     and any strictly positive target `v`, there is a `loss` with
     `reweight 1 loss w = v`. Setting `loss i = -log (v i / w i)` and using
     `Real.exp_log` hits the target exactly.

     So the reweighting channel imposes NO constraint on the post-update
     vector beyond positivity. Whatever supplies `loss` has complete control.
     This is what makes R1b a question about the active set alone rather than
     about what the update rule can express.

  2. THE CAPACITY BOUND IS STRICT FOR PROPER SUBSETS.
     `Reachability.active_card_mul_delta_le_one` gives `|S| * δ ≤ 1`. If `S`
     is not everything, some coordinate outside `S` carries positive mass, so
     the sum over `S` falls strictly short of the total and the bound is
     strict: `|S| * δ < 1`. That is the necessity half of R1b at full
     sharpness.

  READ THESE TOGETHER. Total control over the weight vector, and yet the
  active set is still capped — strictly, for any proper subset. The cap is not
  a limitation of the update rule; it is a property of the margin floor under
  normalization, and no choice of signal evades it.

  STILL OPEN (the sufficiency half). Given `δ * |B| < 1`, construct a witness
  realizing exactly `B`. The construction is `v = 1` on `B` and `v = ε` off it,
  with `ε` small enough that `δ * (|B| + (n - |B|) * ε) ≤ 1` while still
  exceeding nothing off `B`. Elementary, but it needs an explicit `ε` and a
  cardinality computation, and it is not attempted here.
-/

namespace DARM
namespace ReachabilityExact

open DARM.Boundary

/-! ## 1. Surjectivity of the reweighting channel -/

/-- **The channel is surjective onto positive vectors.** Any strictly positive
    target is reachable from any strictly positive source by some `loss`,
    at `η = 1`.

    Consequence: the multiplicative-weights form of the update is not a
    restriction on what post-update vectors are achievable. It only enforces
    positivity, which `exp` gives for free.

    Note there is no `Fintype` hypothesis. `reweight` acts pointwise, so
    surjectivity holds for an arbitrary index type — finiteness is needed only
    where `Z` sums. -/
theorem reweight_surjective_on_positive
    {ι : Type*} (w v : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) :
    ∃ loss : ι → ℝ, reweight 1 loss w = v := by
  refine ⟨fun i => -Real.log (v i / w i), ?_⟩
  funext i
  simp only [reweight]
  have hpos : 0 < v i / w i := div_pos (hv i) (hw i)
  have hne : w i ≠ 0 := (hw i).ne'
  have hrw : -(1 : ℝ) * (-Real.log (v i / w i)) = Real.log (v i / w i) := by ring
  rw [hrw, Real.exp_log hpos]
  field_simp

/-! ## 2. The capacity bound is strict for proper subsets -/

/-- Each active coordinate carries at least `δ * Z` of the mass, so the active
    set collectively consumes at least `|S| * δ * Z`. Extracted so both the
    non-strict and strict bounds can use it. -/
private lemma card_mul_le_sum {ι : Type*} [Fintype ι]
    (δ : ℝ) (v : ι → ℝ) (hZ : 0 < Z v) :
    ((active δ (DARM.Boundary.normalize v (Z v))).card : ℝ) * (δ * Z v)
      ≤ ∑ i ∈ active δ (DARM.Boundary.normalize v (Z v)), v i := by
  have key : ∀ i ∈ active δ (DARM.Boundary.normalize v (Z v)), δ * Z v ≤ v i := by
    intro i hi
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    unfold DARM.Boundary.normalize at hi
    exact (le_div_iff₀ hZ).mp hi
  calc ((active δ (DARM.Boundary.normalize v (Z v))).card : ℝ) * (δ * Z v)
      = ∑ _i ∈ active δ (DARM.Boundary.normalize v (Z v)), (δ * Z v) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ active δ (DARM.Boundary.normalize v (Z v)), v i :=
        Finset.sum_le_sum key

/-- **Sharp capacity bound.** If the post-normalization active set is not the
    whole index type, then `|S| * δ < 1` strictly.

    The slack comes from the coordinate outside `S`: it carries positive mass
    that the active set does not, so the active set's share falls strictly
    below the total.

    This closes the necessity half of R1b. A target `B` that is a proper
    subset of the index type and satisfies `δ * |B| = 1` is NOT reachable —
    the conjectured threshold is strict, not weak. -/
theorem active_card_strict_lt_of_ne_univ
    {ι : Type*} [Fintype ι] (δ : ℝ) (v : ι → ℝ)
    (hv : ∀ i, 0 < v i) (hZ : 0 < Z v)
    (hne : active δ (DARM.Boundary.normalize v (Z v)) ≠ Finset.univ) :
    ((active δ (DARM.Boundary.normalize v (Z v))).card : ℝ) * δ < 1 := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ active δ (DARM.Boundary.normalize v (Z v)) := by
    by_contra h
    push_neg at h
    exact hne (Finset.eq_univ_of_forall h)
  have h1 := card_mul_le_sum δ v hZ
  -- the coordinate outside the active set carries mass the active set does not
  have h2 : ∑ i ∈ active δ (DARM.Boundary.normalize v (Z v)), v i < Z v := by
    simp only [Z]
    exact Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ j) hj
      (hv j) (fun k _ _ => (hv k).le)
  have h3 : ((active δ (DARM.Boundary.normalize v (Z v))).card : ℝ) * (δ * Z v) < Z v := by
    linarith
  have h4 : (((active δ (DARM.Boundary.normalize v (Z v))).card : ℝ) * δ) * Z v < 1 * Z v := by
    rw [mul_assoc, one_mul]
    exact h3
  exact lt_of_mul_lt_mul_right h4 hZ.le

/-! ## Registered status of R1b

  DONE:
    * The reweighting channel is surjective onto positive vectors, so R1b is a
      question about achievable active sets, not about the expressiveness of
      the update rule.
    * The necessity half is sharp: a proper subset `B` requires `δ * |B| < 1`,
      strictly. The weak inequality `δ * |B| ≤ 1` is attainable only when
      `B` is the whole index type.

  OPEN:
    * Sufficiency. Given `δ * |B| < 1` and `B` nonempty, construct a witness
      realizing exactly `B`. Needs an explicit `ε` and a cardinality
      computation. Combined with surjectivity above, a witness at the level of
      weight vectors immediately yields one at the level of `loss`.

  NOT AN AGENT RESULT, still. `loss` remains a universally quantified
  parameter; there is no actor in the model. Surjectivity says the channel
  imposes no constraint, not that anything chooses to exploit it.
-/

end ReachabilityExact
end DARM

#print axioms DARM.ReachabilityExact.reweight_surjective_on_positive
#print axioms DARM.ReachabilityExact.active_card_strict_lt_of_ne_univ
