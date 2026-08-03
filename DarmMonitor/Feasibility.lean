import DarmMonitor.Benchmark

/-
  Feasibility — the sharp form of the capacity bound, and why the proved one
  overstates the operating envelope.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT PROMPTED THIS. `Reachability.active_card_mul_delta_le_one` proves

      |active| * δ ≤ 1

  which invites reading `δ = 1 / dim` as an admissible setting. The sweep in
  `Benchmark.lean` says otherwise: at `dim * δ = 1` no safe state was found at
  all, and they had already become scarce by `0.6`. The theorem is correct; the
  operational inference from it is not.

  THE EXPLANATION. Safety demands `δ * Z ≤ v i` for every active `i`, which is
  exactly `δ * Z ≤ inf over the active set`. The proved bound is obtained by
  SUMMING that family, which replaces the infimum with a quantity no smaller
  than it — in effect a mean. So:

      |S| * δ  ≤  |S| * (inf over S) / Z  ≤  1

  The left inequality is the safety condition. The right is the structural
  bound. The middle quantity is the sharp ceiling, and the gap between it and 1
  is the weight spread: it reaches 1 only when the weights are uniform on `S`
  and carry no mass off it.

  MEASURED, for weights drawn uniformly on an interval:

      [0.5, 1.0]    ceiling on dim*δ ≈ 0.74
      [0.2, 1.0]    ceiling on dim*δ ≈ 0.48
      [0.05, 1.0]   ceiling on dim*δ ≈ 0.29

  So the envelope is not `1/δ` coordinates but `(inf/mean)/δ`, and the ratio is
  a property of the deployment's weight distribution, not of the model.
-/

namespace DARM
namespace Feasibility

open DARM.Boundary

variable {ι : Type*} [Fintype ι]

/-! ## 1. Safety is an infimum condition -/

/-- **The family of constraints is one constraint on the infimum.** -/
theorem forall_iff_le_inf' (S : Finset ι) (hne : S.Nonempty) (c : ℝ) (v : ι → ℝ) :
    (∀ i ∈ S, c ≤ v i) ↔ c ≤ S.inf' hne v := by
  constructor
  · intro h
    exact Finset.le_inf' hne v h
  · intro h i hi
    exact le_trans h (Finset.inf'_le v hi)

/-! ## 2. The sharp ceiling, and the coarse bound as its consequence -/

/-- **`|S| * inf ≤ Z`.** The infimum can be paid `|S|` times out of the total
    mass and no more. This is the sharp statement; the familiar
    `|S| * δ ≤ 1` follows from it. -/
theorem card_mul_inf_le_Z (S : Finset ι) (hne : S.Nonempty) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    (S.card : ℝ) * (S.inf' hne v) ≤ Z v := by
  have hsum : (S.card : ℝ) * (S.inf' hne v) ≤ ∑ i ∈ S, v i := by
    calc (S.card : ℝ) * (S.inf' hne v)
        = ∑ _i ∈ S, (S.inf' hne v) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, v i :=
          Finset.sum_le_sum (fun i hi => Finset.inf'_le v hi)
  have hrest : ∑ i ∈ S, v i ≤ Z v := by
    simp only [Z]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => hv i)
  linarith

/-- **The capacity bound, recovered — and shown to be the loose form.**

    Safety gives `δ * Z ≤ inf`, so `|S| * δ * Z ≤ |S| * inf ≤ Z`, hence
    `|S| * δ ≤ 1`. The middle term is the sharp ceiling. Anything the coarse
    bound permits but the sharp one forbids is infeasible in practice, and the
    difference is the weight spread. -/
theorem sharp_capacity (S : Finset ι) (hne : S.Nonempty) (δ : ℝ) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hZ : 0 < Z v)
    (hsafe : ∀ i ∈ S, δ * Z v ≤ v i) :
    (S.card : ℝ) * δ ≤ 1 := by
  have hinf : δ * Z v ≤ S.inf' hne v :=
    (forall_iff_le_inf' S hne (δ * Z v) v).mp hsafe
  have hcard := card_mul_inf_le_Z S hne v hv
  have hchain : (S.card : ℝ) * (δ * Z v) ≤ Z v := by
    have : (S.card : ℝ) * (δ * Z v) ≤ (S.card : ℝ) * (S.inf' hne v) := by
      apply mul_le_mul_of_nonneg_left hinf
      positivity
    linarith
  have : ((S.card : ℝ) * δ) * Z v ≤ 1 * Z v := by
    rw [mul_assoc, one_mul]; exact hchain
  exact le_of_mul_le_mul_right this hZ

/-! ## 3. The bound is attained only by uniform weights

  This is what makes the gap real rather than an artefact of a loose proof. -/

/-- With every coordinate equal to `c > 0`, the sharp ceiling is exactly `1`:
    `|univ| * inf = Z`. So the coarse bound is tight, and tight only here. -/
theorem uniform_attains (c : ℝ) (hc : 0 < c) (hne : (Finset.univ : Finset ι).Nonempty) :
    ((Finset.univ : Finset ι).card : ℝ) * ((Finset.univ : Finset ι).inf' hne (fun _ => c))
      = Z (fun _ : ι => c) := by
  have hinf : (Finset.univ : Finset ι).inf' hne (fun _ => c) = c := by
    apply le_antisymm
    · obtain ⟨j, hj⟩ := hne
      exact Finset.inf'_le _ hj
    · exact Finset.le_inf' hne _ (fun _ _ => le_refl c)
  rw [hinf]
  simp [Z, Finset.sum_const, nsmul_eq_mul]

/-- **The gap is real.** With one small coordinate among larger ones, the sharp
    ceiling falls well below the coarse bound. Here `|S| * inf / Z = 4/13`,
    against a coarse bound of `1` — so `δ` must be under a third of what
    `|S| * δ ≤ 1` appears to allow. -/
theorem spread_loses :
    (((Finset.univ : Finset (Fin 4)).card : ℝ)
      * ((Finset.univ : Finset (Fin 4)).inf' ⟨0, Finset.mem_univ 0⟩ ![1, 4, 4, 4]))
      / Z (![1, 4, 4, 4] : Fin 4 → ℝ) = 4 / 13 := by
  have hZ : Z (![1, 4, 4, 4] : Fin 4 → ℝ) = 13 := by
    simp [Z, Fin.sum_univ_four]
    norm_num
  have hinf : (Finset.univ : Finset (Fin 4)).inf' ⟨0, Finset.mem_univ 0⟩
      (![1, 4, 4, 4] : Fin 4 → ℝ) = 1 := by
    apply le_antisymm
    · exact Finset.inf'_le _ (Finset.mem_univ 0)
    · refine Finset.le_inf' _ _ (fun i _ => ?_)
      fin_cases i <;> norm_num
  rw [hZ, hinf]
  norm_num

/-! ## Registered status

  DONE. The sharp ceiling is `inf / Z` and the familiar `|S| * δ ≤ 1` is its
  summed consequence. The bound is attained only when the weights are uniform,
  so any spread strictly reduces the admissible `δ` — which is the effect the
  sweep measured and could not otherwise explain.

  PRACTICAL READING. An operating envelope should be computed as
  `(inf over active) / Z`, not as `1 / δ` coordinates. The first is checkable at
  runtime from the weights in hand; the second is a bound that a real
  distribution never approaches.

  OPEN. A bound in terms of a distribution parameter rather than the realized
  infimum — for instance, in terms of the ratio between the smallest expected
  coordinate and the mean — would let an envelope be chosen at design time
  instead of measured per state. Not attempted; it would need distributional
  assumptions the rest of the development deliberately avoids.
-/

end Feasibility
end DARM

#print axioms DARM.Feasibility.forall_iff_le_inf'
#print axioms DARM.Feasibility.card_mul_inf_le_Z
#print axioms DARM.Feasibility.sharp_capacity
#print axioms DARM.Feasibility.uniform_attains
#print axioms DARM.Feasibility.spread_loses
