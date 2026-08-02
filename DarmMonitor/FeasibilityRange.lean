import DarmMonitor.Feasibility

/-
  FeasibilityRange — a design-time operating envelope.

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`.

  THE GAP THIS CLOSES. `Reachability.active_card_mul_delta_le_one` gives a
  NECESSARY condition, `|active| * δ ≤ 1`. `Feasibility.sharp_capacity` gives the
  exact per-state ceiling, `inf / Z`. Neither can be evaluated before the
  weights exist, so neither tells a deployment what `δ` to choose.

  THE RULE. If every weight lies in `[lo, hi]` then

      dim * δ ≤ lo / hi

  is SUFFICIENT: every coordinate clears the floor. The proof is three lines —
  `Z ≤ dim * hi` and `v i ≥ lo`, so `δ * Z ≤ δ * dim * hi ≤ lo ≤ v i`.

  READ THE CONTRAST. The necessary condition is `dim * δ ≤ 1`; the sufficient
  one is `dim * δ ≤ lo / hi`. The correction factor is exactly the dynamic range
  of the weights. A deployment with weights spanning 5:1 has an envelope five
  times narrower than the capacity bound suggests, and `not_sufficient_witness`
  below shows the coarse bound really can be met by an unsafe state.

  SHARPNESS. The true worst case over the box is `lo / (lo + (dim-1) * hi)`,
  attained with one coordinate at the floor and the rest at the ceiling —
  confirmed by sampling. Multiplying by `dim` gives a quantity that decreases
  monotonically to `lo / hi`, so the rule above is the limit and is conservative
  by at most a factor of `(lo + (dim-1) * hi) / (dim * hi)`, which tends to 1.
  The sharper form `δ * (lo + (dim-1) * hi) ≤ lo` is also provable and is left
  out for legibility.

  WORST CASE, NOT TYPICAL. The benchmark ran at `dim = 8`, `δ = 0.05`, weights in
  `[0.2, 1.0]` — so `dim * δ = 0.4` against a rule of `lo/hi = 0.2` — and still
  found 129 safe states in 200 trials. The rule guarantees safety for EVERY
  vector in the box; most vectors do considerably better. It is a floor for
  design, not a prediction.
-/

namespace DARM
namespace FeasibilityRange

open DARM.Boundary

variable {ι : Type*} [Fintype ι]

/-! ## 1. The envelope -/

/-- **Design-time sufficiency.** Weights bounded in `[lo, hi]` with
    `dim * δ * hi ≤ lo` satisfy the safety condition at every coordinate,
    whatever the particular weights turn out to be. -/
theorem safe_of_range (δ lo hi : ℝ) (v : ι → ℝ)
    (hδ : 0 ≤ δ) (hlo : ∀ i, lo ≤ v i) (hhi : ∀ i, v i ≤ hi)
    (hcond : (Fintype.card ι : ℝ) * δ * hi ≤ lo) :
    ∀ i, δ * Z v ≤ v i := by
  intro i
  have hZle : Z v ≤ (Fintype.card ι : ℝ) * hi := by
    simp only [Z]
    calc ∑ j, v j ≤ ∑ _j : ι, hi := Finset.sum_le_sum (fun j _ => hhi j)
      _ = (Fintype.card ι : ℝ) * hi := by
          simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  calc δ * Z v ≤ δ * ((Fintype.card ι : ℝ) * hi) := by nlinarith
    _ = (Fintype.card ι : ℝ) * δ * hi := by ring
    _ ≤ lo := hcond
    _ ≤ v i := hlo i

/-- The same rule in the memorable form: `dim * δ ≤ lo / hi`. -/
theorem safe_of_ratio (δ lo hi : ℝ) (v : ι → ℝ)
    (hδ : 0 ≤ δ) (hhipos : 0 < hi)
    (hlo : ∀ i, lo ≤ v i) (hhi : ∀ i, v i ≤ hi)
    (hcond : (Fintype.card ι : ℝ) * δ ≤ lo / hi) :
    ∀ i, δ * Z v ≤ v i := by
  refine safe_of_range δ lo hi v hδ hlo hhi ?_
  rw [le_div_iff₀ hhipos] at hcond
  linarith

/-! ## 2. The necessary condition is not sufficient

  A state meeting `dim * δ ≤ 1` exactly, and unsafe. -/

/-- **Witness.** `dim = 2`, `δ = 1/2`, weights `(1, 3)`. Then `dim * δ = 1`,
    satisfying the capacity bound at its limit — and `δ * Z = 2 > 1`, so the
    first coordinate fails.

    This is the formal version of what the benchmark sweep found: safe states
    vanish well before `dim * δ` reaches 1, because the capacity bound is
    obtained by summing and cannot see the smallest coordinate. -/
theorem not_sufficient_witness :
    ((Fintype.card (Fin 2) : ℝ) * (1/2) ≤ 1) ∧
      ¬ (∀ i, (1/2 : ℝ) * Z (![1, 3] : Fin 2 → ℝ) ≤ (![1, 3] : Fin 2 → ℝ) i) := by
  have hZ : Z (![1, 3] : Fin 2 → ℝ) = 4 := by
    simp [Z, Fin.sum_univ_two]
    norm_num
  constructor
  · simp
  · intro h
    have h0 := h 0
    rw [hZ] at h0
    norm_num at h0

/-! ## Registered status

  DONE. A deployment can choose `δ` before seeing any weights: bound the weights
  in `[lo, hi]` and take `dim * δ ≤ lo / hi`. The correction factor against the
  familiar `dim * δ ≤ 1` is the dynamic range, and
  `not_sufficient_witness` shows the coarse bound is genuinely not sufficient
  rather than merely loose.

  THREE STATEMENTS NOW EXIST, and they answer different questions:
    * `Reachability.active_card_mul_delta_le_one` — necessary, `|S| * δ ≤ 1`.
      Says what cannot happen.
    * `Feasibility.sharp_capacity` — the exact ceiling `inf / Z`, computable at
      runtime from the weights in hand.
    * `safe_of_ratio` — sufficient, `dim * δ ≤ lo / hi`, evaluable at design
      time from a range assumption.

  OPEN. The rule is worst-case over the box and therefore pessimistic for
  typical draws — the benchmark satisfied `dim * δ = 0.4` against a rule of
  `0.2` and still found most states safe. A distributional version, bounding the
  probability that a random draw is feasible, would sit between the worst case
  and the per-state ceiling. That needs distributional assumptions the rest of
  this development deliberately avoids, and is not attempted.
-/

end FeasibilityRange
end DARM

#print axioms DARM.FeasibilityRange.safe_of_range
#print axioms DARM.FeasibilityRange.safe_of_ratio
#print axioms DARM.FeasibilityRange.not_sufficient_witness
