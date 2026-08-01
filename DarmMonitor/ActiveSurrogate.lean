import DarmMonitor.FixedPoint

/-
  ActiveSurrogate — a computable over-approximation of the active set, and the
  quantified fail-closed refinement theorem.

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`.

  WHAT WAS BLOCKING. `FixedPoint.refinement_coord` covers one coordinate.
  `is_safe_signal_Z` quantifies over `active δ w`, which is `noncomputable` —
  it filters on `δ ≤ w i`, a real comparison. So the quantified form could not
  even be STATED against a running program, let alone proved.

  THE SURROGATE. Filter on fixed-point values instead, choosing the rounding so
  the computable set is a SUPERSET of the real one:

      active_fx δlo wHi := univ.filter (fun i => δlo.raw ≤ (wHi i).raw)

  with `γ δlo ≤ δ` and `w i ≤ γ (wHi i)`. Then `δ ≤ w i` forces
  `γ δlo ≤ γ (wHi i)`, so every genuinely active coordinate is caught. The
  monitor may check coordinates that are not really active — wasted work, never
  missed safety.

  EVERY REAL QUANTITY NEEDS TWO BOUNDS, NOT ONE. This is the structural
  consequence, and it is easy to miss. Look at where `δ` occurs:

      ∀ i ∈ active δ w,  δ * Z (reweight η loss w) ≤ reweight η loss w i
                 ↑                ↑
            needs δ DOWN     needs δ UP

  Membership must round `δ` down so the surrogate over-approximates; the safety
  check must round it up so the requirement is over-approximated. One `δfx`
  cannot do both. Likewise the post-update weights: `Z` sums them and needs each
  rounded UP, while the coordinate comparison needs `w' i` rounded DOWN.

  So the architecture is interval arithmetic over integers — a `(lo, hi)` pair
  per real quantity. That is the sound form of what directed rounding was meant
  to provide, and it arrives as a consequence of the inequality directions
  rather than as a design preference.
-/

namespace DARM
namespace ActiveSurrogate

open DARM.Boundary DARM.FixedPoint

variable {ι : Type*} [Fintype ι]

/-! ## 1. Order on the embedding -/

/-- `γ` is order-reflecting: comparing embeddings is comparing raw integers. -/
theorem gamma_le_iff (x y : Fixed) : γ x ≤ γ y ↔ x.raw ≤ y.raw := by
  unfold γ
  rw [div_le_div_iff_of_pos_right FixedPoint.scale_pos]
  exact Int.cast_le

/-! ## 2. The computable surrogate -/

/-- **Computable active set.** Decidable integer comparison, so this generates
    code — unlike `active`, which filters on a real comparison. -/
def active_fx (δlo : Fixed) (wHi : ι → Fixed) : Finset ι :=
  Finset.univ.filter (fun i => δlo.raw ≤ (wHi i).raw)

theorem mem_active_fx (δlo : Fixed) (wHi : ι → Fixed) (i : ι) :
    i ∈ active_fx δlo wHi ↔ δlo.raw ≤ (wHi i).raw := by
  simp [active_fx]

/-- **The surrogate over-approximates.** Every coordinate active in ℝ is caught
    by the computable filter.

    The rounding directions are what make this work: `δ` down, `w` up. Reversing
    either would let a genuinely active coordinate escape the check, which is
    the fail-open failure. -/
theorem active_subset_active_fx
    (δ : ℝ) (w : ι → ℝ) (δlo : Fixed) (wHi : ι → Fixed)
    (hδlo : γ δlo ≤ δ) (hwHi : ∀ i, w i ≤ γ (wHi i)) :
    active δ w ⊆ active_fx δlo wHi := by
  intro i hi
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [mem_active_fx]
  rw [← gamma_le_iff]
  calc γ δlo ≤ δ := hδlo
    _ ≤ w i := hi
    _ ≤ γ (wHi i) := hwHi i

/-! ## 3. The quantified refinement theorem -/

/-- **Fail-closed refinement, quantified.**

    If the computable check passes on every coordinate of the computable active
    set, then the real safety certificate `is_safe_signal_Z` holds.

    This is the statement that licenses running the fixed-point monitor in place
    of the real one. Note the two bounds on `δ`: `δlo` for membership, `δhi` for
    the requirement. -/
theorem refinement_quantified
    (δ η : ℝ) (loss w : ι → ℝ)
    (δlo δhi Zhi margin : Fixed) (wHi wpLo : ι → Fixed)
    (hδlo : γ δlo ≤ δ) (hδhi : δ ≤ γ δhi) (hδnn : 0 ≤ δ)
    (hZnn : 0 ≤ Z (reweight η loss w))
    (hZhi : Z (reweight η loss w) ≤ γ Zhi)
    (hwHi : ∀ i, w i ≤ γ (wHi i))
    (hwpLo : ∀ i, γ (wpLo i) ≤ reweight η loss w i)
    (hmargin : 0 ≤ γ margin)
    (hall : ∀ i ∈ active_fx δlo wHi,
      FixedPoint.checkSafeCoord δhi Zhi (wpLo i) margin = true) :
    is_safe_signal_Z δ η loss w := by
  intro i hi
  have hsub := active_subset_active_fx δ w δlo wHi hδlo hwHi
  have hcheck := hall i (hsub hi)
  exact FixedPoint.refinement_coord δhi Zhi (wpLo i) margin δ
    (Z (reweight η loss w)) (reweight η loss w i)
    hδhi hZhi hδnn hZnn (hwpLo i) hmargin hcheck

/-! ## 4. It runs -/

/-- Three coordinates, threshold `1/4`, weights `1/2`, `1/8`, `1`. -/
def demoWeights : Fin 3 → Fixed
  | 0 => ⟨2 ^ FixedPoint.k / 2⟩
  | 1 => ⟨2 ^ FixedPoint.k / 8⟩
  | 2 => ⟨2 ^ FixedPoint.k⟩

-- coordinates 0 and 2 clear the 1/4 floor; coordinate 1 does not
#eval (active_fx (⟨2 ^ FixedPoint.k / 4⟩ : Fixed) demoWeights).card   -- 2
#eval decide ((0 : Fin 3) ∈ active_fx (⟨2 ^ FixedPoint.k / 4⟩ : Fixed) demoWeights)
#eval decide ((1 : Fin 3) ∈ active_fx (⟨2 ^ FixedPoint.k / 4⟩ : Fixed) demoWeights)

/-! ## Registered status

  DONE: the quantified refinement is stated and proved. A monitor that computes
  `active_fx` and runs `checkSafeCoord` on each member establishes
  `is_safe_signal_Z` for the real system, provided the fixed-point bounds hold
  in the stated directions.

  THE REMAINING GAP, and it is the substantial one. The theorem takes `wpLo` and
  `Zhi` as HYPOTHESES — conservative fixed-point bounds on the post-update
  weights and their sum. Computing them requires bounding

      reweight η loss w i = w i * Real.exp (-η * loss i)

  and `Real.exp` is transcendental. A running monitor needs computable rational
  bounds on `exp` with proved error, in both directions. Mathlib has series
  bounds (`Real.exp_bound`, `Real.add_one_le_exp`) but assembling a fixed-point
  interval evaluator from them, with the error accounted for, is a project in
  itself and is NOT done here.

  So the honest state: the refinement architecture is proved sound end to end,
  and the numerical evaluator that would feed it does not exist. Anyone
  describing this as a running verified boundary monitor would be overstating
  it by exactly that component.

  ALSO OPEN, from `FixedPoint`: the `Int64` port, and the FFI boundary whose
  glue is hand-written and unverified.
-/

end ActiveSurrogate
end DARM

#print axioms DARM.ActiveSurrogate.gamma_le_iff
#print axioms DARM.ActiveSurrogate.active_subset_active_fx
#print axioms DARM.ActiveSurrogate.refinement_quantified
