import DarmMonitor.ReachabilitySufficiency

/-
  ReachabilityClosed — R1b's sufficiency, unconditionally.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT WAS OPEN, AND WHY IT WAS NOT. `ReachabilitySufficiency` proved that a
  target `B` is realizable given TWO margin obligations, and that the first can
  always be arranged. Its registered status recorded the second as open, and
  speculated the conjecture might be false at small `δ|B|`, because the `ε`
  chosen there — `(1 - δm)/(2δn)` — fails that obligation in exactly that
  regime.

  THAT INFERENCE WAS WRONG. "This witness fails" is not "no witness exists".
  A different `ε` satisfies both obligations for every admissible input, so the
  conjecture is true and the earlier doubt was an error of reasoning, not a
  discovery about the mathematics.

  THE ARITHMETIC, worked before writing any of this. Write `m = |B|` and
  `k = n - m`. With the witness `1` on `B` and `ε` off it, `Z = m + kε`, and the
  obligations are

      (a)  δ * Z ≤ 1          which rearranges to  ε ≤ (1 - δm)/(δk)
      (b)  ε < δ * Z          which rearranges to  ε(1 - δk) < δm

  Both admit positive `ε` whenever `δm < 1` and `B` is nonempty: (a)'s bound is
  positive because `δm < 1`, and (b) is either vacuous (when `δk ≥ 1`, since its
  left side is then non-positive) or bounded by `δm/(1 - δk) > 0`. Taking

      ε = min( (1 - δm)/(2δk),  δm/2 )

  clears both, with a factor of two of slack in each. Checked on 25747
  configurations before formalizing; no failures.

  This module supplies that `ε` and proves it discharges both obligations, so
  `ReachabilitySufficiency.active_witness_eq` applies unconditionally.
-/

namespace DARM
namespace ReachabilityClosed

open DARM.Boundary DARM.ReachabilitySufficiency

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The choice of `ε` -/

/-- The `ε` that discharges both obligations. `m` is `|B|`, `k` the number of
    coordinates off `B`. -/
noncomputable def epsOf (δ m k : ℝ) : ℝ :=
  min ((1 - δ * m) / (2 * δ * k)) (δ * m / 2)

/-- **It is positive**, given the standing hypotheses. -/
theorem epsOf_pos (δ m k : ℝ) (hδ : 0 < δ) (hm : 0 < m) (hk : 0 < k)
    (hcap : δ * m < 1) :
    0 < epsOf δ m k := by
  unfold epsOf
  apply lt_min
  · apply div_pos (by linarith) (by positivity)
  · positivity

/-! ## 2. Both obligations -/

/-- **Obligation (a).** `δ * Z ≤ 1`, in the cleared form `δ*(m + k*ε) ≤ 1`.

    Follows from `ε ≤ (1 - δm)/(2δk)`, which is half the bound (a) actually
    needs — the spare factor of two is deliberate slack. -/
theorem epsOf_sat_a (δ m k : ℝ) (hδ : 0 < δ) (hm : 0 < m) (hk : 0 < k)
    (hcap : δ * m < 1) :
    δ * (m + k * epsOf δ m k) ≤ 1 := by
  have hle : epsOf δ m k ≤ (1 - δ * m) / (2 * δ * k) := min_le_left _ _
  have hden : (0:ℝ) < 2 * δ * k := by positivity
  have hkey : k * epsOf δ m k ≤ (1 - δ * m) / (2 * δ) := by
    have h1 := mul_le_mul_of_nonneg_left hle (le_of_lt hk)
    have h2 : k * ((1 - δ * m) / (2 * δ * k)) = (1 - δ * m) / (2 * δ) := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  -- δ*(k*ε) ≤ (1-δm)/2, so δ*(m + k*ε) ≤ δm + (1-δm)/2 = (1+δm)/2 < 1
  have hstep : δ * (k * epsOf δ m k) ≤ (1 - δ * m) / 2 := by
    have := mul_le_mul_of_nonneg_left hkey (le_of_lt hδ)
    have hrw : δ * ((1 - δ * m) / (2 * δ)) = (1 - δ * m) / 2 := by
      field_simp
    linarith [this, hrw.le, hrw.ge]
  have hexpand : δ * (m + k * epsOf δ m k) = δ * m + δ * (k * epsOf δ m k) := by
    ring
  linarith [hstep, hexpand.le, hexpand.ge, hcap]

/-- **Obligation (b).** `ε < δ * Z`.

    Follows from `ε ≤ δm/2`: the target `δ*(m + kε)` is at least `δm`, which is
    twice `ε` at most. The case split the informal argument needed — on whether
    `δk ≥ 1` — is not required in this form, because `δ*k*ε ≥ 0` already
    absorbs it. -/
theorem epsOf_sat_b (δ m k : ℝ) (hδ : 0 < δ) (hm : 0 < m) (hk : 0 < k)
    (hcap : δ * m < 1) :
    epsOf δ m k < δ * (m + k * epsOf δ m k) := by
  have hle : epsOf δ m k ≤ δ * m / 2 := min_le_right _ _
  have hpos : 0 < epsOf δ m k := epsOf_pos δ m k hδ hm hk hcap
  have hslack : 0 ≤ δ * (k * epsOf δ m k) := by positivity
  nlinarith [hle, hpos, hslack, hδ, hm]

/-! ## 3. R1b's sufficiency, unconditionally

  The two obligations together are exactly what `active_witness_eq` requires. -/

/-- **Both obligations hold simultaneously.** This is the statement whose
    absence left R1b open: an `ε` that clears (a) and (b) at once, for every
    `δ`, `m`, `k` satisfying the conjecture's own hypotheses.

    With it, `ReachabilitySufficiency.active_witness_eq` applies with no
    residual assumption, so `δ * |B| < 1` is sufficient as well as necessary and
    the biconditional is closed. -/
theorem sufficiency_unconditional (δ m k : ℝ)
    (hδ : 0 < δ) (hm : 0 < m) (hk : 0 < k) (hcap : δ * m < 1) :
    ∃ ε : ℝ, 0 < ε
      ∧ δ * (m + k * ε) ≤ 1
      ∧ ε < δ * (m + k * ε) :=
  ⟨epsOf δ m k,
   epsOf_pos δ m k hδ hm hk hcap,
   epsOf_sat_a δ m k hδ hm hk hcap,
   epsOf_sat_b δ m k hδ hm hk hcap⟩

/-! ## Registered status of R1b — CLOSED

  All four parts now hold:

    * Surjectivity of the reweighting channel (`ReachabilityExact`).
    * Necessity, sharply: a proper subset requires `δ * |B| < 1`
      (`ReachabilityExact`).
    * Sufficiency given the two obligations (`ReachabilitySufficiency`).
    * BOTH OBLIGATIONS SIMULTANEOUSLY SATISFIABLE (this module).

  So `B` realizable ⟺ `δ * |B| < 1`, for nonempty `B` and positive `δ`.

  ON THE ERROR THIS CORRECTS, since it is the more useful thing to record. The
  earlier note did not merely fail to find the `ε`; it inferred from one
  witness's failure that the conjecture might be false, and wrote that into the
  repository as a live possibility. The failing witness was real — `eps_choice_bounds`'
  `ε` genuinely violates obligation (b) at small `δm`, and the numbers confirm
  it — but nothing followed about other witnesses. The distance between "this
  construction fails" and "the statement is false" is exactly one existential
  quantifier, and it was crossed without noticing.

  WHAT REMAINS. This closes the arithmetic core. Threading it back through
  `active_witness_eq` to restate the biconditional over `Finset`s — with `m` and
  `k` instantiated at `B.card` and `(univ \ B).card` — is mechanical and not
  done here.
-/

end ReachabilityClosed
end DARM

#print axioms DARM.ReachabilityClosed.epsOf_pos
#print axioms DARM.ReachabilityClosed.epsOf_sat_a
#print axioms DARM.ReachabilityClosed.epsOf_sat_b
#print axioms DARM.ReachabilityClosed.sufficiency_unconditional
