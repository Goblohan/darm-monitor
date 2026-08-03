import DarmMonitor.ActiveSurrogate

/-
  ExpEvaluator — computable bounds on the reweighting step, closing the gap
  between the refinement architecture and a monitor that can actually run.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT WAS MISSING. `ActiveSurrogate.refinement_quantified` takes conservative
  fixed-point bounds on the post-update weights as HYPOTHESES. Producing them
  means bounding

      reweight η loss w i = w i * Real.exp (-η * loss i)

  in both directions, computably, with proved error. Without that the
  architecture is sound but inert.

  THE BRACKET. Write `a = η * loss i`, so the exponent is `-a`. Both bounds come
  from a single Mathlib fact, `Real.add_one_le_exp : x + 1 ≤ exp x`:

      LOWER:  1 - a ≤ exp (-a)              for all a
      UPPER:  exp (-a) ≤ 1 / (1 + a)        for a > -1

  The upper bound needs no series expansion and no case analysis:
  `exp (-a) * (1 + a) ≤ exp (-a) * exp a = exp 0 = 1`, then divide by
  `1 + a > 0`. An earlier plan used `exp_bound_div_one_sub_of_interval` with a
  two-case split on the sign of `a`; that is unnecessary.

  THE DOMAIN RESTRICTION IS REAL AND MUST BE STATED. The upper bound requires
  `η * loss i > -1`. Outside that region this evaluator produces nothing, and a
  monitor built on it must refuse to certify rather than compute — fail-closed,
  consistently with the rest of the refinement. So the deliverable is a monitor
  sound ON A STATED DOMAIN, not an unrestricted one.

  ROUNDING DIRECTIONS. Each bound is then rounded into fixed point in the
  direction that preserves conservatism:
    * `expLoFx` uses an UPPER bound on `a`, since `1 - a` decreases in `a`
    * `expHiFx` uses a LOWER bound on `a`, since `1/(1+a)` decreases in `a`
  This is the interval structure from `ActiveSurrogate` appearing again: each
  real quantity is bracketed, and which end feeds which computation is forced
  by the monotonicity, not chosen.
-/

namespace DARM
namespace ExpEvaluator

open DARM.Boundary DARM.FixedPoint DARM.ActiveSurrogate

/-! ## 1. Additional fixed-point arithmetic

  `FixedPoint` supplies exact addition and upward multiplication. The evaluator
  also needs subtraction, downward multiplication, and upward division. -/

/-- Subtraction. Exact, like addition. -/
def Fixed.sub (x y : Fixed) : Fixed := ⟨x.raw - y.raw⟩

theorem gamma_sub (x y : Fixed) : γ (Fixed.sub x y) = γ x - γ y := by
  unfold γ Fixed.sub
  push_cast
  ring

/-- Multiplication rounding DOWN. Used where the result is a lower bound. -/
def Fixed.mulDown (x y : Fixed) : Fixed :=
  ⟨(x.raw * y.raw) / (2 ^ k)⟩

/-- **The downward product under-approximates.** Mirror of `gamma_mulUp_ge`. -/
theorem gamma_mulDown_le (x y : Fixed) : γ (Fixed.mulDown x y) ≤ γ x * γ y := by
  have hb : (2 ^ k : Int) ≠ 0 := by positivity
  have hM : (0 : ℝ) < (2 ^ k : ℝ) := scale_pos
  have hid := Int.mul_ediv_add_emod (x.raw * y.raw) (2 ^ k)
  have hnn := Int.emod_nonneg (x.raw * y.raw) hb
  have hkey : (2 ^ k : Int) * ((x.raw * y.raw) / (2 ^ k)) ≤ x.raw * y.raw := by
    linarith
  have hcast : (2 ^ k : ℝ) * ((((x.raw * y.raw) / (2 ^ k) : Int)) : ℝ)
      ≤ (x.raw : ℝ) * (y.raw : ℝ) := by exact_mod_cast hkey
  unfold γ Fixed.mulDown
  rw [div_le_iff₀ hM]
  have hsimp : (x.raw : ℝ) / (2 ^ k : ℝ) * ((y.raw : ℝ) / (2 ^ k : ℝ)) * (2 ^ k : ℝ)
      = (x.raw : ℝ) * (y.raw : ℝ) / (2 ^ k : ℝ) := by field_simp
  rw [hsimp, le_div_iff₀ hM]
  linarith

/-- Division rounding UP. Requires a strictly positive divisor. -/
def Fixed.divUp (x y : Fixed) : Fixed :=
  ⟨-((-(x.raw * 2 ^ k)) / y.raw)⟩

/-- **The upward quotient over-approximates.** -/
theorem gamma_divUp_ge (x y : Fixed) (hy : 0 < y.raw) :
    γ x / γ y ≤ γ (Fixed.divUp x y) := by
  have hyne : y.raw ≠ 0 := ne_of_gt hy
  have hM : (0 : ℝ) < (2 ^ k : ℝ) := scale_pos
  have hyR : (0 : ℝ) < (y.raw : ℝ) := by exact_mod_cast hy
  have hid := Int.mul_ediv_add_emod (-(x.raw * 2 ^ k)) y.raw
  have hnn := Int.emod_nonneg (-(x.raw * 2 ^ k)) hyne
  have hkey : (x.raw * 2 ^ k : Int)
      ≤ (-((-(x.raw * 2 ^ k)) / y.raw)) * y.raw := by
    have hcomm : (-((-(x.raw * 2 ^ k)) / y.raw)) * y.raw
        = y.raw * (-((-(x.raw * 2 ^ k)) / y.raw)) := mul_comm _ _
    rw [hcomm]
    linarith
  unfold γ Fixed.divUp
  simp only []
  have hlhs : (x.raw : ℝ) / (2 ^ k : ℝ) / ((y.raw : ℝ) / (2 ^ k : ℝ))
      = (x.raw : ℝ) / (y.raw : ℝ) := by
    field_simp
  rw [hlhs, div_le_div_iff₀ hyR hM]
  exact_mod_cast hkey

/-- Sum over a finite index type. Exact, since addition is. -/
def Fixed.sumOver {ι : Type*} [Fintype ι] (f : ι → Fixed) : Fixed :=
  ⟨∑ i, (f i).raw⟩

theorem gamma_sumOver {ι : Type*} [Fintype ι] (f : ι → Fixed) :
    γ (Fixed.sumOver f) = ∑ i, γ (f i) := by
  unfold γ Fixed.sumOver
  push_cast
  rw [Finset.sum_div]

/-! ## 2. The real bracket on `exp (-a)` -/

/-- **Lower bound, unconditional.** Direct from `add_one_le_exp` at `-a`. -/
theorem exp_neg_lower (a : ℝ) : 1 - a ≤ Real.exp (-a) := by
  have h := Real.add_one_le_exp (-a)
  linarith

/-- **Upper bound on the domain `a > -1`.**

    `exp (-a) * (1 + a) ≤ exp (-a) * exp a = exp 0 = 1`, then divide. No series
    expansion and no case split on the sign of `a`. -/
theorem exp_neg_upper (a : ℝ) (ha : -1 < a) :
    Real.exp (-a) ≤ 1 / (1 + a) := by
  have h1a : (0 : ℝ) < 1 + a := by linarith
  have hpos : (0 : ℝ) < Real.exp (-a) := Real.exp_pos _
  have hle : 1 + a ≤ Real.exp a := by
    have := Real.add_one_le_exp a
    linarith
  have hprod : Real.exp (-a) * (1 + a) ≤ 1 := by
    calc Real.exp (-a) * (1 + a) ≤ Real.exp (-a) * Real.exp a :=
          mul_le_mul_of_nonneg_left hle hpos.le
      _ = Real.exp (-a + a) := (Real.exp_add _ _).symm
      _ = 1 := by simp
  rw [le_div_iff₀ h1a]
  exact hprod

/-! ## 3. Fixed-point bracket

  Note which end of the `a` interval feeds which bound: `1 - a` and `1/(1+a)`
  are both DECREASING in `a`, so the lower bound on `exp (-a)` needs an upper
  bound on `a`, and vice versa. -/

/-- `1.0` in fixed point. -/
def one : Fixed := ⟨2 ^ k⟩

theorem gamma_one : γ one = 1 := by
  unfold γ one
  push_cast
  field_simp

/-- Computable lower bound on `exp (-a)`, from an upper bound on `a`. -/
def expLoFx (aHi : Fixed) : Fixed := Fixed.sub one aHi

/-- Computable upper bound on `exp (-a)`, from a lower bound on `a`.
    The divisor `1 + aLo` must be positive — that is the domain restriction. -/
def expHiFx (aLo : Fixed) : Fixed := Fixed.divUp one (FixedPoint.Fixed.add one aLo)

theorem expLoFx_sound (a : ℝ) (aHi : Fixed) (h : a ≤ γ aHi) :
    γ (expLoFx aHi) ≤ Real.exp (-a) := by
  unfold expLoFx
  rw [gamma_sub, gamma_one]
  have := exp_neg_lower a
  linarith

theorem expHiFx_sound (a : ℝ) (aLo : Fixed)
    (h : γ aLo ≤ a) (hdom : 0 < (FixedPoint.Fixed.add one aLo).raw) :
    Real.exp (-a) ≤ γ (expHiFx aLo) := by
  have hden : γ (FixedPoint.Fixed.add one aLo) = 1 + γ aLo := by
    rw [gamma_add, gamma_one]
  have hdenpos : (0 : ℝ) < 1 + γ aLo := by
    rw [← hden]
    unfold γ
    have : (0:ℝ) < ((FixedPoint.Fixed.add one aLo).raw : ℝ) := by exact_mod_cast hdom
    positivity
  have haneg : -1 < γ aLo := by linarith
  have ha : -1 < a := lt_of_lt_of_le haneg h
  have h1a : (0 : ℝ) < 1 + a := by linarith
  calc Real.exp (-a) ≤ 1 / (1 + a) := exp_neg_upper a ha
    _ ≤ 1 / (1 + γ aLo) := by
        apply one_div_le_one_div_of_le hdenpos
        linarith
    _ = γ one / γ (FixedPoint.Fixed.add one aLo) := by rw [gamma_one, hden]
    _ ≤ γ (expHiFx aLo) := gamma_divUp_ge one _ hdom

/-! ## 4. Bounds on the reweighted coordinate -/

/-- Computable lower bound on `reweight η loss w i`. -/
def wpLoFx (wLo aHi : Fixed) : Fixed := Fixed.mulDown wLo (expLoFx aHi)

/-- Computable upper bound on `reweight η loss w i`. -/
def wpHiFx (wHi aLo : Fixed) : Fixed := FixedPoint.Fixed.mulUp wHi (expHiFx aLo)

theorem wpLoFx_sound (wi a : ℝ) (wLo aHi : Fixed)
    (hw : γ wLo ≤ wi) (hwnn : 0 ≤ γ wLo)
    (ha : a ≤ γ aHi) (hlonn : 0 ≤ γ (expLoFx aHi)) :
    γ (wpLoFx wLo aHi) ≤ wi * Real.exp (-a) := by
  unfold wpLoFx
  calc γ (Fixed.mulDown wLo (expLoFx aHi)) ≤ γ wLo * γ (expLoFx aHi) :=
        gamma_mulDown_le _ _
    _ ≤ wi * Real.exp (-a) := by
        have h1 : γ wLo * γ (expLoFx aHi) ≤ wi * γ (expLoFx aHi) :=
          mul_le_mul_of_nonneg_right hw hlonn
        have h2 : wi * γ (expLoFx aHi) ≤ wi * Real.exp (-a) := by
          apply mul_le_mul_of_nonneg_left (expLoFx_sound a aHi ha)
          linarith
        linarith

theorem wpHiFx_sound (wi a : ℝ) (wHi aLo : Fixed)
    (hw : wi ≤ γ wHi) (hwnn : 0 ≤ wi)
    (ha : γ aLo ≤ a) (hdom : 0 < (FixedPoint.Fixed.add one aLo).raw) :
    wi * Real.exp (-a) ≤ γ (wpHiFx wHi aLo) := by
  unfold wpHiFx
  have hexp := expHiFx_sound a aLo ha hdom
  have hexppos : (0:ℝ) ≤ Real.exp (-a) := (Real.exp_pos _).le
  calc wi * Real.exp (-a) ≤ γ wHi * Real.exp (-a) :=
        mul_le_mul_of_nonneg_right hw hexppos
    _ ≤ γ wHi * γ (expHiFx aLo) := by
        apply mul_le_mul_of_nonneg_left hexp
        linarith
    _ ≤ γ (FixedPoint.Fixed.mulUp wHi (expHiFx aLo)) := gamma_mulUp_ge _ _

/-! ## 5. End to end

  The evaluator's output, assembled and fed to `refinement_quantified`. -/

variable {ι : Type*} [Fintype ι]

/-- The computable upper bound on the partition function. -/
def ZhiFx (wHi aLo : ι → Fixed) : Fixed :=
  Fixed.sumOver (fun i => wpHiFx (wHi i) (aLo i))

/-- **The evaluator is sound.** Given fixed-point brackets on the weights and on
    `η * loss`, with every exponent inside the domain, the computable check
    establishes the real safety certificate.

    This is the statement that makes a running boundary monitor possible: every
    hypothesis is either a bracket the caller can compute or a domain condition
    the caller can check. -/
theorem evaluator_sound
    (δ η : ℝ) (loss w : ι → ℝ)
    (δlo δhi margin : Fixed) (wLo wHi aLo aHi : ι → Fixed)
    (hδlo : γ δlo ≤ δ) (hδhi : δ ≤ γ δhi) (hδnn : 0 ≤ δ)
    (hwnn : ∀ i, 0 ≤ w i)
    (hwHi : ∀ i, w i ≤ γ (wHi i))
    (hwLo : ∀ i, γ (wLo i) ≤ w i) (hwLonn : ∀ i, 0 ≤ γ (wLo i))
    (haLo : ∀ i, γ (aLo i) ≤ η * loss i)
    (haHi : ∀ i, η * loss i ≤ γ (aHi i))
    (hlonn : ∀ i, 0 ≤ γ (expLoFx (aHi i)))
    (hdom : ∀ i, 0 < (FixedPoint.Fixed.add one (aLo i)).raw)
    (hmargin : 0 ≤ γ margin)
    (hcheck : ∀ i ∈ active_fx δlo wHi,
      FixedPoint.checkSafeCoord δhi (ZhiFx wHi aLo) (wpLoFx (wLo i) (aHi i)) margin = true) :
    is_safe_signal_Z δ η loss w := by
  have hrw : ∀ i, reweight η loss w i = w i * Real.exp (-(η * loss i)) := by
    intro i
    unfold reweight
    ring_nf
  -- lower bounds on each reweighted coordinate
  have hwpLo : ∀ i, γ (wpLoFx (wLo i) (aHi i)) ≤ reweight η loss w i := by
    intro i
    rw [hrw i]
    exact wpLoFx_sound (w i) (η * loss i) (wLo i) (aHi i)
      (hwLo i) (hwLonn i) (haHi i) (hlonn i)
  -- upper bound on the partition function
  have hZhi : Z (reweight η loss w) ≤ γ (ZhiFx wHi aLo) := by
    unfold Z ZhiFx
    rw [gamma_sumOver]
    apply Finset.sum_le_sum
    intro i _
    rw [hrw i]
    exact wpHiFx_sound (w i) (η * loss i) (wHi i) (aLo i)
      (hwHi i) (hwnn i) (haLo i) (hdom i)
  have hZnn : 0 ≤ Z (reweight η loss w) := by
    unfold Z
    apply Finset.sum_nonneg
    intro i _
    rw [hrw i]
    exact mul_nonneg (hwnn i) (Real.exp_pos _).le
  exact refinement_quantified δ η loss w δlo δhi (ZhiFx wHi aLo) margin wHi
    (fun i => wpLoFx (wLo i) (aHi i))
    hδlo hδhi hδnn hZnn hZhi hwHi hwpLo hmargin hcheck

/-! ## 6. It runs -/

/-- `0.5` in fixed point. -/
def halfFx : Fixed := ⟨2 ^ k / 2⟩

-- exp(-0.5) ≈ 0.6065.  Bracket: [1 - 0.5, 1/(1 + 0.5)] = [0.5, 0.667].
#eval (expLoFx halfFx).raw * 1000 / 2 ^ k    -- ≈ 500
#eval (expHiFx halfFx).raw * 1000 / 2 ^ k    -- ≈ 667

-- true value is 0.6065, so the bracket [0.500, 0.666] contains it, loosely

/-! ## Registered status

  DONE: the evaluator exists and is proved sound end to end. `evaluator_sound`
  reduces the real certificate `is_safe_signal_Z` to a computable check plus
  brackets the caller supplies.

  THE DOMAIN RESTRICTION, restated because it bounds the claim. The upper bound
  needs `η * loss i > -1` for every coordinate, entering as `hdom`. Outside that
  region the evaluator gives nothing and a monitor must refuse to certify. This
  is a real limitation, not a formality: a large positive loss with a large `η`
  leaves the domain. Sharper bounds — series truncation with a proved remainder
  — would widen it, at the cost of the factorial arithmetic this construction
  was built to avoid.

  ALSO: the bracket `[1-a, 1/(1+a)]` is loose. At `a = 0.5` it spans
  `[0.500, 0.667]` around a true value of `0.6065`, roughly ±14%. A monitor
  using it will reject safe states well inside the margin. Tightening is a
  numerical-analysis problem, not a soundness one.

  STILL OPEN: the `Int64` port, and the FFI boundary whose glue is hand-written.
-/

end ExpEvaluator
end DARM

#print axioms DARM.ExpEvaluator.gamma_mulDown_le
#print axioms DARM.ExpEvaluator.gamma_divUp_ge
#print axioms DARM.ExpEvaluator.exp_neg_upper
#print axioms DARM.ExpEvaluator.expHiFx_sound
#print axioms DARM.ExpEvaluator.evaluator_sound
