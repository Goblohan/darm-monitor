import DarmMonitor.BoundaryCore
import DarmMonitor.EvaluatorTower

/-
  RationalInstance — a second update rule through the whole chain, to test
  whether the abstraction in `BoundaryCore` is real.

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`.

  WHY. `BoundaryCore` shows the boundary theorems do not mention the update
  rule. That is a claim about the proofs. Whether a DIFFERENT update actually
  works end to end — through the fixed-point layer, the active-set surrogate and
  the quantified certificate — is a separate question, and the way to answer it
  is to instantiate one.

  THE RULE.

      ratReweight η loss w i = w i / (1 + η * loss i)

  Rational, so it evaluates exactly in fixed point: two directed divisions and
  nothing else. No bracket, no tower, no precision parameter `n`.

  A DISTINCTION THAT MATTERS. This is NOT a better approximation of
  `exp (-η * loss)`. It is a different update rule whose values happen to be
  computable. At `a = 0.5`, `exp (-a) = 0.6065` while `1/(1+a) = 0.6667`. The
  gain is not accuracy against `exp`; it is that there is nothing left to
  approximate.

  WHAT IT COSTS, both proved in `BoundaryCore`:
    * it does not compose — `rational_not_semigroup`, so a loss stream's
      chunking changes the result;
    * it is not globally positive — `ratUpdate_neg_below`, so the domain
      `η * loss i > -1` is a precondition rather than a convenience.

  So this instance is for deployments with non-negative losses that do not need
  history independence. `exp` remains primary. The point of building it is that
  the abstraction now has two instances rather than one, which is the difference
  between a general theorem and a rename.
-/

namespace DARM
namespace RationalInstance

open DARM.Boundary DARM.BoundaryCore DARM.FixedPoint DARM.ExpEvaluator
open DARM.ActiveSurrogate

/-! ## 1. The update -/

/-- Rational reweighting. Defined for all inputs; meaningful where
    `1 + η * loss i > 0`. -/
noncomputable def ratReweight (η : ℝ) (loss w : ι → ℝ) : ι → ℝ :=
  fun i => w i / (1 + η * loss i)

/-- Positive wherever the weight is positive and the exponent is above `-1`. -/
theorem ratReweight_pos {ι : Type*} (η : ℝ) (loss w : ι → ℝ) (i : ι)
    (hw : 0 < w i) (hdom : -1 < η * loss i) :
    0 < ratReweight η loss w i := by
  unfold ratReweight
  apply div_pos hw
  linarith

/-! ## 2. The boundary theorems apply, unchanged

  These are `BoundaryCore` results with `w' := ratReweight η loss w`. No new
  proof content — which is the whole claim. -/

variable {ι : Type*} [Fintype ι]

theorem rat_safeZ_iff_safePost (δ η : ℝ) (loss w : ι → ℝ)
    (hZ : 0 < Z (ratReweight η loss w)) :
    SafeZ δ w (ratReweight η loss w) ↔ SafePost δ w (ratReweight η loss w) :=
  safeZ_iff_safePost δ w (ratReweight η loss w) hZ

theorem rat_transport (δ η : ℝ) (loss w : ι → ℝ)
    (hZ : 0 < Z (ratReweight η loss w))
    (hsafe : SafeZ δ w (ratReweight η loss w)) :
    active δ w ⊆ active δ (DARM.Boundary.normalize (ratReweight η loss w)
      (Z (ratReweight η loss w))) :=
  transport_gen δ w (ratReweight η loss w) hZ hsafe

/-! ## 3. Exact fixed-point evaluation

  `ExpEvaluator` supplies `Fixed.divUp`. The downward companion is needed for
  the lower bound. -/

/-- Division rounding DOWN. Requires a strictly positive divisor. -/
def Fixed.divDown (x y : Fixed) : Fixed :=
  ⟨(x.raw * 2 ^ k) / y.raw⟩

theorem gamma_divDown_le (x y : Fixed) (hy : 0 < y.raw) :
    γ (Fixed.divDown x y) ≤ γ x / γ y := by
  have hyne : y.raw ≠ 0 := ne_of_gt hy
  have hM : (0 : ℝ) < (2 ^ k : ℝ) := scale_pos
  have hyR : (0 : ℝ) < (y.raw : ℝ) := by exact_mod_cast hy
  have hid := Int.mul_ediv_add_emod (x.raw * 2 ^ k) y.raw
  have hnn := Int.emod_nonneg (x.raw * 2 ^ k) hyne
  have hkey : ((x.raw * 2 ^ k) / y.raw) * y.raw ≤ x.raw * 2 ^ k := by
    have hcomm : ((x.raw * 2 ^ k) / y.raw) * y.raw
        = y.raw * ((x.raw * 2 ^ k) / y.raw) := mul_comm _ _
    rw [hcomm]
    linarith
  unfold γ Fixed.divDown
  have hrhs : (x.raw : ℝ) / (2 ^ k : ℝ) / ((y.raw : ℝ) / (2 ^ k : ℝ))
      = (x.raw : ℝ) / (y.raw : ℝ) := by field_simp
  rw [hrhs, div_le_div_iff₀ hM hyR]
  exact_mod_cast hkey

/-! ## 4. Directed bounds on the rational update

  `w / (1 + a)` increases in `w` and decreases in `a`, so the lower bound takes
  the low weight with the HIGH exponent, and the upper bound the reverse. Both
  are single divisions — nothing is bracketed. -/

def ratLoFx (wLo aHi : Fixed) : Fixed :=
  Fixed.divDown wLo (FixedPoint.Fixed.add ExpEvaluator.one aHi)

def ratHiFx (wHi aLo : Fixed) : Fixed :=
  ExpEvaluator.Fixed.divUp wHi (FixedPoint.Fixed.add ExpEvaluator.one aLo)

/-- Note `hwnn`: a lower bound that could be negative would not survive
    multiplication by the denominator gap. The hypothesis is real, not
    bookkeeping — weights are non-negative in every instance, but the fixed-point
    lower bound has to be too. -/
theorem ratLoFx_sound (wi a : ℝ) (wLo aHi : Fixed)
    (hw : γ wLo ≤ wi) (hwnn : 0 ≤ γ wLo) (ha : a ≤ γ aHi)
    (hdom : 0 < (FixedPoint.Fixed.add ExpEvaluator.one aHi).raw)
    (hapos : 0 < 1 + a) :
    γ (ratLoFx wLo aHi) ≤ wi / (1 + a) := by
  have hden : γ (FixedPoint.Fixed.add ExpEvaluator.one aHi) = 1 + γ aHi := by
    rw [gamma_add, ExpEvaluator.gamma_one]
  have hdenpos : (0 : ℝ) < 1 + γ aHi := by
    rw [← hden]
    unfold γ
    have : (0:ℝ) < ((FixedPoint.Fixed.add ExpEvaluator.one aHi).raw : ℝ) := by
      exact_mod_cast hdom
    positivity
  calc γ (ratLoFx wLo aHi)
      ≤ γ wLo / γ (FixedPoint.Fixed.add ExpEvaluator.one aHi) :=
        gamma_divDown_le wLo _ hdom
    _ = γ wLo / (1 + γ aHi) := by rw [hden]
    _ ≤ wi / (1 + a) := by
        rw [div_le_div_iff₀ hdenpos hapos]
        nlinarith

theorem ratHiFx_sound (wi a : ℝ) (wHi aLo : Fixed)
    (hw : wi ≤ γ wHi) (hwnn : 0 ≤ wi) (ha : γ aLo ≤ a)
    (hdom : 0 < (FixedPoint.Fixed.add ExpEvaluator.one aLo).raw) :
    wi / (1 + a) ≤ γ (ratHiFx wHi aLo) := by
  have hden : γ (FixedPoint.Fixed.add ExpEvaluator.one aLo) = 1 + γ aLo := by
    rw [gamma_add, ExpEvaluator.gamma_one]
  have hdenpos : (0 : ℝ) < 1 + γ aLo := by
    rw [← hden]
    unfold γ
    have : (0:ℝ) < ((FixedPoint.Fixed.add ExpEvaluator.one aLo).raw : ℝ) := by
      exact_mod_cast hdom
    positivity
  have hapos : (0:ℝ) < 1 + a := by linarith
  calc wi / (1 + a) ≤ γ wHi / (1 + γ aLo) := by
        rw [div_le_div_iff₀ hapos hdenpos]
        nlinarith
    _ = γ wHi / γ (FixedPoint.Fixed.add ExpEvaluator.one aLo) := by rw [hden]
    _ ≤ γ (ratHiFx wHi aLo) := ExpEvaluator.gamma_divUp_ge wHi _ hdom

/-! ## 5. It runs, and the width is one quantum -/

-- a = 0.5 in fixed point
def halfA : Fixed := ⟨2 ^ k / 2⟩
def oneW : Fixed := ⟨2 ^ k⟩

-- exact value 1/(1+0.5) = 0.6667, in thousandths: bounds are 666 and 667
#eval (ratLoFx oneW halfA).raw * 1000 / 2 ^ k
#eval (ratHiFx oneW halfA).raw * 1000 / 2 ^ k

-- the same quantity under the exp instance at n = 0 spans [500, 666];
-- but note it is bracketing exp(-0.5) = 0.6065, a DIFFERENT number
#eval (ExpEvaluator.expLoFx halfA).raw * 1000 / 2 ^ k
#eval (ExpEvaluator.expHiFx halfA).raw * 1000 / 2 ^ k

/-! ## Registered status

  ESTABLISHED. The abstraction has two instances. The boundary theorems apply to
  the rational update with no new proof content — sections 2 above are pure
  applications — and the fixed-point evaluation is two directed divisions with
  no bracketing, no tower and no precision parameter.

  READ THE #eval CAREFULLY. The rational bounds are one quantum apart because
  the value is exactly representable, not because the approximation of `exp`
  improved. The two instances compute different numbers: `1/(1+a) = 0.667`
  against `exp (-a) = 0.6065`. Choosing between them is choosing an update rule,
  not a precision setting.

  WHAT THIS INSTANCE GIVES UP, and it is not small: composition
  (`BoundaryCore.rational_not_semigroup`) and global positivity
  (`BoundaryCore.ratUpdate_neg_below`). Over ℝ no exactly-computable update
  recovers composition — `exp` is the unique continuous solution of
  `f(a) * f(b) = f(a + b)` — so this is a forced trade rather than an
  engineering gap.

  NOT DONE. The end-to-end `refinement_quantified` instantiation. Sections 4
  supply the coordinate bounds; assembling them into a partition-function bound
  and feeding the quantified certificate mirrors `evaluator_sound` and is
  mechanical. Left until there is a caller who wants this instance.
-/

end RationalInstance
end DARM

#print axioms DARM.RationalInstance.ratReweight_pos
#print axioms DARM.RationalInstance.rat_safeZ_iff_safePost
#print axioms DARM.RationalInstance.rat_transport
#print axioms DARM.RationalInstance.gamma_divDown_le
#print axioms DARM.RationalInstance.ratLoFx_sound
#print axioms DARM.RationalInstance.ratHiFx_sound
