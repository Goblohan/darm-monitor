import DarmMonitor.Fixed64SumOver

/-
  Fixed64MulDown — the downward multiply over F64.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHY SEPARATELY. `Fixed64.lean` proves `mulUp`, both directed divisions, and
  addition. It does not have `mulDown`, because nothing needed it until now.
  `BracketTightening.bracketIter` squares BOTH ends of a bracket — the lower
  end with `mulDown`, the upper with `mulUp` — so porting the doubling tower to
  F64 needs this first.

  Written as its own module and checked before the tower, deliberately. The
  tower is a recursive induction that must thread an envelope invariant through
  every squaring; attempting it in the same sitting as a new primitive is the
  pattern that cost eight rounds on `Fixed64Sum`.

  THE BOUND. Mirrors `Fixed64.shifted_in_range`, without the negation. Given
  `|a| ≤ 2^94`, floor division by `2^32` yields `|a / 2^32| ≤ 2^62`, comfortably
  inside `Int64` at both ends — a full binary order of slack, which is why this
  one needs no boundary exclusion of the kind `divUp` did.
-/

namespace DARM
namespace Fixed64MulDown

open DARM.FixedPoint DARM.HardwarePort DARM.Fixed64

/-! ## 1. The shifted-down range bound -/

/-- **The downward-shifted product stays in `Int64` range.** No boundary case:
    `2^94 / 2^32 = 2^62`, a full order below `2^63` at both ends. -/
theorem shifted_down_in_range (a : ℤ)
    (hbound : |a| ≤ 19807040628566084398385987584) :
    -(2 ^ 63) ≤ a / (2 ^ k) ∧ a / (2 ^ k) < 2 ^ 63 := by
  have hk : (2 : ℤ) ^ k = 4294967296 := by norm_num [FixedPoint.k]
  rw [hk]
  rw [abs_le] at hbound
  obtain ⟨hb1, hb2⟩ := hbound
  have hq := Int.mul_ediv_add_emod a 4294967296
  have hm := Int.emod_nonneg a (by norm_num : (4294967296 : ℤ) ≠ 0)
  have hml := Int.emod_lt_of_pos a (by norm_num : (0:ℤ) < 4294967296)
  constructor <;> nlinarith [hq, hm, hml, hb1, hb2]

/-! ## 2. The operation -/

/-- 64-bit fixed-point multiplication, rounding the result DOWN. Mirrors
    `ExpEvaluator.Fixed.mulDown`. -/
def F64.mulDown (x y : F64) : F64 :=
  ⟨Int64.ofInt ((x.raw.toInt * y.raw.toInt) / (2 ^ k))⟩

/-- **Downward multiplication simulates**, inside the same envelope `mulUp`
    uses. -/
theorem mulDown_simulates (x y : F64)
    (hx : |x.raw.toInt| ≤ 140737488355328) (hy : |y.raw.toInt| ≤ 140737488355328) :
    (F64.mulDown x y).toFixed
      = ExpEvaluator.Fixed.mulDown x.toFixed y.toFixed := by
  unfold F64.mulDown F64.toFixed ExpEvaluator.Fixed.mulDown
  congr 1
  have hb : |x.raw.toInt * y.raw.toInt| ≤ 19807040628566084398385987584 := by
    rw [abs_mul]
    calc |x.raw.toInt| * |y.raw.toInt|
        ≤ 140737488355328 * 140737488355328 := by
          apply mul_le_mul hx hy (abs_nonneg _) (by norm_num)
      _ ≤ 19807040628566084398385987584 := by norm_num
  obtain ⟨hlo, hhi⟩ := shifted_down_in_range _ hb
  exact toInt_ofInt_of_range _ hlo hhi

/-! ## 3. It runs -/

-- 0.5 * 0.5 = 0.25, in thousandths: 250
#eval (F64.mulDown ⟨Int64.ofInt (2 ^ FixedPoint.k / 2)⟩
                   ⟨Int64.ofInt (2 ^ FixedPoint.k / 2)⟩).raw.toInt
        * 1000 / 2 ^ FixedPoint.k

/-! ## Registered status

  DONE: `mulDown` over F64, proved to refine `ExpEvaluator.Fixed.mulDown`
  inside the same envelope `mulUp` uses. With this, every arithmetic operation
  the doubling tower needs exists in verified 64-bit form.

  NEXT, and deliberately not attempted here: `bracketIter` ported to F64. That
  is a recursive induction which must carry an envelope invariant through every
  squaring. The invariant that should make it work, derived on paper before
  writing: bracket values lie in `[0, 1]`, i.e. raw in `[0, 2^32]`, and
  squaring preserves that — `X ≤ 2^32` gives `X^2 ≤ 2^64`, and shifting right
  by 32 returns at most `2^32`. So the envelope is not merely satisfied at the
  first step but stable under iteration, which is what the induction needs.
-/

end Fixed64MulDown
end DARM

#print axioms DARM.Fixed64MulDown.shifted_down_in_range
#print axioms DARM.Fixed64MulDown.mulDown_simulates
