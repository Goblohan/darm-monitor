import DarmMonitor.Fixed64Sub

/-
  Fixed64Bracket — `expBracket` ported to F64.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT THIS ASSEMBLES. `EvaluatorTower.expBracket n bLo bHi` is
  `bracketIter n (expLoFx bHi, expHiFx bLo)` — build a starting bracket from the
  linear bounds, then square it `n` times. Every ingredient now exists in
  verified 64-bit form, so this is composition rather than new mathematics:
  `sub_simulates` for the lower end, `divUp_simulates` and `add_simulates` for
  the upper, `bracketIter64_toFixed` for the tower.

  ON THE UNIT HYPOTHESES. `bracketIter64_toFixed` needs `InUnit` on both ends of
  the starting bracket. Rather than derive it, this module takes it as a
  hypothesis. That is honest about where it comes from: for the intended use
  the exponent `a` is in `[0, 1]`, so `1 - a` and `1 / (1 + a)` both land in
  `[0, 1]` — but that is a fact about the CALLER's inputs, not something
  provable from the F64 types alone, and stating it as a hypothesis is more
  accurate than manufacturing a derivation of it here.
-/

namespace DARM
namespace Fixed64Bracket

open DARM.FixedPoint DARM.HardwarePort DARM.Fixed64 DARM.Fixed64Refinement
open DARM.Fixed64Sub DARM.Fixed64Tower

/-! ## 1. The linear bounds over F64 -/

/-- Lower end: `1 - a`. Mirrors `ExpEvaluator.expLoFx`. -/
def expLoFx64 (aHi : F64) : F64 := F64.subI oneF64 aHi

/-- Upper end: `1 / (1 + a)`. Mirrors `ExpEvaluator.expHiFx`. -/
def expHiFx64 (aLo : F64) : F64 := F64.divUp oneF64 (F64.addI oneF64 aLo)

theorem expLoFx64_eq (aHi : F64) (hone : InUnit oneF64) (ha : InUnit aHi) :
    (expLoFx64 aHi).toFixed = ExpEvaluator.expLoFx aHi.toFixed := by
  unfold expLoFx64 ExpEvaluator.expLoFx
  rw [sub_simulates_of_inUnit oneF64 aHi hone ha]
  rfl

theorem expHiFx64_eq (aLo : F64)
    (hden : 4294967296 ≤ (F64.addI oneF64 aLo).raw.toInt)
    (hsum_lo : -(2 ^ 63) ≤ oneF64.raw.toInt + aLo.raw.toInt)
    (hsum_hi : oneF64.raw.toInt + aLo.raw.toInt < 2 ^ 63)
    (hwx : -(2 ^ 63) < oneF64.raw.toInt) :
    (expHiFx64 aLo).toFixed = ExpEvaluator.expHiFx aLo.toFixed := by
  unfold expHiFx64 ExpEvaluator.expHiFx
  have hadd := add_simulates oneF64 aLo hsum_lo hsum_hi
  have hdu := divUp_simulates oneF64 (F64.addI oneF64 aLo) hden hwx
  rw [hdu, hadd]
  rfl

/-! ## 2. The bracket -/

/-- `n` squarings of the starting bracket. Mirrors
    `EvaluatorTower.expBracket`. -/
def expBracket64 (n : ℕ) (bLo bHi : F64) : F64 × F64 :=
  bracketIter64 n (expLoFx64 bHi, expHiFx64 bLo)

/-- **The F64 bracket agrees with the `Int` model's bracket.**

    Composition of the two linear-bound agreements with the tower's induction.
    The `InUnit` hypotheses on the starting bracket are what the tower's
    invariant needs; see the header on why they are hypotheses rather than
    derived. -/
theorem expBracket64_toFixed (n : ℕ) (bLo bHi : F64)
    (hone : InUnit oneF64) (hbHi : InUnit bHi)
    (hden : 4294967296 ≤ (F64.addI oneF64 bLo).raw.toInt)
    (hsum_lo : -(2 ^ 63) ≤ oneF64.raw.toInt + bLo.raw.toInt)
    (hsum_hi : oneF64.raw.toInt + bLo.raw.toInt < 2 ^ 63)
    (hwx : -(2 ^ 63) < oneF64.raw.toInt)
    (hlo_unit : InUnit (expLoFx64 bHi)) (hhi_unit : InUnit (expHiFx64 bLo)) :
    (expBracket64 n bLo bHi).1.toFixed
        = (EvaluatorTower.expBracket n bLo.toFixed bHi.toFixed).1
      ∧ (expBracket64 n bLo bHi).2.toFixed
        = (EvaluatorTower.expBracket n bLo.toFixed bHi.toFixed).2 := by
  have hlo := expLoFx64_eq bHi hone hbHi
  have hhi := expHiFx64_eq bLo hden hsum_lo hsum_hi hwx
  have htower := bracketIter64_toFixed n (expLoFx64 bHi, expHiFx64 bLo) hlo_unit hhi_unit
  unfold expBracket64 EvaluatorTower.expBracket
  rw [hlo, hhi] at htower
  exact htower

/-! ## 3. It runs -/

def quarterB : F64 := ⟨Int64.ofInt (2 ^ FixedPoint.k / 4)⟩

-- a = 1/4: linear bounds are 1 - 1/4 = 0.75 and 1/(1+1/4) = 0.8
#eval (expLoFx64 quarterB).raw.toInt * 1000 / 2 ^ FixedPoint.k
#eval (expHiFx64 quarterB).raw.toInt * 1000 / 2 ^ FixedPoint.k

-- after one squaring: 0.5625 and 0.64
#eval (expBracket64 1 quarterB quarterB).1.raw.toInt * 10000 / 2 ^ FixedPoint.k
#eval (expBracket64 1 quarterB quarterB).2.raw.toInt * 10000 / 2 ^ FixedPoint.k

/-! ## Registered status

  DONE: `expBracket` over F64, agreeing with the `Int` model given the unit
  hypotheses the tower's invariant requires.

  WHAT REMAINS FOR `ZhiN64`: `wpHiN64` (one `mulUp` against the bracket's upper
  end) and the sum via `Fixed64SumOver.sumOver64_toFixed`. Both are single
  applications of theorems already proved.
-/

end Fixed64Bracket
end DARM

#print axioms DARM.Fixed64Bracket.expLoFx64_eq
#print axioms DARM.Fixed64Bracket.expHiFx64_eq
#print axioms DARM.Fixed64Bracket.expBracket64_toFixed
