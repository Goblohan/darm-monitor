import DarmMonitor.Fixed64Tower

/-
  Fixed64Sub — subtraction over F64.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHY. `ExpEvaluator.expLoFx aHi = Fixed.sub one aHi` — the lower end of the
  exponential bracket is `1 - a`. Porting `expBracket` to F64 needs `sub`, and
  it is the last primitive missing: `mulUp`, `mulDown`, both directed
  divisions, addition and `sumOver` all exist in verified 64-bit form already.

  Exact, like addition. `F64.subI` computes the difference in `Int` and
  converts once via `Int64.ofInt`, so the only obligation is that the result
  lands in range — no wrapping subtraction appears anywhere.
-/

namespace DARM
namespace Fixed64Sub

open DARM.FixedPoint DARM.HardwarePort DARM.Fixed64

/-- Subtraction over F64. Exact in `Int`; one conversion at the end. -/
def F64.subI (x y : F64) : F64 := ⟨Int64.ofInt (x.raw.toInt - y.raw.toInt)⟩

/-- **Subtraction simulates** inside range, mirroring `Fixed64.add_simulates`. -/
theorem sub_simulates (x y : F64)
    (hlo : -(2 ^ 63) ≤ x.raw.toInt - y.raw.toInt)
    (hhi : x.raw.toInt - y.raw.toInt < 2 ^ 63) :
    (F64.subI x y).toFixed = ExpEvaluator.Fixed.sub x.toFixed y.toFixed := by
  unfold F64.subI F64.toFixed ExpEvaluator.Fixed.sub
  congr 1
  exact toInt_ofInt_of_range _ hlo hhi

/-- Both operands in `[0, 1]` puts the difference in `[-1, 1]`, comfortably in
    range — the case `expLoFx` actually uses, so a caller in that regime needs
    no separate range argument. -/
theorem sub_simulates_of_inUnit (x y : F64)
    (hx : Fixed64Tower.InUnit x) (hy : Fixed64Tower.InUnit y) :
    (F64.subI x y).toFixed = ExpEvaluator.Fixed.sub x.toFixed y.toFixed := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  exact sub_simulates x y (by omega) (by omega)

/-! ## It runs -/

-- 1.0 - 0.25 = 0.75, in thousandths: 750
#eval (F64.subI ⟨Int64.ofInt (2 ^ FixedPoint.k)⟩
                ⟨Int64.ofInt (2 ^ FixedPoint.k / 4)⟩).raw.toInt
        * 1000 / 2 ^ FixedPoint.k

/-! ## Registered status

  DONE: subtraction over F64, with both a general range-hypothesis form and the
  specialization to unit-range operands that `expLoFx` needs.

  With this, EVERY primitive `expBracket` requires exists in verified 64-bit
  form. What remains for `ZhiN64` is composition: `expBracket64` from the tower
  plus `expLoFx64`/`expHiFx64`, then `wpHiN64`, then the sum via
  `Fixed64SumOver.sumOver64_toFixed`.
-/

end Fixed64Sub
end DARM

#print axioms DARM.Fixed64Sub.sub_simulates
#print axioms DARM.Fixed64Sub.sub_simulates_of_inUnit
