import DarmMonitor.Fixed64Refinement
import DarmMonitor.RationalInstance

/-
  RationalF64 — the rational update connected to F64, reusing
  `Fixed64Refinement`'s multiplication bridge unchanged.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHY THIS IS SMALLER THAN IT LOOKS. `checkSafeCoord64` and `refinement_coord64`
  in `Fixed64Refinement.lean` are already generic in what `wfx : F64` represents
  — nothing about them is specific to the exponential update. What differs
  between `ExpEvaluator` and `RationalInstance` is only how the coordinate bound
  `wfx` is COMPUTED: one uses a bracket on `exp`, the other a single division.

  So connecting `RationalInstance` does not need a new check function. It needs
  an F64-native computation of the rational bound (`ratLoFx64`/`ratHiFx64`,
  using the already-proven `F64.divDown`/`F64.divUp`), proved to agree with
  `RationalInstance.ratLoFx`/`ratHiFx` on the `.toFixed` image. That result then
  feeds directly into the unchanged `checkSafeCoord64` and `refinement_coord64`.
-/

namespace DARM
namespace RationalF64

open DARM.FixedPoint DARM.HardwarePort DARM.Fixed64 DARM.Fixed64Refinement
open DARM.RationalInstance DARM.ExpEvaluator

/-! ## 1. F64-native rational bounds

  Mirrors `RationalInstance.ratLoFx`/`ratHiFx`: the denominator is `1 + a`, the
  lower bound divides down, the upper bound divides up. -/

def ratLoFx64 (wLo aHi : F64) : F64 :=
  F64.divDown wLo (F64.addI oneF64 aHi)

def ratHiFx64 (wHi aLo : F64) : F64 :=
  F64.divUp wHi (F64.addI oneF64 aLo)

/-! ## 2. Agreement with the Int model -/

/-- **`ratLoFx64` agrees with `ratLoFx`** on the `.toFixed` images, given the
    divisor condition and that the denominator sum stays in range. -/
theorem ratLoFx64_eq (wLo aHi : F64)
    (hden : (2:ℤ) ^ 32 ≤ (F64.addI oneF64 aHi).raw.toInt)
    (hsum_lo : -(2^63) ≤ oneF64.raw.toInt + aHi.raw.toInt)
    (hsum_hi : oneF64.raw.toInt + aHi.raw.toInt < 2^63) :
    (ratLoFx64 wLo aHi).toFixed = ratLoFx wLo.toFixed aHi.toFixed := by
  have hadd := add_simulates oneF64 aHi hsum_lo hsum_hi
  unfold ratLoFx64 ratLoFx
  have hdd := divDown_simulates wLo (F64.addI oneF64 aHi) hden
  rw [hdd, hadd]
  rfl

/-- **`ratHiFx64` agrees with `ratHiFx`** on the `.toFixed` images, given the
    divisor condition, the sum staying in range, and the two's-complement
    exclusion `divUp_simulates` needs. -/
theorem ratHiFx64_eq (wHi aLo : F64)
    (hden : (2:ℤ) ^ 32 ≤ (F64.addI oneF64 aLo).raw.toInt)
    (hsum_lo : -(2^63) ≤ oneF64.raw.toInt + aLo.raw.toInt)
    (hsum_hi : oneF64.raw.toInt + aLo.raw.toInt < 2^63)
    (hwx : -(2^63) < wHi.raw.toInt) :
    (ratHiFx64 wHi aLo).toFixed = ratHiFx wHi.toFixed aLo.toFixed := by
  have hadd := add_simulates oneF64 aLo hsum_lo hsum_hi
  unfold ratHiFx64 ratHiFx
  have hdu := divUp_simulates wHi (F64.addI oneF64 aLo) hden hwx
  rw [hdu, hadd]
  rfl

/-! ## 3. Soundness, over F64 -/

/-- **Lower bound, over F64.** Combines `ratLoFx64_eq` with the already-proved
    `RationalInstance.ratLoFx_sound`. -/
theorem ratLoFx64_sound (wi a : ℝ) (wLo aHi : F64)
    (hw : γ wLo.toFixed ≤ wi) (hwnn : 0 ≤ γ wLo.toFixed) (ha : a ≤ γ aHi.toFixed)
    (hden : (2:ℤ) ^ 32 ≤ (F64.addI oneF64 aHi).raw.toInt)
    (hsum_lo : -(2^63) ≤ oneF64.raw.toInt + aHi.raw.toInt)
    (hsum_hi : oneF64.raw.toInt + aHi.raw.toInt < 2^63)
    (hdom : 0 < (FixedPoint.Fixed.add ExpEvaluator.one aHi.toFixed).raw)
    (hapos : 0 < 1 + a) :
    γ (ratLoFx64 wLo aHi).toFixed ≤ wi / (1 + a) := by
  rw [ratLoFx64_eq wLo aHi hden hsum_lo hsum_hi]
  exact ratLoFx_sound wi a wLo.toFixed aHi.toFixed hw hwnn ha hdom hapos

/-- **Upper bound, over F64.** -/
theorem ratHiFx64_sound (wi a : ℝ) (wHi aLo : F64)
    (hw : wi ≤ γ wHi.toFixed) (hwnn : 0 ≤ wi) (ha : γ aLo.toFixed ≤ a)
    (hden : (2:ℤ) ^ 32 ≤ (F64.addI oneF64 aLo).raw.toInt)
    (hsum_lo : -(2^63) ≤ oneF64.raw.toInt + aLo.raw.toInt)
    (hsum_hi : oneF64.raw.toInt + aLo.raw.toInt < 2^63)
    (hwx : -(2^63) < wHi.raw.toInt)
    (hdom : 0 < (FixedPoint.Fixed.add ExpEvaluator.one aLo.toFixed).raw) :
    wi / (1 + a) ≤ γ (ratHiFx64 wHi aLo).toFixed := by
  rw [ratHiFx64_eq wHi aLo hden hsum_lo hsum_hi hwx]
  exact ratHiFx_sound wi a wHi.toFixed aLo.toFixed hw hwnn ha hdom

/-! ## 4. It runs -/

def quarterF64 : F64 := ⟨Int64.ofInt (2 ^ FixedPoint.k / 4)⟩

-- a = 1/4: exact value 1/(1+1/4) = 0.8, ratHiFx64 should read close to 800
#eval (ratHiFx64 oneF64 quarterF64).raw.toInt * 1000 / 2 ^ FixedPoint.k
#eval (ratLoFx64 oneF64 quarterF64).raw.toInt * 1000 / 2 ^ FixedPoint.k

/-! ## Registered status

  DONE: `RationalInstance`'s coordinate bounds computed natively on `Int64`,
  proved to agree with the `Int`-model versions, using `divDown_simulates` and
  `divUp_simulates` unchanged. Reuses `Fixed64Refinement`'s `checkSafeCoord64`
  and `refinement_coord64` without modification — confirming those were
  genuinely generic, not accidentally specific to the exponential update.

  Both instances of the boundary abstraction now have a 64-bit path for their
  coordinate computation, at the single-coordinate scope
  `Fixed64Refinement` established.

  NOT DONE, unchanged from before: the quantified sum bound against `Int64`
  wraparound, and any `@[extern]` binding or compiled code.
-/

end RationalF64
end DARM

#print axioms DARM.RationalF64.ratLoFx64_eq
#print axioms DARM.RationalF64.ratHiFx64_eq
#print axioms DARM.RationalF64.ratLoFx64_sound
#print axioms DARM.RationalF64.ratHiFx64_sound
