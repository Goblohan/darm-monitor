import DarmMonitor.Fixed64

/-
  Fixed64Refinement — F64 connected to the real-number safety certificate.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHY THIS EXISTS. An external review of this repository (2026-08-04) made a
  precise point, sharper than how the gap had been described here before:
  `Fixed64.lean` proves that `F64` arithmetic REFINES `FixedPoint.Fixed`, but no
  evaluator in this repository (`ExpEvaluator`, `EvaluatorTower`,
  `RationalInstance`) runs on `F64`. All of them run on `Fixed`, which wraps the
  boxed, arbitrary-precision `Int`. `Fixed64` was a verified island.

  SCOPE, DELIBERATELY NARROW. This module connects F64 to the certificate for
  ONE COORDINATE — the F64 analogue of `FixedPoint.refinement_coord`. It does
  NOT restate the full quantified `EvaluatorTower.evaluator_sound_tower` over
  F64. That is real remaining work: it needs F64 analogues of `active_fx`,
  `ZhiN`, `wpLoN`, threading the envelope hypotheses through a sum over the
  index type. This module is the load-bearing piece it would be built on, built
  and checked first, deliberately, given how many multi-hypothesis attempts
  went wrong elsewhere in this repository today from being attempted whole.

  THE CONSTRUCTION. `checkSafeCoord64` is defined using `F64.mulUp` — the
  already-proven native widening multiply — for the one operation that has an
  overflow envelope. The subsequent addition and comparison are done via
  `.raw.toInt`, i.e. in the exact `Int` projection, not in wrapping `Int64`
  arithmetic. This is not a weaker check: addition and comparison do not
  overflow the way multiplication does, and `FixedPoint.checkSafeCoord` itself
  compares `.raw` values as `Int`. The one operation genuinely needing hardware
  simulation is the multiply, and that is where `mul_simulates` is used.
-/

namespace DARM
namespace Fixed64Refinement

open DARM.FixedPoint DARM.HardwarePort DARM.Fixed64

/-! ## 1. The F64-native check -/

/-- **The computable certificate, over F64.** Uses the proven native multiply;
    the final comparison is exact `Int` comparison on the `.raw.toInt`
    projections, which cannot overflow. -/
def checkSafeCoord64 (δfx Zfx wfx marginfx : F64) : Bool :=
  decide ((F64.mulUp δfx Zfx).raw.toInt + marginfx.raw.toInt ≤ wfx.raw.toInt)

/-! ## 2. The check agrees with the Int model, inside the envelope -/

/-- **`checkSafeCoord64` agrees with `FixedPoint.checkSafeCoord`** on the
    `.toFixed` images, provided the multiplication envelope holds. This is the
    bridge: everything else about `refinement_coord` transfers for free once
    the check itself is shown equivalent. -/
theorem checkSafeCoord64_eq (δfx Zfx wfx marginfx : F64)
    (hδb : |δfx.raw.toInt| ≤ mulSafeBound) (hZb : |Zfx.raw.toInt| ≤ mulSafeBound) :
    checkSafeCoord64 δfx Zfx wfx marginfx
      = FixedPoint.checkSafeCoord δfx.toFixed Zfx.toFixed wfx.toFixed marginfx.toFixed := by
  have hmul := mul_simulates δfx Zfx hδb hZb
  have hmuleq : (F64.mulUp δfx Zfx).raw.toInt
      = (FixedPoint.Fixed.mulUp δfx.toFixed Zfx.toFixed).raw := by
    have h := congrArg Fixed.raw hmul
    simpa [F64.toFixed] using h
  unfold checkSafeCoord64 FixedPoint.checkSafeCoord
  simp only [F64.toFixed] at hmuleq ⊢
  rw [hmuleq]
  rfl

/-! ## 3. The single-coordinate refinement over F64 -/

/-- **Fail-closed refinement, over `F64`.** If the F64-native check passes,
    the multiplication envelope holds, and the F64 values bound the reals in
    the conservative directions, then the real inequality `δ * Z ≤ w` holds.

    This is `FixedPoint.refinement_coord` transported across `F64.toFixed`. It
    is what "F64 connects to the certificate" concretely means: a caller
    running `checkSafeCoord64` on genuine `Int64` values, inside the proven
    envelope, gets the same real-number guarantee as the `Int`-based evaluator. -/
theorem refinement_coord64
    (δfx Zfx wfx marginfx : F64) (δr Zr wr : ℝ)
    (hδb : |δfx.raw.toInt| ≤ mulSafeBound) (hZb : |Zfx.raw.toInt| ≤ mulSafeBound)
    (hδ : δr ≤ γ δfx.toFixed) (hZ : Zr ≤ γ Zfx.toFixed)
    (hδnn : 0 ≤ δr) (hZnn : 0 ≤ Zr)
    (hw : γ wfx.toFixed ≤ wr)
    (hmargin : 0 ≤ γ marginfx.toFixed)
    (hcheck : checkSafeCoord64 δfx Zfx wfx marginfx = true) :
    δr * Zr ≤ wr := by
  have heq := checkSafeCoord64_eq δfx Zfx wfx marginfx hδb hZb
  rw [heq] at hcheck
  exact refinement_coord δfx.toFixed Zfx.toFixed wfx.toFixed marginfx.toFixed δr Zr wr
    hδ hZ hδnn hZnn hw hmargin hcheck

/-! ## 4. It runs -/

def oneF64 : F64 := ⟨Int64.ofInt (2 ^ FixedPoint.k)⟩
def quarterF64 : F64 := ⟨Int64.ofInt (2 ^ FixedPoint.k / 4)⟩
def halfF64 : F64 := ⟨Int64.ofInt (2 ^ FixedPoint.k / 2)⟩

-- δ = 1/4, Z = 1, w = 1/2:  requirement 1/4 ≤ 1/2, passes.
#eval checkSafeCoord64 quarterF64 oneF64 halfF64 ⟨0⟩

-- δ = 1/2, Z = 1, w = 1/4:  requirement 1/2 ≤ 1/4, fails.
#eval checkSafeCoord64 halfF64 oneF64 quarterF64 ⟨0⟩

/-! ## Registered status

  DONE: `F64` is connected to the real-number certificate for one coordinate,
  via genuine `Int64` values and the proven native multiply. This is the
  concrete answer to "does F64 connect to anything": yes, for the operation
  that carries the overflow envelope, and the connection is proved rather than
  assumed.

  SINCE DONE (see Fixed64ZhiN/Fixed64Evaluator for the quantified version, and Fixed64Sum for why the wrapping concern below was wrong). The concern as recorded at the time was:

    * THE QUANTIFIED VERSION. `EvaluatorTower.evaluator_sound_tower` restated
      over F64 needs F64 analogues of `active_fx` (the surrogate active set),
      `ZhiN` (the summed partition-function bound), and `wpLoN`/`wpHiN`. The
      sum is where a new argument is needed beyond what is proved here: F64
      addition is native `Int64 +`, which WRAPS, and no theorem in this
      repository yet bounds a sum of `F64` values inside `Int64` range. That is
      a real gap, not a restatement of what `HardwarePort.sum_output_fits`
      already proves over `Int` — the F64 version needs the wrapping addition
      itself shown safe, which is a genuinely different theorem.
    * DIVISION IS UNCONNECTED. `divDown_simulates` and `divUp_simulates` are
      proved but nothing here uses them; `checkSafeCoord64` only needs
      multiplication. Connecting `RationalInstance`, which runs on division, is
      separate work of the same shape as this module.
    * ANY NATIVE CODE. Still unchanged from `Fixed64.lean` and `HardwarePort`:
      no `@[extern]` binding, nothing compiled, nothing profiled.
-/

end Fixed64Refinement
end DARM

#print axioms DARM.Fixed64Refinement.checkSafeCoord64_eq
#print axioms DARM.Fixed64Refinement.refinement_coord64
