import DarmMonitor.Fixed64MulDown

/-
  Fixed64Tower — the doubling tower ported to F64.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT THIS IS. `BracketTightening.bracketIter` squares both ends of a bracket
  `n` times, tightening it. Porting it to F64 is the last piece before `ZhiN64`
  and the quantified evaluator over 64-bit values.

  WHY IT IS DIFFERENT FROM EVERYTHING ELSE IN THE PORT. Every previous
  simulation theorem was single-step: one operation, one envelope hypothesis,
  one application of `toInt_ofInt_of_range`. This one is recursive, so the
  envelope must hold not merely at the first squaring but at EVERY squaring —
  and squaring grows magnitude, so that is not automatic.

  THE INVARIANT, derived on paper before writing any of this. Bracket values
  are bounds on `exp(-a)` for `a ≥ 0`, hence lie in `[0, 1]` — raw in
  `[0, 2^32]`. Squaring preserves that: `X ≤ 2^32` gives `X^2 ≤ 2^64`, and
  shifting right by `32` returns at most `2^32`. So `[0, 2^32]` is stable under
  iteration, and since `2^32` is far below the multiplication envelope's
  `2^47`, every step's simulation hypothesis is satisfied for free.

  That stability is the whole content. Without it the induction has no
  hypothesis to carry; with it, each step is an already-proved single-step
  simulation.
-/

namespace DARM
namespace Fixed64Tower

open DARM.FixedPoint DARM.HardwarePort DARM.Fixed64 DARM.Fixed64MulDown

/-! ## 1. The invariant -/

/-- A bracket value is in `[0, 1]`: raw in `[0, 2^32]`. -/
def InUnit (x : F64) : Prop := 0 ≤ x.raw.toInt ∧ x.raw.toInt ≤ 4294967296

/-- Values in the unit range satisfy the multiplication envelope with room to
    spare — `2^32` against `2^47`. -/
theorem inUnit_within_envelope {x : F64} (h : InUnit x) :
    |x.raw.toInt| ≤ 140737488355328 := by
  obtain ⟨h0, h1⟩ := h
  rw [abs_of_nonneg h0]
  omega

/-! ## 2. Squaring preserves the invariant -/

/-- **`mulUp` preserves `[0, 1]`.** `X ≤ 2^32` gives `X^2 ≤ 2^64`, which shifts
    back to at most `2^32`. -/
theorem mulUp_inUnit {x : F64} (h : InUnit x) : InUnit (F64.mulUp x x) := by
  obtain ⟨h0, h1⟩ := h
  have hk : (2 : ℤ) ^ k = 4294967296 := by norm_num [FixedPoint.k]
  have hsq : x.raw.toInt * x.raw.toInt ≤ 18446744073709551616 := by nlinarith
  have hsqnn : 0 ≤ x.raw.toInt * x.raw.toInt := by positivity
  have hb : |x.raw.toInt * x.raw.toInt| ≤ 19807040628566084398385987584 := by
    rw [abs_of_nonneg hsqnn]; omega
  obtain ⟨hlo, hhi⟩ := shifted_in_range _ hb
  unfold InUnit F64.mulUp
  rw [toInt_ofInt_of_range _ hlo hhi]
  rw [hk]
  have hq := Int.mul_ediv_add_emod (-(x.raw.toInt * x.raw.toInt)) 4294967296
  have hm := Int.emod_nonneg (-(x.raw.toInt * x.raw.toInt))
    (by norm_num : (4294967296 : ℤ) ≠ 0)
  have hml := Int.emod_lt_of_pos (-(x.raw.toInt * x.raw.toInt))
    (by norm_num : (0:ℤ) < 4294967296)
  constructor <;> nlinarith [hq, hm, hml, hsq, hsqnn]

/-- **`mulDown` preserves `[0, 1]`.** Same bound, floor instead of ceiling. -/
theorem mulDown_inUnit {x : F64} (h : InUnit x) :
    InUnit (Fixed64MulDown.F64.mulDown x x) := by
  obtain ⟨h0, h1⟩ := h
  have hk : (2 : ℤ) ^ k = 4294967296 := by norm_num [FixedPoint.k]
  have hsq : x.raw.toInt * x.raw.toInt ≤ 18446744073709551616 := by nlinarith
  have hsqnn : 0 ≤ x.raw.toInt * x.raw.toInt := by positivity
  have hb : |x.raw.toInt * x.raw.toInt| ≤ 19807040628566084398385987584 := by
    rw [abs_of_nonneg hsqnn]; omega
  obtain ⟨hlo, hhi⟩ := shifted_down_in_range _ hb
  unfold InUnit Fixed64MulDown.F64.mulDown
  rw [toInt_ofInt_of_range _ hlo hhi]
  rw [hk]
  have hq := Int.mul_ediv_add_emod (x.raw.toInt * x.raw.toInt) 4294967296
  have hm := Int.emod_nonneg (x.raw.toInt * x.raw.toInt)
    (by norm_num : (4294967296 : ℤ) ≠ 0)
  have hml := Int.emod_lt_of_pos (x.raw.toInt * x.raw.toInt)
    (by norm_num : (0:ℤ) < 4294967296)
  constructor <;> nlinarith [hq, hm, hml, hsq, hsqnn]

/-! ## 3. The tower -/

/-- `n` squarings of an F64 bracket pair. Mirrors
    `BracketTightening.bracketIter`. -/
def bracketIter64 : ℕ → F64 × F64 → F64 × F64
  | 0, p => p
  | n + 1, p =>
      bracketIter64 n (Fixed64MulDown.F64.mulDown p.1 p.1, F64.mulUp p.2 p.2)

/-- **The tower agrees with the `Int` model**, given the unit invariant on both
    ends of the starting bracket.

    The induction carries `InUnit` on both components; each step's simulation
    hypothesis then follows from `inUnit_within_envelope` rather than needing
    to be supplied. -/
theorem bracketIter64_toFixed : ∀ (n : ℕ) (p : F64 × F64),
    InUnit p.1 → InUnit p.2 →
    ((bracketIter64 n p).1.toFixed
      = (BracketTightening.bracketIter n (p.1.toFixed, p.2.toFixed)).1
     ∧ (bracketIter64 n p).2.toFixed
      = (BracketTightening.bracketIter n (p.1.toFixed, p.2.toFixed)).2) := by
  intro n
  induction n with
  | zero => intro p _ _; exact ⟨rfl, rfl⟩
  | succ m ih =>
    intro p h1 h2
    have hlo := mulDown_inUnit h1
    have hhi := mulUp_inUnit h2
    have hstep1 : (Fixed64MulDown.F64.mulDown p.1 p.1).toFixed
        = ExpEvaluator.Fixed.mulDown p.1.toFixed p.1.toFixed :=
      mulDown_simulates p.1 p.1 (inUnit_within_envelope h1) (inUnit_within_envelope h1)
    have hstep2 : (F64.mulUp p.2 p.2).toFixed
        = FixedPoint.Fixed.mulUp p.2.toFixed p.2.toFixed :=
      mul_simulates p.2 p.2 (inUnit_within_envelope h2) (inUnit_within_envelope h2)
    have hrec := ih (Fixed64MulDown.F64.mulDown p.1 p.1, F64.mulUp p.2 p.2) hlo hhi
    simp only [bracketIter64, BracketTightening.bracketIter]
    rw [hstep1, hstep2] at hrec
    exact hrec

/-! ## 4. It runs -/

def halfF64' : F64 := ⟨Int64.ofInt (2 ^ FixedPoint.k / 2)⟩

-- (0.5)^2 = 0.25 after one squaring, (0.25)^2 = 0.0625 after two.
#eval (bracketIter64 1 (halfF64', halfF64')).1.raw.toInt * 1000 / 2 ^ FixedPoint.k
#eval (bracketIter64 2 (halfF64', halfF64')).1.raw.toInt * 10000 / 2 ^ FixedPoint.k

/-! ## Registered status

  DONE: the doubling tower over F64, with the unit invariant proved stable
  under both directed squarings and the agreement theorem proved by induction.
  Every arithmetic operation and every structural piece the quantified
  evaluator needs now exists in verified 64-bit form.

  WHAT REMAINS FOR `ZhiN64`: assembling `expBracket64` (this tower applied to
  `expLoFx`/`expHiFx` images), `wpHiN64`, and the sum via
  `Fixed64SumOver.sumOver64_toFixed`. That is composition of proved parts, not
  new mathematics — but "mechanical" has undersold difficulty repeatedly in
  this port, so it is left as its own step rather than claimed here.

  Also unchanged: no `@[extern]` binding, nothing compiled or profiled.
-/

end Fixed64Tower
end DARM

#print axioms DARM.Fixed64Tower.inUnit_within_envelope
#print axioms DARM.Fixed64Tower.mulUp_inUnit
#print axioms DARM.Fixed64Tower.mulDown_inUnit
#print axioms DARM.Fixed64Tower.bracketIter64_toFixed
