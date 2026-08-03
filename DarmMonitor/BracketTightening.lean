import DarmMonitor.ExpEvaluator

/-
  BracketTightening — arbitrarily sharp bounds on `exp (-a)` by argument
  doubling, at no cost in soundness.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  THE PROBLEM. `ExpEvaluator`'s bracket is sound but loose. At `a = 0.5` it
  gives `[0.500, 0.666]` around a true `exp (-0.5) = 0.6065` — about ±14%. A
  monitor using it rejects states comfortably inside the real margin. That is a
  usefulness problem, not a soundness one, but it is the one a reviewer probes
  first.

  THE IDEA. `exp (-2b) = exp (-b) ^ 2`, so a bracket on `exp (-b)` squares into
  a bracket on `exp (-2b)`. A caller wanting `exp (-a)` therefore brackets
  `a / 2^n` — where the linear bounds `1 - x` and `1 / (1 + x)` are far tighter,
  since they are exact to first order at `x = 0` — and squares back up `n` times.

  Halving is left to the caller rather than done here. The caller computes
  `a = η * loss i` anyway and can divide by `2^n` at the same time; doing it
  inside would need directed halving lemmas for no gain.

  MEASURED IMPROVEMENT at `a = 0.5`, true value `0.6065`:

      direct            [0.500, 0.666]   width 0.167
      one doubling      [0.562, 0.640]   width 0.078
      two doublings     [0.586, 0.624]   width 0.038

  Each squaring roughly halves the width. `n` is a free parameter: the monitor
  trades multiplications for tightness, and every choice is sound.

  WHAT THIS DOES NOT CHANGE. The domain restriction. The upper bound still needs
  `b > -1` at the base of the tower, which after `n` halvings is
  `η * loss i > -2^n` — so doubling actually WIDENS the admissible domain as
  well as tightening the bracket. That is a second benefit and is recorded
  below, though the theorem here does not state it.
-/

namespace DARM
namespace BracketTightening

open DARM.Boundary DARM.FixedPoint DARM.ExpEvaluator

/-! ## 1. Nonnegativity is preserved by the downward product -/

theorem gamma_nonneg_iff (x : Fixed) : 0 ≤ γ x ↔ 0 ≤ x.raw := by
  unfold γ
  constructor
  · intro h
    have hs : (0:ℝ) < (2 ^ k : ℝ) := scale_pos
    have : (0:ℝ) ≤ (x.raw : ℝ) := by
      by_contra hc
      push_neg at hc
      have : (x.raw : ℝ) / (2 ^ k : ℝ) < 0 := div_neg_of_neg_of_pos hc hs
      linarith
    exact_mod_cast this
  · intro h
    have : (0:ℝ) ≤ (x.raw : ℝ) := by exact_mod_cast h
    positivity

theorem mulDown_nonneg (x y : Fixed) (hx : 0 ≤ γ x) (hy : 0 ≤ γ y) :
    0 ≤ γ (ExpEvaluator.Fixed.mulDown x y) := by
  rw [gamma_nonneg_iff] at hx hy ⊢
  unfold ExpEvaluator.Fixed.mulDown
  exact Int.ediv_nonneg (mul_nonneg hx hy) (by positivity)

/-! ## 2. The doubling step -/

/-- `exp (-2b)` is the square of `exp (-b)`. -/
theorem exp_neg_double (b : ℝ) :
    Real.exp (-(2 * b)) = Real.exp (-b) * Real.exp (-b) := by
  rw [← Real.exp_add]
  ring_nf

/-- **Squaring a bracket doubles the argument.**

    Given `[γ L, γ U]` bracketing `exp (-b)` with `γ L ≥ 0`, the squared pair
    brackets `exp (-2b)`. Rounding stays conservative: the lower bound squares
    downward, the upper bound upward. -/
theorem bracket_double (b : ℝ) (L U : Fixed)
    (hL : γ L ≤ Real.exp (-b)) (hU : Real.exp (-b) ≤ γ U) (hLnn : 0 ≤ γ L) :
    γ (ExpEvaluator.Fixed.mulDown L L) ≤ Real.exp (-(2 * b)) ∧
      Real.exp (-(2 * b)) ≤ γ (FixedPoint.Fixed.mulUp U U) := by
  have hEpos : (0:ℝ) < Real.exp (-b) := Real.exp_pos _
  constructor
  · calc γ (ExpEvaluator.Fixed.mulDown L L) ≤ γ L * γ L :=
          ExpEvaluator.gamma_mulDown_le L L
      _ ≤ Real.exp (-b) * Real.exp (-b) := by nlinarith
      _ = Real.exp (-(2 * b)) := (exp_neg_double b).symm
  · calc Real.exp (-(2 * b)) = Real.exp (-b) * Real.exp (-b) := exp_neg_double b
      _ ≤ γ U * γ U := by nlinarith
      _ ≤ γ (FixedPoint.Fixed.mulUp U U) := FixedPoint.gamma_mulUp_ge U U

/-! ## 3. Iterating -/

/-- `n` squarings of a bracket pair. -/
def bracketIter : ℕ → Fixed × Fixed → Fixed × Fixed
  | 0, p => p
  | n + 1, p =>
      bracketIter n (ExpEvaluator.Fixed.mulDown p.1 p.1,
                     FixedPoint.Fixed.mulUp p.2 p.2)

/-- **`n` squarings bracket `exp (-(2^n * b))`.**

    The caller supplies a bracket on `exp (-b)` for `b = a / 2^n`, and recovers
    a bracket on `exp (-a)` that is tighter by roughly a factor of `2^n`. -/
theorem bracketIter_sound : ∀ (n : ℕ) (b : ℝ) (L U : Fixed),
    γ L ≤ Real.exp (-b) → Real.exp (-b) ≤ γ U → 0 ≤ γ L →
    γ (bracketIter n (L, U)).1 ≤ Real.exp (-((2 : ℝ) ^ n * b)) ∧
      Real.exp (-((2 : ℝ) ^ n * b)) ≤ γ (bracketIter n (L, U)).2 ∧
      0 ≤ γ (bracketIter n (L, U)).1 := by
  intro n
  induction n with
  | zero =>
    intro b L U hL hU hLnn
    simp only [bracketIter, pow_zero, one_mul]
    exact ⟨hL, hU, hLnn⟩
  | succ m ih =>
    intro b L U hL hU hLnn
    have hd := bracket_double b L U hL hU hLnn
    have hnn := mulDown_nonneg L L hLnn hLnn
    have hres := ih (2 * b) (ExpEvaluator.Fixed.mulDown L L)
      (FixedPoint.Fixed.mulUp U U) hd.1 hd.2 hnn
    have harg : (2 : ℝ) ^ m * (2 * b) = (2 : ℝ) ^ (m + 1) * b := by ring
    simp only [bracketIter]
    rw [← harg]
    exact hres

/-! ## 4. Measured improvement -/

/-- `0.25` in fixed point — one halving of `0.5`. -/
def quarterFx : Fixed := ⟨2 ^ k / 4⟩

/-- `0.125` in fixed point — two halvings. -/
def eighthFx : Fixed := ⟨2 ^ k / 8⟩

-- Direct bracket at a = 0.5, in thousandths:  [500, 666]
#eval (expLoFx halfFx).raw * 1000 / 2 ^ k
#eval (expHiFx halfFx).raw * 1000 / 2 ^ k

-- One doubling from b = 0.25:                 [562, 640]
#eval (ExpEvaluator.Fixed.mulDown (expLoFx quarterFx) (expLoFx quarterFx)).raw * 1000 / 2 ^ k
#eval (FixedPoint.Fixed.mulUp (expHiFx quarterFx) (expHiFx quarterFx)).raw * 1000 / 2 ^ k

-- Two doublings from b = 0.125:               [586, 624]
#eval (bracketIter 2 (expLoFx eighthFx, expHiFx eighthFx)).1.raw * 1000 / 2 ^ k
#eval (bracketIter 2 (expLoFx eighthFx, expHiFx eighthFx)).2.raw * 1000 / 2 ^ k

-- true exp(-0.5) = 0.6065, so 606 in these units

/-! ## Registered status

  DONE: the bracket can be made arbitrarily tight at the caller's discretion,
  with `n` squarings costing `2n` fixed-point multiplications. Soundness is
  independent of `n` — every choice is conservative, so `n` is a pure
  performance/precision dial rather than a correctness parameter.

  A SECOND BENEFIT, not stated as a theorem. The upper bound needs `b > -1` at
  the base of the tower. With `b = a / 2^n` this becomes `a > -2^n`, so doubling
  widens the admissible domain exponentially as well as tightening the bracket.
  Formalizing that would mean restating `evaluator_sound` with the tower in
  place, which is mechanical but not done here.

  NOT DONE: wiring the tower into `evaluator_sound`. That theorem still takes
  the single-step brackets. A caller can apply `bracketIter` and pass the result,
  but the composition is not yet packaged as one theorem.

  STILL OPEN, unchanged: the `Int64` port, and the FFI boundary whose glue is
  hand-written and unverified.
-/

end BracketTightening
end DARM

#print axioms DARM.BracketTightening.mulDown_nonneg
#print axioms DARM.BracketTightening.exp_neg_double
#print axioms DARM.BracketTightening.bracket_double
#print axioms DARM.BracketTightening.bracketIter_sound
