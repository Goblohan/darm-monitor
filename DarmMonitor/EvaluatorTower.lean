import DarmMonitor.BracketTightening

/-
  EvaluatorTower — `evaluator_sound` with the doubling tower built in.

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`.

  WHAT WAS LEFT OVER. `ExpEvaluator.evaluator_sound` takes the single-step
  brackets. `BracketTightening.bracketIter_sound` makes brackets arbitrarily
  sharp. Both are proved, but a caller wanting tight bounds had to apply
  `bracketIter` and thread the result through by hand.

  THE FIX. Generalize the coordinate lemmas to accept ANY bracket on
  `exp (-a)` rather than the specific `expLoFx`/`expHiFx` pair. The tower then
  plugs in without further work, and `n` becomes an ordinary argument.

  WHAT THE CALLER SUPPLIES. Brackets on `b i` where `2^n * b i = η * loss i` —
  that is, on the exponent divided down by `2^n`. Halving is left to the caller
  because it is arithmetic they are already doing, and doing it here would need
  directed halving lemmas for no gain.

  TWO EFFECTS, BOTH FROM THE SAME `n`:
    * the bracket tightens by roughly half per squaring
      (measured: 166 -> 78 -> 38 thousandths at `a = 0.5`)
    * the domain condition applies to `b`, not `a`, so it reads
      `η * loss i > -2^n` rather than `> -1`

  Soundness holds for every `n`, so it is a precision dial, not a correctness
  parameter. `n = 0` recovers `evaluator_sound` exactly.
-/

namespace DARM
namespace EvaluatorTower

open DARM.Boundary DARM.FixedPoint DARM.ActiveSurrogate DARM.ExpEvaluator
open DARM.BracketTightening

/-! ## 1. Coordinate bounds from an arbitrary bracket

  Generalizations of `wpLoFx_sound` and `wpHiFx_sound`: the exponential bound is
  a parameter rather than a fixed construction. -/

theorem wpLo_of_bracket (wi a : ℝ) (wLo E : Fixed)
    (hw : γ wLo ≤ wi) (hwnn : 0 ≤ γ wLo)
    (hE : γ E ≤ Real.exp (-a)) (hEnn : 0 ≤ γ E) :
    γ (ExpEvaluator.Fixed.mulDown wLo E) ≤ wi * Real.exp (-a) := by
  calc γ (ExpEvaluator.Fixed.mulDown wLo E) ≤ γ wLo * γ E :=
        ExpEvaluator.gamma_mulDown_le wLo E
    _ ≤ wi * Real.exp (-a) := by
        have h1 : γ wLo * γ E ≤ wi * γ E := mul_le_mul_of_nonneg_right hw hEnn
        have h2 : wi * γ E ≤ wi * Real.exp (-a) := by
          apply mul_le_mul_of_nonneg_left hE
          linarith
        linarith

theorem wpHi_of_bracket (wi a : ℝ) (wHi E : Fixed)
    (hw : wi ≤ γ wHi) (hwnn : 0 ≤ wi)
    (hE : Real.exp (-a) ≤ γ E) :
    wi * Real.exp (-a) ≤ γ (FixedPoint.Fixed.mulUp wHi E) := by
  have hexppos : (0:ℝ) ≤ Real.exp (-a) := (Real.exp_pos _).le
  calc wi * Real.exp (-a) ≤ γ wHi * Real.exp (-a) :=
        mul_le_mul_of_nonneg_right hw hexppos
    _ ≤ γ wHi * γ E := by
        apply mul_le_mul_of_nonneg_left hE
        linarith
    _ ≤ γ (FixedPoint.Fixed.mulUp wHi E) := FixedPoint.gamma_mulUp_ge wHi E

/-! ## 2. The tower as a single bracket -/

/-- `n` squarings of the single-step bracket. `n = 0` is the single-step
    bracket itself. -/
def expBracket (n : ℕ) (bLo bHi : Fixed) : Fixed × Fixed :=
  bracketIter n (expLoFx bHi, expHiFx bLo)

/-- **The tower brackets `exp (-(2^n * b))`.** -/
theorem expBracket_sound (n : ℕ) (b : ℝ) (bLo bHi : Fixed)
    (hLo : γ bLo ≤ b) (hHi : b ≤ γ bHi)
    (hdom : 0 < (FixedPoint.Fixed.add ExpEvaluator.one bLo).raw)
    (hbase : 0 ≤ γ (expLoFx bHi)) :
    γ (expBracket n bLo bHi).1 ≤ Real.exp (-((2:ℝ) ^ n * b)) ∧
      Real.exp (-((2:ℝ) ^ n * b)) ≤ γ (expBracket n bLo bHi).2 ∧
      0 ≤ γ (expBracket n bLo bHi).1 := by
  unfold expBracket
  exact bracketIter_sound n b (expLoFx bHi) (expHiFx bLo)
    (expLoFx_sound b bHi hHi) (expHiFx_sound b bLo hLo hdom) hbase

/-! ## 3. Assembled coordinate and partition bounds -/

def wpLoN (n : ℕ) (wLo bLo bHi : Fixed) : Fixed :=
  ExpEvaluator.Fixed.mulDown wLo (expBracket n bLo bHi).1

def wpHiN (n : ℕ) (wHi bLo bHi : Fixed) : Fixed :=
  FixedPoint.Fixed.mulUp wHi (expBracket n bLo bHi).2

variable {ι : Type*} [Fintype ι]

def ZhiN (n : ℕ) (wHi bLo bHi : ι → Fixed) : Fixed :=
  ExpEvaluator.Fixed.sumOver (fun i => wpHiN n (wHi i) (bLo i) (bHi i))

/-! ## 4. End to end, with `n` as a parameter -/

/-- **The evaluator with the tower.** Identical in shape to
    `ExpEvaluator.evaluator_sound`, but the brackets are `n`-fold tightened and
    the caller supplies bounds on the HALVED exponent `b i`, related to the true
    exponent by `2^n * b i = η * loss i`.

    Setting `n = 0` recovers the original theorem. Increasing `n` costs `2n`
    fixed-point multiplications per coordinate and buys both tightness and
    domain width. Soundness is independent of `n`. -/
theorem evaluator_sound_tower
    (n : ℕ) (δ η : ℝ) (loss w b : ι → ℝ)
    (δlo δhi margin : Fixed) (wLo wHi bLo bHi : ι → Fixed)
    (hb : ∀ i, (2:ℝ) ^ n * b i = η * loss i)
    (hδlo : γ δlo ≤ δ) (hδhi : δ ≤ γ δhi) (hδnn : 0 ≤ δ)
    (hwnn : ∀ i, 0 ≤ w i)
    (hwHi : ∀ i, w i ≤ γ (wHi i))
    (hwLo : ∀ i, γ (wLo i) ≤ w i) (hwLonn : ∀ i, 0 ≤ γ (wLo i))
    (hbLo : ∀ i, γ (bLo i) ≤ b i)
    (hbHi : ∀ i, b i ≤ γ (bHi i))
    (hbase : ∀ i, 0 ≤ γ (expLoFx (bHi i)))
    (hdom : ∀ i, 0 < (FixedPoint.Fixed.add ExpEvaluator.one (bLo i)).raw)
    (hmargin : 0 ≤ γ margin)
    (hcheck : ∀ i ∈ active_fx δlo wHi,
      FixedPoint.checkSafeCoord δhi (ZhiN n wHi bLo bHi)
        (wpLoN n (wLo i) (bLo i) (bHi i)) margin = true) :
    is_safe_signal_Z δ η loss w := by
  have hrw : ∀ i, reweight η loss w i = w i * Real.exp (-((2:ℝ) ^ n * b i)) := by
    intro i
    unfold reweight
    rw [hb i]
    ring_nf
  have hbr : ∀ i, γ (expBracket n (bLo i) (bHi i)).1 ≤ Real.exp (-((2:ℝ) ^ n * b i))
      ∧ Real.exp (-((2:ℝ) ^ n * b i)) ≤ γ (expBracket n (bLo i) (bHi i)).2
      ∧ 0 ≤ γ (expBracket n (bLo i) (bHi i)).1 := by
    intro i
    exact expBracket_sound n (b i) (bLo i) (bHi i) (hbLo i) (hbHi i) (hdom i) (hbase i)
  have hwpLo : ∀ i, γ (wpLoN n (wLo i) (bLo i) (bHi i)) ≤ reweight η loss w i := by
    intro i
    rw [hrw i]
    exact wpLo_of_bracket (w i) ((2:ℝ) ^ n * b i) (wLo i) _
      (hwLo i) (hwLonn i) (hbr i).1 (hbr i).2.2
  have hZhi : Z (reweight η loss w) ≤ γ (ZhiN n wHi bLo bHi) := by
    unfold Z ZhiN
    rw [ExpEvaluator.gamma_sumOver]
    apply Finset.sum_le_sum
    intro i _
    rw [hrw i]
    exact wpHi_of_bracket (w i) ((2:ℝ) ^ n * b i) (wHi i) _
      (hwHi i) (hwnn i) (hbr i).2.1
  have hZnn : 0 ≤ Z (reweight η loss w) := by
    unfold Z
    apply Finset.sum_nonneg
    intro i _
    rw [hrw i]
    exact mul_nonneg (hwnn i) (Real.exp_pos _).le
  exact refinement_quantified δ η loss w δlo δhi (ZhiN n wHi bLo bHi) margin wHi
    (fun i => wpLoN n (wLo i) (bLo i) (bHi i))
    hδlo hδhi hδnn hZnn hZhi hwHi hwpLo hmargin hcheck

/-! ## 5. It runs -/

-- the n = 2 bracket at a = 0.5, i.e. b = 0.125, in thousandths: [586, 624]
#eval (expBracket 2 eighthFx eighthFx).1.raw * 1000 / 2 ^ k
#eval (expBracket 2 eighthFx eighthFx).2.raw * 1000 / 2 ^ k

-- n = 0 is the single-step bracket at b = 0.5: [500, 666]
#eval (expBracket 0 halfFx halfFx).1.raw * 1000 / 2 ^ k
#eval (expBracket 0 halfFx halfFx).2.raw * 1000 / 2 ^ k

/-! ## Registered status

  DONE. The runtime chain is now a single theorem. `evaluator_sound_tower`
  reduces `is_safe_signal_Z` — a statement over ℝ — to a computable check, with
  `n` an ordinary argument controlling precision and domain width. Every
  hypothesis is a bracket the caller computes or a condition it can test.

  STILL OPEN, unchanged:
    * The `Int64` port. `Int` is arbitrary-precision, which keeps the algebra
      clean but boxes into `lean_object*`. Porting is what makes `@[export]`
      emit primitive C types.
    * The FFI boundary. Lean's emitted C uses its runtime; the marshalling glue
      is hand-written and unverified, so the TCB is Lean kernel + C emitter +
      C compiler + that glue.

  NOT A GAP, but worth stating: nothing here has been benchmarked. The
  arithmetic is proved sound and the brackets are measured, but no monitor has
  been run against a workload, so the practical rejection rate at any given `n`
  is unknown.
-/

end EvaluatorTower
end DARM

#print axioms DARM.EvaluatorTower.wpLo_of_bracket
#print axioms DARM.EvaluatorTower.wpHi_of_bracket
#print axioms DARM.EvaluatorTower.expBracket_sound
#print axioms DARM.EvaluatorTower.evaluator_sound_tower
