import DarmMonitor.Fixed64Sum

/-
  Fixed64SumOver — `Fixed.sumOver` ported to F64, in the form the evaluators
  actually use.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHY THIS AND NOT `Fixed64Sum`. `Fixed64Sum.sumF64_eq_sum` sums a `List F64`.
  The evaluators do not use lists: `EvaluatorTower.ZhiN` calls
  `ExpEvaluator.Fixed.sumOver`, which is `⟨∑ i, (f i).raw⟩` — a `Finset` sum
  over a `Fintype` index, computed exactly in `Int`. Porting that shape
  directly is simpler than bridging from lists, and it is what a caller needs.

  THE POINT, AGAIN. `Fixed.sumOver` sums `Int` values exactly. The F64 version
  does the same and converts once at the end via `Int64.ofInt`. There is no
  wrapping addition anywhere in the chain — the only obligation is that the
  exact total lands inside `Int64` range, which is a per-term bound times the
  cardinality.
-/

namespace DARM
namespace Fixed64SumOver

open DARM.FixedPoint DARM.HardwarePort DARM.Fixed64 DARM.Fixed64Refinement

variable {ι : Type*} [Fintype ι]

/-! ## 1. The Finset bound

  Same shape as `HardwarePort.sum_output_fits`, over an arbitrary `Fintype`
  rather than `Finset.range n`. -/

theorem finset_abs_sum_le (v : ι → ℤ) (B : ℤ)
    (hB : ∀ i, |v i| ≤ B) :
    |∑ i, v i| ≤ (Fintype.card ι : ℤ) * B := by
  calc |∑ i, v i| ≤ ∑ i, |v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, B := Finset.sum_le_sum (fun i _ => hB i)
    _ = (Fintype.card ι : ℤ) * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## 2. The F64 sum -/

/-- Sum over a finite index type, mirroring `ExpEvaluator.Fixed.sumOver`.
    Accumulates exactly in `Int`; converts once. -/
def F64.sumOver (f : ι → F64) : F64 :=
  ⟨Int64.ofInt (∑ i, (f i).raw.toInt)⟩

/-- **The F64 sum agrees with the `Int` model's sum**, given a per-term bound
    whose product with the cardinality stays inside `Int64` range.

    This is the form `ZhiN` needs. Everything downstream of it — instantiating
    `B` at the multiplication or division envelope — is arithmetic on already
    proved bounds, not new content. -/
theorem sumOver64_toFixed (f : ι → F64) (B : ℤ)
    (hB : ∀ i, |(f i).raw.toInt| ≤ B)
    (hcap : (Fintype.card ι : ℤ) * B < int64Bound) :
    (F64.sumOver f).toFixed
      = ExpEvaluator.Fixed.sumOver (fun i => (f i).toFixed) := by
  have hbound : |∑ i, (f i).raw.toInt| ≤ (Fintype.card ι : ℤ) * B :=
    finset_abs_sum_le (fun i => (f i).raw.toInt) B hB
  have hlt : |∑ i, (f i).raw.toInt| < int64Bound := lt_of_le_of_lt hbound hcap
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hlt
  unfold F64.sumOver F64.toFixed ExpEvaluator.Fixed.sumOver
  congr 1
  exact toInt_ofInt_of_range _ hlo.le hhi

/-! ## 3. It runs -/

def threeOnes : Fin 3 → F64 := fun _ => oneF64

-- 1.0 + 1.0 + 1.0 = 3.0, in thousandths: 3000
#eval (F64.sumOver threeOnes).raw.toInt * 1000 / 2 ^ FixedPoint.k

/-! ## Registered status

  DONE: `Fixed.sumOver` ported to F64 with a proved agreement theorem, in the
  `Fintype`-indexed form the evaluators use rather than the list form.
  Instantiating `B` at an already-proved envelope is the only step between this
  and `ZhiN64`.

  NOT DONE: `ZhiN64` itself, because it needs `expBracket` ported to F64 first
  — that is the doubling tower (`bracketIter` over F64), which is its own
  piece of work and was deliberately not attempted in the same sitting. The
  SUM was the flagged gap; it is now closed in the right shape.

  Also unchanged: no `@[extern]` binding, nothing compiled.
-/

end Fixed64SumOver
end DARM

#print axioms DARM.Fixed64SumOver.finset_abs_sum_le
#print axioms DARM.Fixed64SumOver.sumOver64_toFixed
