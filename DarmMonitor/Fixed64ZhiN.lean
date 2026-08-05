import DarmMonitor.Fixed64Bracket

/-
  Fixed64ZhiN — the partition-function bound over F64.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT THIS COMPLETES. `EvaluatorTower.ZhiN` is
  `sumOver (fun i => wpHiN n (wHi i) (bLo i) (bHi i))`, where `wpHiN` is one
  `mulUp` against the bracket's upper end. Both pieces now exist in verified
  64-bit form — `Fixed64Bracket.expBracket64_toFixed` for the bracket,
  `Fixed64.mul_simulates` for the product, `Fixed64SumOver.sumOver64_toFixed`
  for the sum — so this is their composition.

  With it, every structural component of the quantified evaluator exists over
  F64. What remains is `evaluator_sound_tower64` itself, which threads these
  together with the real-number certificate.

  ON THE HYPOTHESIS COUNT. This theorem carries many hypotheses, and that is
  not incidental: each is an obligation a real caller genuinely has. The
  bracket needs its unit conditions, the product needs its envelope, the sum
  needs its per-term bound times cardinality. Collapsing them into something
  shorter would mean hiding a condition rather than removing it.
-/

namespace DARM
namespace Fixed64ZhiN

open DARM.FixedPoint DARM.HardwarePort DARM.Fixed64 DARM.Fixed64Refinement
open DARM.Fixed64Tower DARM.Fixed64Bracket DARM.Fixed64SumOver

variable {ι : Type*} [Fintype ι]

/-! ## 1. The per-coordinate upper bound -/

/-- Mirrors `EvaluatorTower.wpHiN`: one `mulUp` against the bracket's upper
    end. -/
def wpHiN64 (n : ℕ) (wHi bLo bHi : F64) : F64 :=
  F64.mulUp wHi (expBracket64 n bLo bHi).2

/-- **`wpHiN64` agrees with `wpHiN`**, given the bracket's hypotheses and the
    multiplication envelope on both factors. -/
theorem wpHiN64_eq (n : ℕ) (wHi bLo bHi : F64)
    (hone : InUnit oneF64) (hbHi : InUnit bHi)
    (hden : 4294967296 ≤ (F64.addI oneF64 bLo).raw.toInt)
    (hsum_lo : -(2 ^ 63) ≤ oneF64.raw.toInt + bLo.raw.toInt)
    (hsum_hi : oneF64.raw.toInt + bLo.raw.toInt < 2 ^ 63)
    (hwx : -(2 ^ 63) < oneF64.raw.toInt)
    (hlo_unit : InUnit (expLoFx64 bHi)) (hhi_unit : InUnit (expHiFx64 bLo))
    (hwb : |wHi.raw.toInt| ≤ 140737488355328)
    (hbb : |(expBracket64 n bLo bHi).2.raw.toInt| ≤ 140737488355328) :
    (wpHiN64 n wHi bLo bHi).toFixed
      = EvaluatorTower.wpHiN n wHi.toFixed bLo.toFixed bHi.toFixed := by
  have hbr := expBracket64_toFixed n bLo bHi hone hbHi hden hsum_lo hsum_hi hwx
    hlo_unit hhi_unit
  unfold wpHiN64 EvaluatorTower.wpHiN
  rw [mul_simulates wHi (expBracket64 n bLo bHi).2 hwb hbb, hbr.2]

/-! ## 2. The partition-function bound -/

/-- Mirrors `EvaluatorTower.ZhiN`. -/
def ZhiN64 (n : ℕ) (wHi bLo bHi : ι → F64) : F64 :=
  F64.sumOver (fun i => wpHiN64 n (wHi i) (bLo i) (bHi i))

/-- **`ZhiN64` agrees with `ZhiN`.**

    The per-coordinate agreement comes from `wpHiN64_eq`; the sum agreement
    from `sumOver64_toFixed`, whose bound obligation is the per-term envelope
    times the index type's cardinality. -/
theorem ZhiN64_eq (n : ℕ) (wHi bLo bHi : ι → F64) (B : ℤ)
    (hcoord : ∀ i, (wpHiN64 n (wHi i) (bLo i) (bHi i)).toFixed
      = EvaluatorTower.wpHiN n (wHi i).toFixed (bLo i).toFixed (bHi i).toFixed)
    (hB : ∀ i, |(wpHiN64 n (wHi i) (bLo i) (bHi i)).raw.toInt| ≤ B)
    (hcap : (Fintype.card ι : ℤ) * B < int64Bound) :
    (ZhiN64 n wHi bLo bHi).toFixed
      = EvaluatorTower.ZhiN n (fun i => (wHi i).toFixed)
          (fun i => (bLo i).toFixed) (fun i => (bHi i).toFixed) := by
  unfold ZhiN64 EvaluatorTower.ZhiN
  rw [sumOver64_toFixed (fun i => wpHiN64 n (wHi i) (bLo i) (bHi i)) B hB hcap]
  congr 1
  funext i
  exact hcoord i

/-! ## 3. It runs -/

def quarterZ : F64 := ⟨Int64.ofInt (2 ^ FixedPoint.k / 4)⟩
def wsZ : Fin 2 → F64 := fun _ => oneF64
def bsZ : Fin 2 → F64 := fun _ => quarterZ

-- two coordinates, each 1.0 * bracket-upper at n=1 (0.64), summing to ~1.28
#eval (ZhiN64 1 wsZ bsZ bsZ).raw.toInt * 100 / 2 ^ FixedPoint.k

/-! ## Registered status

  DONE: `ZhiN64` and `wpHiN64`, agreeing with their `Int` counterparts. Every
  structural component of the quantified evaluator now exists over F64:
  arithmetic (`Fixed64`, `Fixed64MulDown`, `Fixed64Sub`), summation
  (`Fixed64SumOver`), the tower (`Fixed64Tower`), the bracket
  (`Fixed64Bracket`), and now the partition bound.

  This completes step 1 of the runtime path.

  NEXT: `evaluator_sound_tower64` — the quantified theorem itself, threading
  these together with the real-number certificate. After that, the `@[extern]`
  boundary and an actual binary, neither of which is Lean work.
-/

end Fixed64ZhiN
end DARM

#print axioms DARM.Fixed64ZhiN.wpHiN64_eq
#print axioms DARM.Fixed64ZhiN.ZhiN64_eq
