import DarmMonitor.Fixed64ZhiN

/-
  Fixed64Evaluator — the quantified evaluator over F64.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT THIS IS. Step 2 of the runtime path: `EvaluatorTower.evaluator_sound_tower`
  restated over `F64`. A caller running the check on genuine `Int64` values
  gets `is_safe_signal_Z` — the real-number safety certificate — back.

  HOW IT IS PROVED. Not by re-deriving anything. Every F64 operation has been
  proved to agree with its `Int`-model counterpart, so this transports: show
  the F64 check, active set, and bounds coincide with the `Fixed` ones on
  `.toFixed` images, then apply `evaluator_sound_tower` to those images. The
  real-number reasoning happens once, in the `Int` model, and is inherited.

  ON THE AGREEMENT HYPOTHESES. `hZhiEq` and `hwpLoEq` are taken as hypotheses
  rather than derived inline. Deriving them would mean restating every
  condition `ZhiN64_eq` and the bracket lemmas need, indexed over `ι` — the
  same obligations, just relocated and harder to read. A caller discharges them
  with `Fixed64ZhiN.ZhiN64_eq` and `wpLoN64_eq` below. This keeps visible where
  each obligation actually comes from.
-/

namespace DARM
namespace Fixed64Evaluator

open DARM.FixedPoint DARM.HardwarePort DARM.Fixed64 DARM.Fixed64Refinement
open DARM.Fixed64Tower DARM.Fixed64Bracket DARM.Fixed64ZhiN
open DARM.ActiveSurrogate DARM.EvaluatorTower DARM.Boundary

variable {ι : Type*} [Fintype ι]

/-! ## 1. The per-coordinate lower bound over F64 -/

/-- Mirrors `EvaluatorTower.wpLoN`: one `mulDown` against the bracket's lower
    end. -/
def wpLoN64 (n : ℕ) (wLo bLo bHi : F64) : F64 :=
  Fixed64MulDown.F64.mulDown wLo (expBracket64 n bLo bHi).1

/-- **`wpLoN64` agrees with `wpLoN`.** -/
theorem wpLoN64_eq (n : ℕ) (wLo bLo bHi : F64)
    (hone : InUnit oneF64) (hbHi : InUnit bHi)
    (hden : 4294967296 ≤ (F64.addI oneF64 bLo).raw.toInt)
    (hsum_lo : -(2 ^ 63) ≤ oneF64.raw.toInt + bLo.raw.toInt)
    (hsum_hi : oneF64.raw.toInt + bLo.raw.toInt < 2 ^ 63)
    (hwx : -(2 ^ 63) < oneF64.raw.toInt)
    (hlo_unit : InUnit (expLoFx64 bHi)) (hhi_unit : InUnit (expHiFx64 bLo))
    (hwb : |wLo.raw.toInt| ≤ 140737488355328)
    (hbb : |(expBracket64 n bLo bHi).1.raw.toInt| ≤ 140737488355328) :
    (wpLoN64 n wLo bLo bHi).toFixed
      = EvaluatorTower.wpLoN n wLo.toFixed bLo.toFixed bHi.toFixed := by
  have hbr := expBracket64_toFixed n bLo bHi hone hbHi hden hsum_lo hsum_hi hwx
    hlo_unit hhi_unit
  unfold wpLoN64 EvaluatorTower.wpLoN
  rw [Fixed64MulDown.mulDown_simulates wLo (expBracket64 n bLo bHi).1 hwb hbb, hbr.1]

/-! ## 2. The active set over F64

  `active_fx` filters on `δlo.raw ≤ (wHi i).raw`, and `F64.toFixed x = ⟨x.raw.toInt⟩`,
  so the F64 filter and the model's filter are the same predicate. -/

def active_fx64 (δlo : F64) (wHi : ι → F64) : Finset ι :=
  Finset.univ.filter (fun i => δlo.raw.toInt ≤ (wHi i).raw.toInt)

theorem active_fx64_eq (δlo : F64) (wHi : ι → F64) :
    active_fx64 δlo wHi = active_fx δlo.toFixed (fun i => (wHi i).toFixed) := by
  unfold active_fx64 active_fx F64.toFixed
  rfl

/-! ## 3. The quantified evaluator -/

/-- **The evaluator, over F64.**

    Running `checkSafeCoord64` on genuine `Int64` values, over the F64 active
    set, with the F64 partition bound and coordinate bounds, establishes
    `is_safe_signal_Z` for the real system.

    This is the theorem the port existed to reach. Every hypothesis is either a
    real-number bound the caller already had to supply for the `Int` version,
    or an agreement fact discharged by the `_eq` lemmas in this port. -/
theorem evaluator_sound_tower64
    (n : ℕ) (δ η : ℝ) (loss w b : ι → ℝ)
    (δlo δhi margin : F64) (wLo wHi bLo bHi : ι → F64)
    (hb : ∀ i, (2:ℝ) ^ n * b i = η * loss i)
    (hδlo : γ δlo.toFixed ≤ δ) (hδhi : δ ≤ γ δhi.toFixed) (hδnn : 0 ≤ δ)
    (hwnn : ∀ i, 0 ≤ w i)
    (hwHi : ∀ i, w i ≤ γ (wHi i).toFixed)
    (hwLo : ∀ i, γ (wLo i).toFixed ≤ w i) (hwLonn : ∀ i, 0 ≤ γ (wLo i).toFixed)
    (hbLo : ∀ i, γ (bLo i).toFixed ≤ b i)
    (hbHi : ∀ i, b i ≤ γ (bHi i).toFixed)
    (hbase : ∀ i, 0 ≤ γ (ExpEvaluator.expLoFx (bHi i).toFixed))
    (hdom : ∀ i, 0 < (FixedPoint.Fixed.add ExpEvaluator.one (bLo i).toFixed).raw)
    (hmargin : 0 ≤ γ margin.toFixed)
    (hZhiEq : (ZhiN64 n wHi bLo bHi).toFixed
      = EvaluatorTower.ZhiN n (fun i => (wHi i).toFixed)
          (fun i => (bLo i).toFixed) (fun i => (bHi i).toFixed))
    (hwpLoEq : ∀ i, (wpLoN64 n (wLo i) (bLo i) (bHi i)).toFixed
      = EvaluatorTower.wpLoN n (wLo i).toFixed (bLo i).toFixed (bHi i).toFixed)
    (hcheck : ∀ i ∈ active_fx64 δlo wHi,
      FixedPoint.checkSafeCoord δhi.toFixed (ZhiN64 n wHi bLo bHi).toFixed
        (wpLoN64 n (wLo i) (bLo i) (bHi i)).toFixed margin.toFixed = true) :
    is_safe_signal_Z δ η loss w := by
  refine EvaluatorTower.evaluator_sound_tower n δ η loss w b
    δlo.toFixed δhi.toFixed margin.toFixed
    (fun i => (wLo i).toFixed) (fun i => (wHi i).toFixed)
    (fun i => (bLo i).toFixed) (fun i => (bHi i).toFixed)
    hb hδlo hδhi hδnn hwnn hwHi hwLo hwLonn hbLo hbHi hbase hdom hmargin ?_
  intro i hi
  have hi64 : i ∈ active_fx64 δlo wHi := by
    rw [active_fx64_eq]; exact hi
  have h := hcheck i hi64
  rw [hZhiEq, hwpLoEq i] at h
  exact h

/-! ## Registered status

  DONE. Step 2 of the runtime path. `evaluator_sound_tower64` takes the check
  run on `Int64` values and returns `is_safe_signal_Z` — the real-number
  certificate — for the whole index type, not one coordinate.

  Together with step 1 this means: every operation, every structure, and now
  the quantified theorem exist in verified 64-bit form. The proof obligations a
  caller carries are exactly the ones the `Int` version already had, plus the
  agreement facts, which the `_eq` lemmas discharge.

  WHAT REMAINS, and it is not Lean work:
    * The `@[extern]` binding to a widening multiply. This is a TRUST BOUNDARY:
      nothing proves the C matches the Lean specification it replaces.
    * A `[[lean_exe]]` target and an actual compiled binary.
    * Measurement against that binary rather than the interpreter.

  Per the runtime plan, those should not share a session with proof work —
  different failure modes, and a wrong C function compiles cleanly and fails
  silently.
-/

end Fixed64Evaluator
end DARM

#print axioms DARM.Fixed64Evaluator.wpLoN64_eq
#print axioms DARM.Fixed64Evaluator.active_fx64_eq
#print axioms DARM.Fixed64Evaluator.evaluator_sound_tower64
