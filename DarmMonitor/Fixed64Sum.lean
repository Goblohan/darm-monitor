import DarmMonitor.RationalF64

/-
  Fixed64Sum — summing F64 values, and why the "wraparound" concern in
  `Fixed64Refinement`'s registered status was wrong.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  THE CORRECTION. `Fixed64Refinement.lean` recorded, as open work: "native
  Int64 addition wraps, and no theorem yet bounds a sum of F64 values against
  that." Checking the actual code shows this describes a primitive that is
  never used. `F64.addI x y = Int64.ofInt (x.raw.toInt + y.raw.toInt)` computes
  the sum in `Int` — exact, arbitrary precision — and converts back only once,
  at the end, via the same `bmod`-based `Int64.ofInt` that
  `toInt_ofInt_of_range` already characterizes exactly. Raw `Int64 +` appears
  nowhere in this repository.

  So there is no wraparound case to handle in what is actually written. What is
  needed is: given a per-term bound and a total-count bound, every partial sum
  built by iterating `addI` stays in `Int64` range, so every step round-trips
  exactly and the F64 fold equals the exact `Int` sum.

  ON THE SECOND ATTEMPT AT THIS PROOF. A first version tried to accumulate the
  range bound inductively — separately bound the head and the tail, then add
  the two bounds together at each step. That repeatedly produced `abs`-wrapped
  hypotheses passed to `linarith` before being unwrapped, which is silent and
  looks like a different failure each time depending on which branch hits it
  first. The fix is structural, not tactical: bound the WHOLE prefix list in
  one triangle-inequality application (`list_abs_sum_le` below, proved once,
  with no `F64` involved) rather than reconstructing the bound piece by piece
  at every cons.
-/

namespace DARM
namespace Fixed64Sum

open DARM.FixedPoint DARM.HardwarePort DARM.Fixed64 DARM.Fixed64Refinement

/-! ## 1. A pure `List ℤ` bound, proved once

  Deliberately has nothing to do with `F64` or `Int64`, so it can be checked in
  isolation from everything about hardware representation. -/

private lemma list_abs_sum_le (l : List ℤ) (B : ℤ)
    (hB : ∀ v ∈ l, |v| ≤ B) (hBnn : 0 ≤ B) :
    |l.sum| ≤ (l.length : ℤ) * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hxb : |x| ≤ B := hB x (by simp)
    have hxsb : |xs.sum| ≤ (xs.length : ℤ) * B := ih (fun v hv => hB v (by simp [hv]))
    have htri : |x + xs.sum| ≤ |x| + |xs.sum| := by
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le x, neg_abs_le xs.sum]
      · linarith [le_abs_self x, le_abs_self xs.sum]
    simp only [List.length_cons, List.sum_cons]
    push_cast
    linarith [htri, hxb, hxsb]

/-! ## 2. The fold -/

/-- Sum of a list of `F64` values via repeated `addI`. -/
def sumF64 : List F64 → F64
  | [] => ⟨0⟩
  | x :: xs => F64.addI x (sumF64 xs)

/-! ## 3. It matches the exact Int sum, given a per-term and count bound -/

/-- **The F64 fold equals the exact `Int` sum**, provided every term is bounded
    by `B` and the list is short enough that the total cannot leave range.

    Applies `list_abs_sum_le` to the FULL cons'd list at each step, rather than
    combining a separately-bounded head and tail — that is what makes the
    induction go through cleanly. -/
theorem sumF64_eq_sum (l : List F64) (B : ℤ) (hB : ∀ x ∈ l, |x.raw.toInt| ≤ B)
    (hBnn : 0 ≤ B) (hcap : (l.length : ℤ) * B < int64Bound) :
    (sumF64 l).raw.toInt = (l.map (fun x => x.raw.toInt)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hBx : ∀ y ∈ xs, |y.raw.toInt| ≤ B := fun y hy => hB y (by simp [hy])
    have hlenle : (xs.length : ℤ) ≤ ((x :: xs).length : ℤ) := by
      simp only [List.length_cons]; push_cast; linarith
    have hcapxs : (xs.length : ℤ) * B < int64Bound := by nlinarith [hcap, hlenle, hBnn]
    have ihxs := ih hBx hcapxs
    -- bound the WHOLE list x :: xs in one shot
    have hfull : |(x.raw.toInt + (xs.map (fun y => y.raw.toInt)).sum)|
        ≤ ((x :: xs).length : ℤ) * B := by
      have h := list_abs_sum_le ((x :: xs).map (fun y => y.raw.toInt)) B
        (fun v hv => by
          simp only [List.mem_map] at hv
          obtain ⟨y, hy, rfl⟩ := hv
          exact hB y hy) hBnn
      simpa [List.map_cons, List.sum_cons] using h
    have hrange : -(2 ^ 63) < x.raw.toInt + (xs.map (fun y => y.raw.toInt)).sum
        ∧ x.raw.toInt + (xs.map (fun y => y.raw.toInt)).sum < 2 ^ 63 := by
      have h2 : |(x.raw.toInt + (xs.map (fun y => y.raw.toInt)).sum)| < int64Bound :=
        lt_of_le_of_lt hfull hcap
      exact abs_lt.mp h2
    show (F64.addI x (sumF64 xs)).raw.toInt
        = x.raw.toInt + (xs.map (fun y => y.raw.toInt)).sum
    unfold F64.addI
    dsimp only
    rw [ihxs]
    exact toInt_ofInt_of_range _ hrange.1.le (by omega)

/-! ## 4. It runs -/

def threeF64 : List F64 := [oneF64, oneF64, oneF64]

-- 1.0 + 1.0 + 1.0 = 3.0, in thousandths: 3000
#eval (sumF64 threeF64).raw.toInt * 1000 / 2 ^ FixedPoint.k

/-! ## Registered status

  DONE: `sumF64_eq_sum` proves the `F64` fold matches the exact `Int` sum
  whenever every term is bounded and the count-times-bound product stays under
  `int64Bound`. This CORRECTS the "wraparound" note in `Fixed64Refinement.lean`
  — no code in this repository performs raw wrapping `Int64` addition; `addI`
  always round-trips through exact `Int`, and this theorem shows that
  round-trip stays valid across an entire list, not just one step.

  NOT DONE: this sums a bare `List F64`, not the `active_fx`-filtered sum
  `ZhiN` needs, and it is not yet wired into `EvaluatorTower` or `RationalF64`.
  Doing so is now mechanical — instantiate `B` at the multiplication or
  division envelope already proved — but it has not been done. The genuinely
  new mathematics this module was expected to require did not materialize;
  what remained was checking whether it was needed at all, and it mostly was
  not: `F64.addI` was already exact.
-/

end Fixed64Sum
end DARM

#print axioms DARM.Fixed64Sum.sumF64_eq_sum
