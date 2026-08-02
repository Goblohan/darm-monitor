import DarmMonitor.EvaluatorTower

/-
  Benchmark — how often does the computable check reject a state that is
  genuinely safe?

  STATUS: measurement, not proof. This module contains no theorems. It exists
  because everything else in the repository establishes that the monitor is
  CORRECT, and nothing establishes that it is USABLE.

  THE QUESTION. `refinement_coord` is fail-closed: the fixed-point check never
  accepts an unsafe state. It may reject a safe one, and that is the price of
  conservatism. The price was unmeasured. If a monitor rejects most safe states
  it is sound and worthless.

  GROUND TRUTH. Computed in `Float`, which is not ℝ. That is a real caveat, but
  a workable one: doubles carry ~53 bits, the fixed-point model carries 32, and
  the bracket at `n = 0` is loose by ~2^-3. So the reference is three orders of
  magnitude sharper than the thing being measured, which is what a reference
  needs to be. It is not a proof and is not presented as one.

  METHOD. A deterministic LCG generates weight and loss vectors. For each trial:
    1. compute the true safety condition in `Float`
    2. discard trials that are NOT truly safe — those are not what is being
       measured, since rejecting them is correct
    3. run the actual `expBracket` / `wpLoN` / `wpHiN` / `ZhiN` pipeline from
       `EvaluatorTower` at each `n`
    4. count how often the computable check accepts

  Nothing here is randomised at run time: the seed is fixed, so the numbers are
  reproducible by anyone running `lake build`.
-/

namespace DARM
namespace Benchmark

open DARM.FixedPoint DARM.ExpEvaluator DARM.BracketTightening DARM.EvaluatorTower

/-! ## 1. Deterministic pseudo-random source -/

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- A value in `[lo, hi)` scaled to thousandths, from a seed. -/
def randThou (s lo hi : Nat) : Nat := lo + s % (hi - lo)

/-- Fixed-point value from thousandths. -/
def ofThou (t : Nat) : Fixed := ⟨(t * 2 ^ k) / 1000⟩

/-- Fixed-point value from signed thousandths. -/
def ofThouI (t : Int) : Fixed := ⟨(t * 2 ^ k) / 1000⟩

/-- Float value from thousandths. -/
def fThou (t : Int) : Float := Float.ofInt t / 1000.0

/-! ## 2. One trial

  `dim` coordinates, weights in [0.2, 1.0), losses in [-0.4, 0.9), η = 1/2,
  δ = 0.05. The δ is small deliberately: a large margin floor makes the active
  set empty and the test vacuous. -/

def dim : Nat := 8
def etaThou : Int := 500
def deltaThou : Int := 50

structure Trial where
  wThou : List Int
  lossThou : List Int

def mkTrial (seed : Nat) : Trial :=
  let ws := (List.range dim).map (fun i =>
    (randThou (Nat.repeat lcg (2 * i + 1) seed) 200 1000 : Int))
  let ls := (List.range dim).map (fun i =>
    (randThou (Nat.repeat lcg (2 * i + 2) seed) 0 1300 : Int) - 400)
  ⟨ws, ls⟩

/-- True safety, computed in `Float`. -/
def trulySafe (t : Trial) : Bool :=
  let eta := fThou etaThou
  let delta := fThou deltaThou
  let wp := (t.wThou.zip t.lossThou).map (fun p =>
    fThou p.1 * Float.exp (-(eta * fThou p.2)))
  let Z := wp.foldl (· + ·) 0.0
  let idx := List.range dim
  idx.all (fun i =>
    let wi := fThou (t.wThou.getD i 0)
    if delta ≤ wi then
      delta * Z ≤ wp.getD i 0.0
    else true)

/-- The computable check, using the real `EvaluatorTower` pipeline. -/
def fxAccepts (t : Trial) (n : Nat) : Bool :=
  let bs := (List.range dim).map (fun i =>
    -- exponent a = eta * loss, halved n times, in thousandths
    let a := etaThou * (t.lossThou.getD i 0) / 1000
    ofThouI (a / (2 ^ n : Nat)))
  let brs := (List.range dim).map (fun i =>
    expBracket n (bs.getD i ⟨0⟩) (bs.getD i ⟨0⟩))
  let wfx := (List.range dim).map (fun i => ofThouI (t.wThou.getD i 0))
  let wpLo := (List.range dim).map (fun i =>
    ExpEvaluator.Fixed.mulDown (wfx.getD i ⟨0⟩) (brs.getD i (⟨0⟩, ⟨0⟩)).1)
  let wpHi := (List.range dim).map (fun i =>
    FixedPoint.Fixed.mulUp (wfx.getD i ⟨0⟩) (brs.getD i (⟨0⟩, ⟨0⟩)).2)
  let Zhi : Fixed := ⟨wpHi.foldl (fun acc x => acc + x.raw) 0⟩
  let dfx := ofThouI deltaThou
  (List.range dim).all (fun i =>
    let wi := ofThouI (t.wThou.getD i 0)
    if dfx.raw ≤ wi.raw then
      FixedPoint.checkSafeCoord dfx Zhi (wpLo.getD i ⟨0⟩) ⟨0⟩
    else true)

/-! ## 3. Aggregate -/

def trials : Nat := 200

/-- Of the genuinely-safe states, how many does the check accept at level `n`?
    Returns `(safe states tested, accepted)`. -/
def measure (n : Nat) : Nat × Nat :=
  (List.range trials).foldl
    (fun acc s =>
      let t := mkTrial (s * 7919 + 13)
      if trulySafe t then
        (acc.1 + 1, acc.2 + (if fxAccepts t n then 1 else 0))
      else acc)
    (0, 0)

-- (safe states tested, accepted by the fixed-point check)
#eval measure 0
#eval measure 1
#eval measure 2
#eval measure 3
#eval measure 4

/-! ## Reading the result

  The second number over the first is the acceptance rate on genuinely safe
  states; one minus that is the false-rejection rate — the cost of soundness.

  WHAT THIS DOES NOT SHOW. Nothing here tests the fail-closed direction, because
  that is proved (`refinement_coord`) and does not need testing. A benchmark
  cannot establish soundness; it can only establish that soundness is affordable.

  WHAT WOULD MAKE IT BETTER. Realistic loss distributions rather than uniform;
  larger `dim`; sweeping `δ` and `η` rather than fixing them. The current
  parameters are a single point in that space, chosen so the active set is
  usually non-empty. Numbers from one point should not be generalized.
-/

end Benchmark
end DARM
