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

/-- A configuration: dimension, learning rate and margin floor in thousandths. -/
structure Config where
  dim : Nat
  etaThou : Int
  deltaThou : Int

def baseline : Config := ⟨8, 500, 50⟩

structure Trial where
  wThou : List Int
  lossThou : List Int

def mkTrial (c : Config) (seed : Nat) : Trial :=
  let ws := (List.range c.dim).map (fun i =>
    (randThou (Nat.repeat lcg (2 * i + 1) seed) 200 1000 : Int))
  let ls := (List.range c.dim).map (fun i =>
    (randThou (Nat.repeat lcg (2 * i + 2) seed) 0 1300 : Int) - 400)
  ⟨ws, ls⟩

/-- True safety, computed in `Float`. -/
def trulySafe (c : Config) (t : Trial) : Bool :=
  let eta := fThou c.etaThou
  let delta := fThou c.deltaThou
  let wp := (t.wThou.zip t.lossThou).map (fun p =>
    fThou p.1 * Float.exp (-(eta * fThou p.2)))
  let Z := wp.foldl (· + ·) 0.0
  let idx := List.range c.dim
  idx.all (fun i =>
    let wi := fThou (t.wThou.getD i 0)
    if delta ≤ wi then
      delta * Z ≤ wp.getD i 0.0
    else true)

/-- The computable check, using the real `EvaluatorTower` pipeline. -/
def fxAccepts (c : Config) (t : Trial) (n : Nat) : Bool :=
  let bs := (List.range c.dim).map (fun i =>
    -- exponent a = eta * loss, halved n times, in thousandths
    let a := c.etaThou * (t.lossThou.getD i 0) / 1000
    ofThouI (a / (2 ^ n : Nat)))
  let brs := (List.range c.dim).map (fun i =>
    expBracket n (bs.getD i ⟨0⟩) (bs.getD i ⟨0⟩))
  let wfx := (List.range c.dim).map (fun i => ofThouI (t.wThou.getD i 0))
  let wpLo := (List.range c.dim).map (fun i =>
    ExpEvaluator.Fixed.mulDown (wfx.getD i ⟨0⟩) (brs.getD i (⟨0⟩, ⟨0⟩)).1)
  let wpHi := (List.range c.dim).map (fun i =>
    FixedPoint.Fixed.mulUp (wfx.getD i ⟨0⟩) (brs.getD i (⟨0⟩, ⟨0⟩)).2)
  let Zhi : Fixed := ⟨wpHi.foldl (fun acc x => acc + x.raw) 0⟩
  let dfx := ofThouI c.deltaThou
  (List.range c.dim).all (fun i =>
    let wi := ofThouI (t.wThou.getD i 0)
    if dfx.raw ≤ wi.raw then
      FixedPoint.checkSafeCoord dfx Zhi (wpLo.getD i ⟨0⟩) ⟨0⟩
    else true)

/-! ## 3. Aggregate -/

def trials : Nat := 200

/-- Of the genuinely-safe states, how many does the check accept at level `n`?
    Returns `(safe states tested, accepted)`. -/
def measure (c : Config) (n : Nat) : Nat × Nat :=
  (List.range trials).foldl
    (fun acc s =>
      let t := mkTrial c (s * 7919 + 13)
      if trulySafe c t then
        (acc.1 + 1, acc.2 + (if fxAccepts c t n then 1 else 0))
      else acc)
    (0, 0)

/-! ### Precision sweep at the baseline configuration

  `(safe states tested, accepted)`. Each doubling roughly halves the rejections. -/

#eval measure baseline 0
#eval measure baseline 1
#eval measure baseline 2
#eval measure baseline 3
#eval measure baseline 4

/-! ### Learning rate

  `n` must scale with `η`. The bracket quality depends on `η * loss / 2^n`, so
  keeping it sharp as `η` grows needs `2^n` to grow with it. At `η = 2` the
  baseline `n = 3` is no longer enough. -/

#eval measure ⟨8, 250, 50⟩ 3
#eval measure ⟨8, 500, 50⟩ 3
#eval measure ⟨8, 1000, 50⟩ 3
#eval measure ⟨8, 2000, 50⟩ 3
#eval measure ⟨8, 2000, 50⟩ 6

/-! ### Margin floor and dimension — the feasibility boundary

  `Reachability.active_card_mul_delta_le_one` proves `|active| * δ ≤ 1`. These
  rows show that bound is NECESSARY BUT FAR FROM SUFFICIENT: the first component
  (safe states found) collapses to zero well before `dim * δ` reaches 1.

  The reason is that the bound comes from summing, so it is tight only when every
  coordinate sits exactly at `δ * Z`. With any spread in the weights the binding
  constraint is the SMALLEST coordinate, which fails much earlier. The usable
  region is roughly half the proved one. -/

#eval measure ⟨8, 500, 20⟩ 3     -- dim*δ = 0.16
#eval measure ⟨8, 500, 50⟩ 3     -- dim*δ = 0.40
#eval measure ⟨8, 500, 80⟩ 3     -- dim*δ = 0.64
#eval measure ⟨8, 500, 125⟩ 3    -- dim*δ = 1.00, the proved limit
#eval measure ⟨4, 500, 50⟩ 3     -- dim*δ = 0.20
#eval measure ⟨16, 500, 50⟩ 3    -- dim*δ = 0.80

/-! ## Reading the result

  The second number over the first is the acceptance rate on genuinely safe
  states; one minus that is the false-rejection rate — the cost of soundness.

  WHAT THIS DOES NOT SHOW. Nothing here tests the fail-closed direction, because
  that is proved (`refinement_coord`) and does not need testing. A benchmark
  cannot establish soundness; it can only establish that soundness is affordable.

  TWO THINGS THE SWEEP FOUND.

  1. `n` MUST SCALE WITH `η`. The bracket is taken at `η * loss / 2^n`, so
     holding it sharp as `η` grows requires `2^n` to grow with it. The baseline
     `n = 3` is adequate at `η = 0.5` and not at `η = 2`.

  2. THE CAPACITY BOUND IS NECESSARY BUT FAR FROM SUFFICIENT.
     `Reachability.active_card_mul_delta_le_one` proves `|active| * δ ≤ 1`. The
     rows above show safe states becoming scarce well before `dim * δ` reaches
     1. The bound is obtained by summing, so it is tight only when every
     coordinate sits exactly at `δ * Z`; with any spread the binding constraint
     is the smallest coordinate, which fails earlier. A deployment should not
     read `|active| ≤ 1/δ` as an operating envelope — the usable region is
     smaller, and by an amount that depends on the weight distribution.

  STILL NOT DONE. Loss distributions are uniform, which is unlikely to be
  realistic. Sample counts are small. Ground truth is `Float`. These numbers
  locate a boundary; they do not characterize it.
-/

end Benchmark
end DARM
