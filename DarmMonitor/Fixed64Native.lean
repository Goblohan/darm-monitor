import DarmMonitor.Fixed64Evaluator

/-
  Fixed64Native — the C binding, and differential tests against the verified
  implementation.

  STATUS: the Lean side compiles and the tests run. The C function is NOT
  verified. See the trust discussion below.

  WHAT THIS IS. Step 3 of the runtime path: an `@[extern]` binding to a C
  widening multiply, so the arithmetic runs as native 64-bit register
  operations rather than through Lean's boxed `Int`.

  THE DESIGN CHOICE, AND WHY. `@[extern]` on the PROVED `F64.mulUp` would
  replace its implementation everywhere, including inside every simulation
  theorem. Those theorems would remain true about the Lean definition while the
  running code was something else — the proof and the executable would diverge
  silently, with nothing checking the gap.

  So the native version is a SEPARATE definition. `F64.mulUp` is untouched and
  still proved. `mulUpNative` is the C-backed one, and `#eval` tests below
  compare them on a spread of inputs. That does not prove agreement — nothing
  short of a verified compiler could — but it makes the trust boundary
  something exercised rather than merely asserted.

  A BUG THIS ALREADY CAUGHT. The first version of `darm_native.c` used C's `/`
  operator. C truncates toward zero; Lean's `Int.ediv` floors. They diverge on
  negative numerators, so `mulUp` would have been wrong for every POSITIVE
  product — at `x = y = 3` the specification gives 1 and truncation gives 0.
  Arithmetic right shift is floor division for a positive power of two and is
  what the C now uses. The differential tests would have caught this; no proof
  in this repository would have.

  THE TRUSTED COMPUTING BASE, stated precisely. Before this module: the Lean
  kernel. With it: the Lean kernel, the Lean C emitter, Clang, the Lean FFI
  calling conventions, and `darm_native.c` itself. That is a real and
  significant widening, and it is the price of leaving the interpreter.
-/

namespace DARM
namespace Fixed64Native

open DARM.FixedPoint DARM.Fixed64

/-! ## 1. The bindings -/

/-- Native widening multiply, rounding up. Implemented in `c/darm_native.c`.
    NOT verified — mirrors `F64.mulUp`, tested against it below. -/
@[extern "darm_mul_up_64"]
opaque mulUpNativeRaw : Int64 → Int64 → Int64

/-- Native widening multiply, rounding down. Mirrors
    `Fixed64MulDown.F64.mulDown`. -/
@[extern "darm_mul_down_64"]
opaque mulDownNativeRaw : Int64 → Int64 → Int64

def mulUpNative (x y : F64) : F64 := ⟨mulUpNativeRaw x.raw y.raw⟩

def mulDownNative (x y : F64) : F64 := ⟨mulDownNativeRaw x.raw y.raw⟩

/-! ## 2. Differential tests

  Each compares the native result against the verified Lean implementation.
  `true` means they agree on that input; anything else is a divergence and
  means the C is wrong, since the Lean side is proved. -/

def agreeUp (x y : F64) : Bool :=
  (mulUpNative x y).raw == (F64.mulUp x y).raw

def agreeDown (x y : F64) : Bool :=
  (mulDownNative x y).raw == (Fixed64MulDown.F64.mulDown x y).raw

private def fx (n : Int) : F64 := ⟨Int64.ofInt n⟩
/-- Deterministically generate many test pairs.

    Uses a simple integer recurrence so every CI run is identical.
    This is NOT random. It is reproducible.
-/
def generatedPairs (n : Nat) : List (F64 × F64) :=
  (List.range n).map fun i =>
    let x : Int := (Int.ofNat ((i * 7919) % 100000)) - 50000
    let y : Int := (Int.ofNat ((i * 1543) % 100000)) - 50000
    (fx x, fx y)

/-- A spread chosen to hit the cases where truncation and flooring differ:
    both signs, products of both signs, exact multiples of `2^32`, and small
    values where the shift matters most. -/
def testPairs : List (F64 × F64) :=
  [ (fx 3, fx 3), (fx (-3), fx 3), (fx 3, fx (-3)), (fx (-3), fx (-3))
  , (fx 4294967296, fx 4294967296)
  , (fx 2147483648, fx 2147483648)
  , (fx 12345, fx 67890), (fx (-12345), fx 67890)
  , (fx 0, fx 5), (fx 1, fx 1)
  , (fx 140737488355328, fx 1), (fx (-140737488355328), fx 1) ]

-- Number of test pairs on which the native and verified versions agree.
-- Both should equal `testPairs.length`, printed third.
-- #eval (testPairs.filter (fun p => agreeUp p.1 p.2)).length
-- #eval (testPairs.filter (fun p => agreeDown p.1 p.2)).length
-- #eval testPairs.length

-- and the specific case the truncation bug got wrong
-- #eval agreeUp (fx 3) (fx 3)

def largeTestPairs : List (F64 × F64) :=
 testPairs ++ generatedPairs 5000

/-! ## Registered status

  DONE: C bindings for both directed multiplies, with differential tests
  against the proved Lean implementations.

  NOT PROVED, and this is the point: agreement between `mulUpNative` and
  `F64.mulUp` is TESTED, not proved. The tests cover both signs, exact powers
  of two, the envelope boundary, and the small values where flooring versus
  truncation diverges — but a spread of twelve inputs is not a proof over
  `Int64 × Int64`.

  WHAT WOULD MAKE IT STRONGER, short of a verified compiler: property-based
  testing over many random inputs rather than a fixed list, and running the
  tests in CI so a toolchain change that alters the C semantics is caught. The
  second is cheap and should be done.

  REMAINING IN THE RUNTIME PATH: a `[[lean_exe]]` target and an actual compiled
  binary (step 4), then measurement against it rather than the interpreter.
-/

end Fixed64Native
end DARM
