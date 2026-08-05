/*
  darm_native.c — widening fixed-point multiply for DARM.

  TRUST BOUNDARY. Nothing proves this function matches the Lean specification
  it mirrors. It is asserted to, and exercised against the verified version by
  the differential tests in `DarmMonitor/Fixed64Native.lean`. Testing is not
  proof: a divergence outside the tested inputs would not be caught.

  This file, the C compiler, and the Lean FFI conventions are in the trusted
  computing base. The verified Lean modules are unaffected by a bug here — but
  a monitor built on this function would not be.

  THE SPECIFICATION, from `Fixed64.lean` and `Fixed64MulDown.lean`:

      F64.mulUp   x y = Int64.ofInt (-((-(x.raw * y.raw)) / 2^32))
      F64.mulDown x y = Int64.ofInt (  (x.raw * y.raw)    / 2^32)

  where `/` is `Int.ediv` — EUCLIDEAN division, which for a positive divisor is
  FLOOR division.

  A BUG THIS FILE ALREADY HAD, recorded because it is the whole reason the
  differential test exists. A first version used C's `/` operator. C truncates
  toward zero; Lean floors. They agree on non-negative numerators and diverge
  on negative ones — so `mulUp` would have been wrong for every positive
  product. At x = y = 3 the specification gives 1 and the truncating version
  gives 0.

  Arithmetic right shift IS floor division for a positive power of two, on
  every target Clang supports, so `>>` is used instead of `/`. This is the
  correct primitive, not a micro-optimisation.

  `HardwarePort.prod_within_int128` proves the 128-bit intermediate never
  overflows for any Int64 inputs, which is why __int128_t suffices.
*/

#include <stdint.h>

/* k = 32, matching FixedPoint.k */
#define DARM_SHIFT 32

/* Rounds toward positive infinity: ceil(x*y / 2^32).
   ceil(a/m) = -floor(-a/m), and floor by a power of two is an arithmetic
   right shift. */
int64_t darm_mul_up_64(int64_t x, int64_t y) {
    __int128_t prod = (__int128_t)x * (__int128_t)y;
    __int128_t q    = (-prod) >> DARM_SHIFT;   /* floor(-prod / 2^32) */
    return (int64_t)(-q);
}

/* Rounds toward negative infinity: floor(x*y / 2^32). */
int64_t darm_mul_down_64(int64_t x, int64_t y) {
    __int128_t prod = (__int128_t)x * (__int128_t)y;
    return (int64_t)(prod >> DARM_SHIFT);      /* floor(prod / 2^32) */
}
