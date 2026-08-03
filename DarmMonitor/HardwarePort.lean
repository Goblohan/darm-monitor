import DarmMonitor.RationalInstance

/-
  HardwarePort — the overflow envelope for a 64-bit fixed-point implementation.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHY THIS EXISTS. `FixedPoint.Fixed` wraps `Int`, which is arbitrary-precision
  and compiles to a boxed `lean_object*`. A callable library wants `int64_t` in
  the exported signature. Porting means every arithmetic lemma acquires a
  no-overflow side condition, and this module establishes what those conditions
  are BEFORE any code is rewritten.

  THE ARITHMETIC. At `k = 32`, a naive single-word product `x.raw * y.raw`
  overflows `Int64` once both operands exceed value 0.5, because
  `(2^32)^2 = 2^64 > 2^63`. That does not force a smaller `k`: 64-bit hardware
  computes fixed-point products through a widening multiply — `__int128_t` in
  C, `MULH`/`UMULH` in the instruction set — and shifts the 128-bit intermediate
  back down. The operating limit then comes from the OUTPUT fitting in `Int64`,
  not the intermediate.

  Lean has no `Int128` (checked: `#check Int128` fails). It does not need one:
  `Int` is arbitrary-precision, so an intermediate computed in `Int` is an exact
  specification of what a 128-bit register does, provided the value stays inside
  128-bit range. That containment is `prod_within_int128` below.

  WHAT THIS BUYS, AND WHAT IT DOES NOT. It reduces the trusted component to a
  single mapping: `Int` multiplication on a proved-bounded range, implemented as
  `__int128_t`. It does NOT eliminate it. Lean's code generator emits
  `lean_object*` with a GMP fallback for `Int`; getting a 128-bit register
  operation requires `@[extern]` or hand-written C, and that binding is
  unverified. The honest TCB for an exported build is

      Lean kernel + Lean C emitter + C compiler + the extern binding + marshalling glue

  which is smaller than an unproved multiply and is not zero. See the non-claims
  in the README.
-/

namespace DARM
namespace HardwarePort

open DARM.FixedPoint

/-! ## 1. The constants -/

/-- Fractional bits, matching `FixedPoint.k`. -/
abbrev kk : ℕ := 32

/-- Largest magnitude a signed 64-bit integer holds. -/
abbrev int64Bound : ℤ := 2 ^ 63

/-- Largest magnitude a signed 128-bit intermediate holds. -/
abbrev int128Bound : ℤ := 2 ^ 127

/-! ## 2. The intermediate never overflows 128 bits

  This is what licenses computing the product in `Int` and implementing it as
  `__int128_t`: on the whole `Int64` range, the exact product is representable. -/

/-- **The widening product is safe unconditionally.** Two operands each within
    the `Int64` range multiply to at most `2^126`, comfortably inside 128 bits.

    So no hypothesis is needed for the intermediate. Every constraint below
    comes from fitting the SHIFTED result back into 64 bits. -/
theorem prod_within_int128 (x y : ℤ)
    (hx : |x| < int64Bound) (hy : |y| < int64Bound) :
    |x * y| < int128Bound := by
  rw [abs_mul]
  calc |x| * |y| < int64Bound * int64Bound := by
        apply mul_lt_mul'' hx hy (abs_nonneg x) (abs_nonneg y)
    _ = 2 ^ 126 := by norm_num
    _ < int128Bound := by norm_num

/-! ## 3. The output constraint

  `mulUp` shifts the product right by `k`. The result must fit in `Int64`. -/

/-- **The multiplication envelope.** If both raw values are bounded by `B`, the
    shifted product fits in `Int64` provided `B^2 ≤ 2^63 * 2^k`.

    At `k = 32` this reads `B^2 ≤ 2^95`, so `B ≤ 2^47`, which in value terms is
    `2^47 / 2^32 = 2^15 = 32768`. Weights near 1 sit fifteen binary orders below
    the limit. -/
theorem mul_output_fits (x y B : ℤ) (hB : 0 ≤ B)
    (hx : |x| ≤ B) (hy : |y| ≤ B)
    (hcap : B * B ≤ int64Bound * 2 ^ kk) :
    |x * y| ≤ int64Bound * 2 ^ kk := by
  rw [abs_mul]
  calc |x| * |y| ≤ B * B := by
        apply mul_le_mul hx hy (abs_nonneg y) hB
    _ ≤ int64Bound * 2 ^ kk := hcap

/-- The concrete bound at `k = 32`: raw magnitude `2^47`, i.e. value `32768`. -/
theorem mul_envelope_k32 (x y : ℤ)
    (hx : |x| ≤ 2 ^ 47) (hy : |y| ≤ 2 ^ 47) :
    |x * y| ≤ int64Bound * 2 ^ kk := by
  refine mul_output_fits x y (2 ^ 47) (by positivity) hx hy ?_
  norm_num

/-! ## 4. The summation envelope

  `Z` sums over the index type; the bound couples dimension with magnitude. -/

/-- **The summation envelope.** A sum of `n` terms each bounded by `B` is
    bounded by `n * B`, so `Int64` safety needs `n * B < 2^63`.

    At `k = 32` and value magnitude 1 — raw `2^32` — this permits `n < 2^31`,
    which is not a practical constraint. Summation is the comfortable operation;
    multiplication is the binding one. -/
theorem sum_output_fits (n : ℕ) (B : ℤ) (v : ℕ → ℤ)
    (hB : ∀ i, |v i| ≤ B) (hBnn : 0 ≤ B)
    (hcap : (n : ℤ) * B < int64Bound) :
    |∑ i ∈ Finset.range n, v i| < int64Bound := by
  calc |∑ i ∈ Finset.range n, v i| ≤ ∑ i ∈ Finset.range n, |v i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, B := Finset.sum_le_sum (fun i _ => hB i)
    _ = (n : ℤ) * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ < int64Bound := hcap

/-! ## 5. Division

  `divUp` computes `x.raw * 2^k` before dividing, so the numerator is the
  binding term — the same shape as multiplication with one operand fixed at
  `2^k`. -/

/-- **The division envelope.** The pre-division numerator `x * 2^k` fits in
    128 bits whenever `x` fits in 64. As with multiplication, the constraint
    that matters is on the output, which is bounded by `x / y` and therefore by
    `x` itself when `|y| ≥ 2^k` (divisor at least 1 in value terms). -/
theorem div_numerator_within_int128 (x : ℤ) (hx : |x| < int64Bound) :
    |x * 2 ^ kk| < int128Bound := by
  refine prod_within_int128 x (2 ^ kk) hx ?_
  rw [abs_of_nonneg (by positivity : (0:ℤ) ≤ 2 ^ kk)]
  norm_num

/-! ## Registered status

  ESTABLISHED, and this is the answer to "can the port keep `k = 32`":

    * The 128-bit intermediate never overflows, for ANY pair of `Int64` inputs
      (`prod_within_int128`). No hypothesis required.
    * The binding constraint is the shifted OUTPUT. At `k = 32` it permits raw
      magnitude `2^47`, i.e. values up to 32768 (`mul_envelope_k32`). The
      earlier concern that `k = 32` caps values at 0.5 assumed a single-word
      intermediate and is wrong for real 64-bit hardware.
    * Summation is not the constraint: `n * B < 2^63` permits `n < 2^31` at unit
      magnitude.
    * Division reduces to multiplication with `2^k` as one operand.

  NOT ESTABLISHED, and worth being exact about. These are bounds on the
  ARITHMETIC. None of the following is done:

    * A `Fixed64` type and a simulation theorem showing its operations agree
      with `FixedPoint.Fixed` within the envelope. That is the next module and
      it is where the real work is.
    * Any `@[extern]` binding. Lean emits `lean_object*` for `Int`; a 128-bit
      register operation requires a C mapping that is not verified here.
    * Any measurement. "Unboxed" and "zero-alloc" are goals, not observations —
      nothing has been compiled to a binary and profiled.
-/

end HardwarePort
end DARM

#print axioms DARM.HardwarePort.prod_within_int128
#print axioms DARM.HardwarePort.mul_output_fits
#print axioms DARM.HardwarePort.mul_envelope_k32
#print axioms DARM.HardwarePort.sum_output_fits
#print axioms DARM.HardwarePort.div_numerator_within_int128
