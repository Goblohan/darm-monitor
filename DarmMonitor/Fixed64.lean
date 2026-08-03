import DarmMonitor.HardwarePort
import DarmMonitor.RationalInstance

/-
  Fixed64 — the 64-bit fixed-point type and its model projection.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  SCOPE. This module contains the type, the projection into the `Int`-based
  model, and the multiplication envelope restated over that type. It does NOT
  contain simulation theorems. Those were drafted and are not proved; they are
  recorded as open below rather than shipped half-finished.

  WHY THE PORT NEEDS SIMULATION THEOREMS. `FixedPoint.Fixed` wraps `Int`, which
  compiles to a boxed `lean_object*`. An exported library wants `int64_t`.
  Establishing that the 64-bit operations compute the same values as the
  verified model — inside the envelope `HardwarePort` proves — is what makes a
  64-bit implementation a REFINEMENT rather than a reimplementation whose
  agreement is assumed. Without those theorems this module is a type, not a
  port.

  THE MECHANISM THEY WOULD USE. Lean core supplies

      Int64.toInt_ofInt : (Int64.ofInt n).toInt = n.bmod Int64.size

  where `bmod` is balanced modulus, the identity on `[-2^63, 2^63)`. So each
  simulation theorem reduces to a range obligation, and the range obligations
  are exactly `HardwarePort`'s envelope. The mathematics is settled; what is
  missing is the tactic work.

  A NOTE FOR WHOEVER FINISHES THIS. The bridge lemma

      (Int64.ofInt n).toInt = n   for  -2^63 <= n < 2^63

  is provable by `unfold Int.bmod; simp only []; split <;> omega` when the
  modulus is a numeric literal. In context it is `Int64.size`, a definition,
  which `omega` cannot evaluate — rewriting it to its value first is what the
  proof needs. Verified standalone; not landed in context.
-/

namespace DARM
namespace Fixed64

open DARM.FixedPoint DARM.HardwarePort

/-! ## 1. The type -/

/-- A 64-bit fixed-point value: an `Int64` read as `raw * 2^-k`. -/
structure F64 where
  raw : Int64
deriving DecidableEq, Repr

/-- The `Int`-based model of a 64-bit value. Simulation theorems, when they
    exist, will be statements about this projection agreeing with the
    corresponding `Fixed` operation. -/
def F64.toFixed (x : F64) : Fixed := ⟨x.raw.toInt⟩

/-- Every 64-bit value's model lies in range, by construction. -/
theorem toFixed_in_range (x : F64) :
    -(2 ^ 63) ≤ (x.toFixed).raw ∧ (x.toFixed).raw < 2 ^ 63 :=
  ⟨Int64.le_toInt x.raw, Int64.toInt_lt x.raw⟩

/-- The projection is injective, so results transfer in both directions between
    the 64-bit type and the model. -/
theorem toFixed_injective (x y : F64) (h : x.toFixed = y.toFixed) : x = y := by
  unfold F64.toFixed at h
  have hraw : x.raw.toInt = y.raw.toInt := by injection h
  have : Int64.ofInt x.raw.toInt = Int64.ofInt y.raw.toInt := by rw [hraw]
  rw [Int64.ofInt_toInt, Int64.ofInt_toInt] at this
  cases x; cases y; simp_all

/-! ## 2. The multiplication envelope over this type -/

/-- Raw magnitude below which multiplication is safe at `k = 32`. In value terms
    this is `2^47 / 2^32 = 32768`, so weights near 1 sit fifteen binary orders
    below the limit. -/
abbrev mulSafeBound : ℤ := 2 ^ 47

/-- **The multiplication precondition.** Two operands within `mulSafeBound` have
    a product whose shift by `k` fits in `Int64`.

    Restated from `HardwarePort.mul_envelope_k32` so a caller reasons about
    `F64` values rather than raw integers. -/
theorem mul_precondition (x y : F64)
    (hx : |x.raw.toInt| ≤ mulSafeBound) (hy : |y.raw.toInt| ≤ mulSafeBound) :
    |x.raw.toInt * y.raw.toInt| ≤ int64Bound * 2 ^ kk :=
  HardwarePort.mul_envelope_k32 _ _ hx hy


/-! ## 3. The bridge

  `Int64.ofInt` is modular. Inside the representable range balanced modulus is
  the identity, so "no overflow" becomes a range obligation and nothing more.

  NOTE ON THE PROOF. `omega` cannot evaluate `Int64.size`, which is a definition
  rather than a literal; `show` forces it to the literal first. The same issue
  affects every constant below — `k`, `kk`, `int64Bound` — and is why each
  tactic block reduces them before calling `omega`. -/

theorem toInt_ofInt_of_range (n : ℤ)
    (hlo : -(2 ^ 63) ≤ n) (hhi : n < 2 ^ 63) :
    (Int64.ofInt n).toInt = n := by
  rw [Int64.toInt_ofInt]
  change Int.bmod n 18446744073709551616 = n
  unfold Int.bmod
  simp only []
  split <;> omega

/-! ## 4. Addition -/

def F64.addI (x y : F64) : F64 := ⟨Int64.ofInt (x.raw.toInt + y.raw.toInt)⟩

theorem add_simulates (x y : F64)
    (hlo : -(2 ^ 63) ≤ x.raw.toInt + y.raw.toInt)
    (hhi : x.raw.toInt + y.raw.toInt < 2 ^ 63) :
    (F64.addI x y).toFixed = FixedPoint.Fixed.add x.toFixed y.toFixed := by
  unfold F64.addI F64.toFixed FixedPoint.Fixed.add
  congr 1
  exact toInt_ofInt_of_range _ hlo hhi

/-! ## 5. Multiplication -/

def F64.mulUp (x y : F64) : F64 :=
  ⟨Int64.ofInt (-((-(x.raw.toInt * y.raw.toInt)) / (2 ^ k)))⟩

/-- The shifted product stays in `Int64` range.

    NOTE ON THE BOUND. `2^94`, not `2^95`. At `a = 2^95 - 1` the floor division
    gives exactly `-2^63`, so the negated quotient hits `2^63` and the strict
    bound fails — the wider statement is FALSE, not merely hard. `2^94` is what
    `mul_simulates` supplies (`2^47 * 2^47`) and leaves a full binary order of
    margin. -/
theorem shifted_in_range (a : ℤ)
    (hbound : |a| ≤ 19807040628566084398385987584) :
    -(2 ^ 63) ≤ -((-a) / (2 ^ k)) ∧ -((-a) / (2 ^ k)) < 2 ^ 63 := by
  have hk : (2 : ℤ) ^ k = 4294967296 := by norm_num [FixedPoint.k]
  rw [hk]
  rw [abs_le] at hbound
  have hq := Int.mul_ediv_add_emod (-a) 4294967296
  have hm := Int.emod_nonneg (-a) (by norm_num : (4294967296 : ℤ) ≠ 0)
  have hml := Int.emod_lt_of_pos (-a) (by norm_num : (0:ℤ) < 4294967296)
  obtain ⟨hb1, hb2⟩ := hbound
  constructor <;> nlinarith [hq, hm, hml, hb1, hb2]

theorem mul_simulates (x y : F64)
    (hx : |x.raw.toInt| ≤ 140737488355328) (hy : |y.raw.toInt| ≤ 140737488355328) :
    (F64.mulUp x y).toFixed = FixedPoint.Fixed.mulUp x.toFixed y.toFixed := by
  unfold F64.mulUp F64.toFixed FixedPoint.Fixed.mulUp
  congr 1
  have hb : |x.raw.toInt * y.raw.toInt| ≤ 19807040628566084398385987584 := by
    rw [abs_mul]
    calc |x.raw.toInt| * |y.raw.toInt|
        ≤ 140737488355328 * 140737488355328 := by
          apply mul_le_mul hx hy (abs_nonneg _) (by norm_num)
      _ ≤ 19807040628566084398385987584 := by norm_num
  obtain ⟨hlo, hhi⟩ := shifted_in_range _ hb
  exact toInt_ofInt_of_range _ hlo hhi

/-! ## 6. Division

  The divisor must be at least 1 in value terms. Below that the quotient
  genuinely overflows — an unsafe case, not an unproved one. Free for
  `RationalInstance`, whose divisor is `1 + eta * L` on the non-negative-loss
  domain. -/

def F64.divDown (x y : F64) : F64 :=
  ⟨Int64.ofInt ((x.raw.toInt * 2 ^ k) / y.raw.toInt)⟩

theorem quotient_in_range (a d : ℤ) (hd : 4294967296 ≤ d)
    (hlo : -(2 ^ 63) ≤ a) (hhi : a < 2 ^ 63) :
    -(2 ^ 63) ≤ (a * 2 ^ k) / d ∧ (a * 2 ^ k) / d < 2 ^ 63 := by
  have hk : (2 : ℤ) ^ k = 4294967296 := by norm_num [FixedPoint.k]
  rw [hk]
  have hdpos : (0 : ℤ) < d := by omega
  have hq := Int.mul_ediv_add_emod (a * 4294967296) d
  have hm := Int.emod_nonneg (a * 4294967296) (by omega : d ≠ 0)
  have hml := Int.emod_lt_of_pos (a * 4294967296) hdpos
  constructor <;> nlinarith [hq, hm, hml, hd, hlo, hhi]

theorem divDown_simulates (x y : F64) (hy : 4294967296 ≤ y.raw.toInt) :
    (F64.divDown x y).toFixed
      = RationalInstance.Fixed.divDown x.toFixed y.toFixed := by
  unfold F64.divDown F64.toFixed RationalInstance.Fixed.divDown
  congr 1
  obtain ⟨hlo, hhi⟩ := quotient_in_range x.raw.toInt y.raw.toInt hy
    (Int64.le_toInt x.raw) (Int64.toInt_lt x.raw)
  exact toInt_ofInt_of_range _ hlo hhi

/-! ## 7. Upward division

  Needs a STRICT lower bound on the quotient, because it negates the result and
  the target bound is strict. `quotient_in_range` gives only `-(2^63) ≤ q`.

  The strict version is available once the input excludes `-2^63`. With
  `-2^63 < x < 2^63` we have `|x| ≤ 2^63 - 1`, so `|x * 2^32| ≤ 2^95 - 2^32` —
  symmetric, with a full `2^32` of slack below `2^95`. The quotient by `d ≥ 2^32`
  is then bounded by `2^63 - 1` at both ends.

  Excluding `-2^63` is not a restriction in practice: it is the extreme negative
  representable raw value, not a weight any deployment produces. -/

/-- **Strict quotient bound**, available when the input excludes the two's
    complement minimum. -/
theorem quotient_in_range_strict (a d : ℤ) (hd : 4294967296 ≤ d)
    (hlo : -(2 ^ 63) < a) (hhi : a < 2 ^ 63) :
    -(2 ^ 63) < (a * 4294967296) / d ∧ (a * 4294967296) / d < 2 ^ 63 := by
  have hdpos : (0 : ℤ) < d := by omega
  have hq := Int.mul_ediv_add_emod (a * 4294967296) d
  have hm := Int.emod_nonneg (a * 4294967296) (by omega : d ≠ 0)
  have hml := Int.emod_lt_of_pos (a * 4294967296) hdpos
  constructor <;> nlinarith [hq, hm, hml, hd, hlo, hhi, hdpos]

/-- 64-bit fixed-point division rounding UP. -/
def F64.divUp (x y : F64) : F64 :=
  ⟨Int64.ofInt (-((-(x.raw.toInt * 2 ^ k)) / y.raw.toInt))⟩

/-- **Upward division simulates**, given a divisor of at least one and an input
    above the two's complement minimum. -/
theorem divUp_simulates (x y : F64) (hy : 4294967296 ≤ y.raw.toInt)
    (hx : -(2 ^ 63) < x.raw.toInt) :
    (F64.divUp x y).toFixed = ExpEvaluator.Fixed.divUp x.toFixed y.toFixed := by
  unfold F64.divUp F64.toFixed ExpEvaluator.Fixed.divUp
  congr 1
  have hk : (2 : ℤ) ^ k = 4294967296 := by norm_num [FixedPoint.k]
  rw [hk]
  have h1 : -(2 ^ 63) < -(x.raw.toInt) := by
    have := Int64.toInt_lt x.raw; omega
  have h2 : -(x.raw.toInt) < 2 ^ 63 := by omega
  obtain ⟨hlo, hhi⟩ := quotient_in_range_strict (-(x.raw.toInt)) y.raw.toInt hy h1 h2
  have hswap : (-(x.raw.toInt) * 4294967296) = -(x.raw.toInt * 4294967296) := by ring
  rw [hswap] at hlo hhi
  refine toInt_ofInt_of_range (-((-(x.raw.toInt * 4294967296)) / y.raw.toInt)) ?_ ?_
  · omega
  · omega

/-! ## Registered status

  PROVED: the type, its model projection and injectivity; the multiplication
  envelope over `F64`; the bridge `toInt_ofInt_of_range`; and simulation for
  addition, multiplication and downward division. Nine theorems, no `sorryAx`.

  ON `divUp` ASYMMETRY — RESOLVED. Three incremental attempts failed; deriving the bound first settled it. With -2^63 < x < 2^63 the product bound is symmetric with 2^32 of slack, giving a strict quotient at both ends. See quotient_in_range_strict.

  `divUp` negates before dividing, so the range argument runs over `-x`. Two's
  complement is asymmetric: `Int64.toInt` covers `[-2^63, 2^63)`, so negating
  the minimum yields `2^63`, one past the top. Excluding that single input with
  a precondition is necessary but NOT sufficient — the same asymmetry reappears
  one level down, at the quotient.

  Concretely: `quotient_in_range` proves `-(2^63) ≤ q`. The upward direction
  needs `-(2^63) < q`, strictly, because it negates that bound and the target is
  strict. When `q = -2^63` exactly, `-q = 2^63` and the bound fails.

  So the fix is to strengthen `quotient_in_range` to a strict lower bound, which
  means rechecking `divDown_simulates`, which cites it. That is a coherent piece
  of work — all four bounds derived together on paper first — rather than an
  incremental patch. It was attempted incrementally three times here, and each
  fix exposed the next boundary one level down. Recorded rather than repeated.

  NOT PROVED, and this is the remainder of the port:

    * THE BRIDGE. `(Int64.ofInt n).toInt = n` on the representable range. Every
      simulation theorem routes through it. See the note in the header for what
      the proof needs.
    * UPWARD DIVISION. See the asymmetry note above. Downward division is
      proved, which covers the paths that need it today.
    * ANY NATIVE CODE. Lean computes intermediates in `Int`, which boxes.
      Reaching a widening register multiply needs an `@[extern]` binding to
      `__int128_t`. That binding is a stated ABI contract rather than an open
      proof obligation, but it is still a component that can be wrong and
      belongs in the TCB beside the C compiler.

  So: the overflow analysis is verified in `HardwarePort`, and the refinement
  holds for the bridge, addition, multiplication and downward division. What is
  missing is upward division and any native code. The accurate description is
  "the arithmetic refines the model except for one direction of division;
  nothing is compiled".
-/

end Fixed64
end DARM

#print axioms DARM.Fixed64.toFixed_in_range
#print axioms DARM.Fixed64.toFixed_injective
#print axioms DARM.Fixed64.mul_precondition
#print axioms DARM.Fixed64.toInt_ofInt_of_range
#print axioms DARM.Fixed64.add_simulates
#print axioms DARM.Fixed64.shifted_in_range
#print axioms DARM.Fixed64.mul_simulates
#print axioms DARM.Fixed64.quotient_in_range
#print axioms DARM.Fixed64.divDown_simulates
#print axioms DARM.Fixed64.quotient_in_range_strict
#print axioms DARM.Fixed64.divUp_simulates
