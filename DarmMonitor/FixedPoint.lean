import DarmMonitor.Runtime

/-
  FixedPoint — a computable, conservative refinement of the boundary
  certificate, with a fail-closed simulation theorem.

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`.

  THE PROBLEM. `is_safe_signal_Z` quantifies over `ℝ`, and `Real` in Lean is a
  quotient of Cauchy sequences with no code generation, so `reweight`,
  `normalize`, `active`, and `Ratifiable` are all `noncomputable`. The boundary
  certificate cannot be extracted, and re-implementing it in C would place
  unverified arithmetic between the proofs and the binary.

  THE RESOLUTION. Do not extract the real specification. Build a computable
  fixed-point model inside Lean and prove that passing the computable check
  IMPLIES the real condition. Rounding then costs conservatism, never safety.

  DIRECTION OF CONSERVATISM. Safety is a LOWER bound on each coordinate:

      is_safe_signal_Z δ η loss w  :=  ∀ i ∈ active δ w, δ * Z ≤ w' i

  so a conservative check must demand MORE than the real condition: the
  requirement `δ * Z` is rounded UP, the coordinate `w'` is rounded DOWN.
  Shifting the threshold down instead — `Z - ε` — makes the check easier to
  pass and is fail-OPEN.

  THIS APPLIES TO THE MULTIPLICATION ITSELF, which is easy to miss. A first
  draft of this module used floor division for the fixed-point product, on the
  reasoning that truncation "under-approximates". It does — and the product is
  on the REQUIREMENT side, so under-approximating it reintroduces exactly the
  fail-open error one level down. `Fixed.mulUp` rounds the product up.

  ERROR SOURCES, AND WHICH SURVIVE.
    (a) representation, per coordinate: `2^-k`. Survives, and is the caller's
        obligation — supplied as the hypotheses `δr ≤ γ δfx` etc.
    (b) accumulation in `Z`, which sums over ι. Does NOT arise as a separate
        term: `Fixed.add` is exact (`gamma_add`), so summing introduces no
        error beyond the inputs' own. See `gamma_sum_le`. This is a correction
        to the natural guess that `Z` accumulates `|ι| * 2^-k` of ARITHMETIC
        error; the `|ι|` factor is entirely in the inputs.
    (c) truncation in the product. Eliminated by construction — `mulUp` rounds
        the wrong way for an attacker, so there is nothing left to bound.

  WHY `Int` AND NOT `Int64`. `Int64` is modular, so every lemma would carry a
  no-overflow side condition, and `Z` is a sum over ι — exactly where overflow
  bites. Proving the error algebra over arbitrary-precision `Int` keeps this
  theorem about the mathematics. Porting to `Int64` with explicit range
  hypotheses is the right next step and a separately statable result, and is
  what shrinks the FFI layer. Registered as open below.
-/

namespace DARM
namespace FixedPoint

open DARM.Boundary

/-! ## 1. Representation

  `k` is a module constant, not a type parameter: parameterizing introduces
  dependent-type friction in the sum manipulations for no gain here. -/

/-- Fractional bits. -/
def k : ℕ := 32

/-- A fixed-point value: an integer read as `raw * 2^-k`. -/
structure Fixed where
  raw : Int
deriving DecidableEq, Repr

/-- **The embedding into the reals.** Every claim below is ultimately about `γ`. -/
noncomputable def γ (x : Fixed) : ℝ := (x.raw : ℝ) / (2 ^ k : ℝ)

lemma scale_pos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity

/-! ## 2. Arithmetic -/

/-- Addition. Exact: no shift, no truncation. -/
def Fixed.add (x y : Fixed) : Fixed := ⟨x.raw + y.raw⟩

/-- **Addition is exact under `γ`.** No error term at all. -/
theorem gamma_add (x y : Fixed) : γ (Fixed.add x y) = γ x + γ y := by
  unfold γ Fixed.add
  push_cast
  ring

/-- Multiplication rounding the result UP.

    Ceiling division expressed through floor: `⌈a/b⌉ = -⌊-a/b⌋`. Lean's `/` on
    `Int` is Euclidean, which coincides with floor for a positive divisor.
    Upward is the conservative direction because the product lands on the
    requirement side of the safety inequality. -/
def Fixed.mulUp (x y : Fixed) : Fixed :=
  ⟨-((-(x.raw * y.raw)) / (2 ^ k))⟩

/-- **The product over-approximates.** `γ (mulUp x y) ≥ γ x * γ y`.

    This is what removes truncation from the error budget: the fixed-point
    product is never smaller than the real one, so rounding cannot let an
    unsafe state through. -/
theorem gamma_mulUp_ge (x y : Fixed) : γ x * γ y ≤ γ (Fixed.mulUp x y) := by
  have hb : (2 ^ k : Int) ≠ 0 := by positivity
  have hM : (0 : ℝ) < (2 ^ k : ℝ) := scale_pos
  -- the division identity: b * (a / b) + a % b = a, with the remainder nonneg
  have hid := Int.mul_ediv_add_emod (-(x.raw * y.raw)) (2 ^ k)
  have hnn := Int.emod_nonneg (-(x.raw * y.raw)) hb
  have hkey : (x.raw * y.raw : Int)
      ≤ (2 ^ k : Int) * (-((-(x.raw * y.raw)) / (2 ^ k))) := by linarith
  have hcast : ((x.raw : ℝ) * (y.raw : ℝ))
      ≤ (2 ^ k : ℝ) * (((-((-(x.raw * y.raw)) / (2 ^ k))) : Int) : ℝ) := by
    exact_mod_cast hkey
  unfold γ Fixed.mulUp
  rw [le_div_iff₀ hM]
  have hsimp : (x.raw : ℝ) / (2 ^ k : ℝ) * ((y.raw : ℝ) / (2 ^ k : ℝ)) * (2 ^ k : ℝ)
      = (x.raw : ℝ) * (y.raw : ℝ) / (2 ^ k : ℝ) := by
    field_simp
  rw [hsimp, div_le_iff₀ hM]
  linarith

/-- Summing fixed-point values. Exact, by `gamma_add`. -/
def Fixed.sum (l : List Fixed) : Fixed := l.foldr Fixed.add ⟨0⟩

/-- **Conservative accumulation.** Two fixed-point values dominating two reals
    give a sum dominating the sum, with no error contributed by the addition.

    Stated pairwise; the list version follows by induction and is not needed for
    the refinement theorem. The point is that `Fixed.add` is exact, so a sum
    over `ι` accumulates only the inputs' own representation error — not an
    additional `|ι| * 2^-k` of arithmetic error, which is the natural guess. -/
theorem gamma_add_le (x y : Fixed) (a b : ℝ) (ha : a ≤ γ x) (hb : b ≤ γ y) :
    a + b ≤ γ (Fixed.add x y) := by
  rw [gamma_add]
  linarith

/-! ## 3. The conservative check and the refinement theorem -/

/-- **The computable certificate, one coordinate.**

    `δ ⊗ Z + margin ≤ w`, entirely in fixed point, with the product rounded up.
    `margin` is an optional additional buffer; `0` suffices for soundness. -/
def checkSafeCoord (δfx Zfx wfx marginfx : Fixed) : Bool :=
  decide ((Fixed.mulUp δfx Zfx).raw + marginfx.raw ≤ wfx.raw)

/-- **Fail-closed refinement.**

    If the computable check passes, and the fixed-point values bound the reals
    in the conservative directions, then the real inequality `δ * Z ≤ w` holds.

    Rounding can make this check REJECT a state that is safe in ℝ — a false
    negative, acceptable. It cannot make the check ACCEPT a state unsafe in ℝ.
    That is the fail-closed property, and it is what licenses running the
    computable check in place of the real one. -/
theorem refinement_coord
    (δfx Zfx wfx marginfx : Fixed) (δr Zr wr : ℝ)
    (hδ : δr ≤ γ δfx) (hZ : Zr ≤ γ Zfx)
    (hδnn : 0 ≤ δr) (hZnn : 0 ≤ Zr)
    (hw : γ wfx ≤ wr)
    (hmargin : 0 ≤ γ marginfx)
    (hcheck : checkSafeCoord δfx Zfx wfx marginfx = true) :
    δr * Zr ≤ wr := by
  -- the check, transported to ℝ
  have hraw : (Fixed.mulUp δfx Zfx).raw + marginfx.raw ≤ wfx.raw :=
    of_decide_eq_true hcheck
  have hcast : (((Fixed.mulUp δfx Zfx).raw : ℝ) + (marginfx.raw : ℝ))
      ≤ (wfx.raw : ℝ) := by exact_mod_cast hraw
  have hgam : γ (Fixed.mulUp δfx Zfx) + γ marginfx ≤ γ wfx := by
    unfold γ
    rw [← sub_nonneg]
    have heq :
        (wfx.raw : ℝ) / (2 ^ k : ℝ)
          - (((Fixed.mulUp δfx Zfx).raw : ℝ) / (2 ^ k : ℝ)
             + (marginfx.raw : ℝ) / (2 ^ k : ℝ))
        = ((wfx.raw : ℝ)
            - (((Fixed.mulUp δfx Zfx).raw : ℝ) + (marginfx.raw : ℝ))) / (2 ^ k : ℝ) := by
      field_simp
    rw [heq]
    apply div_nonneg _ (by positivity)
    linarith
  -- the real product is dominated by the fixed-point operands' product
  have hprod : δr * Zr ≤ γ δfx * γ Zfx := by
    have h1 : δr * Zr ≤ γ δfx * Zr := mul_le_mul_of_nonneg_right hδ hZnn
    have h2 : γ δfx * Zr ≤ γ δfx * γ Zfx :=
      mul_le_mul_of_nonneg_left hZ (le_trans hδnn hδ)
    linarith
  -- and the fixed-point product over-approximates it
  have hmul := gamma_mulUp_ge δfx Zfx
  linarith

/-! ## 4. It runs -/

/-- `1.0` in fixed point. -/
def one : Fixed := ⟨2 ^ k⟩

/-- `0.25` in fixed point. -/
def quarter : Fixed := ⟨2 ^ k / 4⟩

/-- `0.5` in fixed point. -/
def half : Fixed := ⟨2 ^ k / 2⟩

-- δ = 1/4, Z = 1, w = 1/2:  requirement 1/4 ≤ 1/2, passes.
#eval checkSafeCoord quarter one half ⟨0⟩

-- δ = 1/2, Z = 1, w = 1/4:  requirement 1/2 ≤ 1/4, fails.
#eval checkSafeCoord half one quarter ⟨0⟩

-- with a margin, the first case tightens toward rejection
#eval checkSafeCoord quarter one half quarter

/-! ## Registered status

  DONE: the computable check runs, and `refinement_coord` proves it fail-closed
  against the real condition. Truncation error is eliminated by construction
  (`gamma_mulUp_ge`) rather than bounded; addition is exact
  (`gamma_add`), so summation contributes no arithmetic error of its own.

  NOT DONE, and each is real:
    * `Int64`. The port is what makes `@[export]` emit primitive C types and
      keeps the FFI layer thin, but it needs no-overflow hypotheses threaded
      through, and `Z` is a sum. Separate result.
    * The quantified form. `refinement_coord` is one coordinate;
      `is_safe_signal_Z` quantifies over the active set, and the active set
      itself is `noncomputable`. A computable surrogate for membership is
      needed before the quantified refinement can even be stated.
    * The FFI boundary. Lean's emitted C uses its runtime, boxing and reference
      counting. The marshalling glue is hand-written and unverified, so the
      honest TCB is: Lean kernel + Lean C emitter + C compiler + that glue.
      Smaller than a hand-written monitor; not zero.
-/

end FixedPoint
end DARM

#print axioms DARM.FixedPoint.gamma_add
#print axioms DARM.FixedPoint.gamma_add_le
#print axioms DARM.FixedPoint.gamma_mulUp_ge
#print axioms DARM.FixedPoint.refinement_coord
