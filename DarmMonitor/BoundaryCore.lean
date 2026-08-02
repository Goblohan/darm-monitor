import DarmMonitor.Feasibility

/-
  BoundaryCore — the boundary theorems over an arbitrary post-update vector,
  and a formal account of what the exponential update buys.

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`.

  THE OBSERVATION. None of the four theorems in `BoundaryMargin.lean` unfolds
  `reweight`. `safe_signal_equiv` is `δ * Z ≤ w'ᵢ ↔ δ ≤ w'ᵢ / Z`, pure algebra
  over a positive scalar. `transportSupp` cites it. `is_safe_signal_Z_iff_Z_le_min`
  rearranges an infimum. The update appears only as an opaque term.

  So the boundary calculus is not about multiplicative weights at all. It is
  about a PAIR of vectors — a pre-update `w` fixing the active set, and a
  post-update `w'` that must clear the margin floor. This module states it that
  way and recovers the existing theorems as instances.

  WHY THIS IS NOT A LICENCE TO REPLACE `exp`. A rational surrogate
  `w / (1 + η * loss)` is computable exactly, which is tempting, and it fails on
  two counts that the abstraction makes precise rather than removing:

    SEMIGROUP. `exp (-a) * exp (-b) = exp (-(a + b))`, so a loss stream may be
    batched or streamed and reach the same state. The rational form does not
    satisfy this — `exp_semigroup` and `rational_not_semigroup` below prove both
    halves. For a monitor consuming telemetry, the boundary would depend on
    clock-cycle chunking. That is state-drift, not rounding.

    SINGULARITY. `exp` is positive on all of ℝ. The rational form blows up at
    `η * loss = -1` and goes negative below it, invalidating the non-negativity
    hypothesis the capacity bounds need. A global guarantee becomes conditional.

  A third objection — that swapping the update degrades the `O(√(T ln N))`
  regret bound of multiplicative weights — does NOT apply here, and the reason
  is worth recording. This development contains no regret, no comparator, no
  loss sequence, and no horizon. `reweight` is a single-step function. Nothing
  proved depends on it being the mirror-descent solution. That is precisely why
  the abstraction below goes through.

  CONCLUSION. Abstract the interface; keep `exp` as the primary instance. The
  surrogate is admissible only where losses are non-negative and history
  independence is not required.
-/

namespace DARM
namespace BoundaryCore

open DARM.Boundary

variable {ι : Type*} [Fintype ι]

/-! ## 1. The certificate over an arbitrary post-update vector

  `w` fixes the active set; `w'` must clear the floor. No relation between them
  is assumed. -/

/-- Scalar certificate: the margin floor times the total mass is affordable at
    every coordinate that was active before the update. -/
def SafeZ (δ : ℝ) (w w' : ι → ℝ) : Prop :=
  ∀ i ∈ active δ w, δ * Z w' ≤ w' i

/-- Geometric floor: after normalization, every previously-active coordinate is
    still at or above `δ`. -/
def SafePost (δ : ℝ) (w w' : ι → ℝ) : Prop :=
  ∀ i ∈ active δ w, δ ≤ DARM.Boundary.normalize w' (Z w') i

/-- **The O(n) → O(1) collapse, with no update rule in sight.**

    Generalizes `safe_signal_equiv`. The proof is the same division
    rearrangement; the exponential never entered it. -/
theorem safeZ_iff_safePost (δ : ℝ) (w w' : ι → ℝ) (hZ : 0 < Z w') :
    SafeZ δ w w' ↔ SafePost δ w w' := by
  unfold SafeZ SafePost DARM.Boundary.normalize
  constructor
  · intro h i hi
    rw [le_div_iff₀ hZ]
    have := h i hi
    linarith
  · intro h i hi
    have := h i hi
    rw [le_div_iff₀ hZ] at this
    linarith

/-- **Support transport, generalized.** Every coordinate active before the
    update is active after it. -/
theorem transport_gen (δ : ℝ) (w w' : ι → ℝ) (hZ : 0 < Z w')
    (hsafe : SafeZ δ w w') :
    active δ w ⊆ active δ (DARM.Boundary.normalize w' (Z w')) := by
  have hpost : SafePost δ w w' := (safeZ_iff_safePost δ w w' hZ).mp hsafe
  intro i hi
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hpost i hi

/-- **The scalar bound against the minimum active mass, generalized.** -/
theorem safeZ_iff_Z_le_min (δ : ℝ) (w w' : ι → ℝ) (hδ : 0 < δ)
    (hne : (active δ w).Nonempty) :
    SafeZ δ w w' ↔ Z w' ≤ ((active δ w).inf' hne (fun i => w' i)) / δ := by
  unfold SafeZ
  rw [le_div_iff₀ hδ]
  constructor
  · intro h
    rw [mul_comm]
    refine Finset.le_inf' hne _ (fun i hi => ?_)
    have := h i hi
    linarith
  · intro h i hi
    have hmin : (active δ w).inf' hne (fun i => w' i) ≤ w' i := Finset.inf'_le _ hi
    rw [mul_comm] at h
    linarith

/-! ## 2. The existing results are instances

  Nothing is lost by generalizing: substituting the multiplicative-weights
  update recovers each original statement. -/

theorem safe_signal_equiv_from_core (δ η : ℝ) (loss w : ι → ℝ)
    (hZ : 0 < Z (reweight η loss w)) :
    is_safe_signal_Z δ η loss w ↔ is_safe_signal_post δ η loss w :=
  safeZ_iff_safePost δ w (reweight η loss w) hZ

theorem transportSupp_from_core (δ η : ℝ) (loss w : ι → ℝ)
    (hZ : 0 < Z (reweight η loss w))
    (hsafe : is_safe_signal_Z δ η loss w) :
    active δ w ⊆ active δ (DARM.Boundary.normalize (reweight η loss w)
      (Z (reweight η loss w))) :=
  transport_gen δ w (reweight η loss w) hZ hsafe

/-! ## 3. What the exponential buys: the semigroup property -/

/-- **`exp` composes.** Two updates applied in sequence equal one update on the
    summed loss, so a loss stream may be batched arbitrarily. -/
theorem exp_semigroup (a b : ℝ) :
    Real.exp (-a) * Real.exp (-b) = Real.exp (-(a + b)) := by
  rw [← Real.exp_add]
  ring_nf

/-- The rational surrogate: computable exactly, singular at `-1`. -/
noncomputable def ratUpdate (x : ℝ) : ℝ := 1 / (1 + x)

/-- Positive exactly on the domain `x > -1`. -/
theorem ratUpdate_pos (x : ℝ) (hx : -1 < x) : 0 < ratUpdate x := by
  unfold ratUpdate
  apply div_pos one_pos
  linarith

/-- **The rational surrogate does NOT compose.** At `a = b = 1` the sequential
    product is `1/4` and the batched update is `1/3`.

    This is the decisive objection to replacing `exp`. Under this update a
    monitor's boundary would depend on how a loss stream happened to be chunked
    across clock cycles — state drift, not approximation error. It also makes
    trace-level composition strictly harder, since two safe updates would no
    longer collapse into one. -/
theorem rational_not_semigroup :
    ratUpdate 1 * ratUpdate 1 ≠ ratUpdate (1 + 1) := by
  unfold ratUpdate
  norm_num

/-- **And it is not globally positive.** Below `-1` the update flips sign,
    breaking the non-negativity hypothesis every capacity bound requires. -/
theorem ratUpdate_neg_below : ratUpdate (-2) < 0 := by
  unfold ratUpdate
  norm_num

/-! ## Registered status

  ESTABLISHED. The boundary calculus is independent of the update rule. It
  relates a pre-update vector fixing the active set to a post-update vector
  clearing the floor, and needs only positivity of the total mass. The four
  original theorems are instances.

  CONSEQUENCE FOR THE RUNTIME. The approximation layer — `ExpEvaluator`,
  `BracketTightening`, `EvaluatorTower` — exists to bracket a transcendental
  function that the boundary theorems never required. Any instance with an
  exactly-computable update needs none of it. That is a real simplification for
  targets that can accept the trade below.

  THE TRADE, now proved rather than argued. `exp` is the only one of the two
  that composes (`exp_semigroup` versus `rational_not_semigroup`) and the only
  one positive everywhere (`ratUpdate_neg_below`). So the surrogate is
  admissible only where losses are bounded below and history independence is not
  needed. `exp` remains primary.

  NOT DONE. `BoundaryMargin.lean` still states its theorems in terms of
  `reweight` rather than citing these. Migrating it is mechanical and would let
  the `exp`-specific forms be deleted, but it cascades through every downstream
  module and re-earns their axiom traces. Deferred deliberately.

  ALSO OPEN. Whether an exactly-computable update exists that DOES satisfy the
  semigroup property. `exp` is the unique continuous solution of
  `f(a) * f(b) = f(a + b)` up to a scale factor in the exponent, so over ℝ the
  answer is no. Over a fixed-point or modular representation the question is
  different and has not been examined.
-/

end BoundaryCore
end DARM

#print axioms DARM.BoundaryCore.safeZ_iff_safePost
#print axioms DARM.BoundaryCore.transport_gen
#print axioms DARM.BoundaryCore.safeZ_iff_Z_le_min
#print axioms DARM.BoundaryCore.safe_signal_equiv_from_core
#print axioms DARM.BoundaryCore.exp_semigroup
#print axioms DARM.BoundaryCore.rational_not_semigroup
#print axioms DARM.BoundaryCore.ratUpdate_neg_below
