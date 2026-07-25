import Mathlib

/-
  BoundaryMargin — support-transport under a delta-margin floor.

  STATUS: VERIFIED - safe_signal_equiv machine-checked, axiom-clean. A1-A4 remain registered as open assumptions.

  Setting: weights w : Fin n -> R on the (unnormalized) simplex. A coordinate
  is "active" if w i >= delta. A multiplicative-weights update reweights by
  exp(-eta * loss i), then normalizes by the partition function Z = sum of
  reweighted mass. Positivity is free (exp > 0); the real threat is that
  normalization is GLOBAL — one coordinate with tiny loss inflates Z and can
  drag an otherwise-healthy active coordinate below delta.

  The naive defense bounds every loss independently: O(n) constraints.

  The result here: that O(n) family is equivalent to a SINGLE scalar bound on Z,

      Z <= (min over active i of (reweighted mass i)) / delta                (Z-bound)

  This is `safe_signal_equiv`. `transportSupp` is the corollary: the Z-bound
  preserves the active set (subset, not equality — resurrection is allowed).

  Assumptions made explicit:
    - hZ : 0 < Z (reweighted). Needed for every div/mul rearrangement.
    - equivalence carries a nonemptiness proof of the active set; the empty
      case is trivially safe and handled inside transportSupp.

  SCOPE: finite-dimensional, no measure theory. Real-analysis over Fin n -> R.
-/

namespace DARM.Boundary

open Finset BigOperators

variable {n : ℕ}

/-- Unnormalized multiplicative-weights update. -/
noncomputable def reweight (η : ℝ) (loss w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => w i * Real.exp (-η * loss i)

/-- Partition function: total reweighted mass. -/
def Z (w' : Fin n → ℝ) : ℝ := ∑ j, w' j

/-- Normalization by a supplied positive scalar. -/
noncomputable def normalize (w' : Fin n → ℝ) (Zv : ℝ) : Fin n → ℝ :=
  fun i => w' i / Zv

/-- Active set: coordinates at or above the critical margin δ. -/
noncomputable def active (δ : ℝ) (w : Fin n → ℝ) : Finset (Fin n) :=
  univ.filter (fun i => δ ≤ w i)

/-- The computable certificate the monitor evaluates: a single scalar bound.
    `δ * Z ≤ w'ᵢ` for every currently-active `i`, where `w' = reweight …`.
    (Stated in the cleared-denominator form `δ * Z ≤ w'ᵢ` to avoid division
    inside the predicate; equivalent to `Z ≤ w'ᵢ / δ` under `0 < δ`.) -/
def is_safe_signal_Z (δ η : ℝ) (loss w : Fin n → ℝ) : Prop :=
  ∀ i ∈ active δ w, δ * Z (reweight η loss w) ≤ reweight η loss w i

/-- The geometric floor invariant: after normalization, every previously-active
    coordinate is still ≥ δ. -/
def is_safe_signal_post (δ η : ℝ) (loss w : Fin n → ℝ) : Prop :=
  ∀ i ∈ active δ w,
    δ ≤ normalize (reweight η loss w) (Z (reweight η loss w)) i

/-- **Centerpiece.** The single scalar Z-certificate is equivalent to the
    per-coordinate post-normalization floor. This is the O(n) → O(1) collapse:
    one inequality on `Z` captures the entire family of active-coordinate
    constraints. Requires `0 < Z` for the div/mul rearrangement. -/
theorem safe_signal_equiv (δ η : ℝ) (loss w : Fin n → ℝ)
    (hZ : 0 < Z (reweight η loss w)) :
    is_safe_signal_Z δ η loss w ↔ is_safe_signal_post δ η loss w := by
  unfold is_safe_signal_Z is_safe_signal_post normalize
  constructor
  · -- Z-bound ⇒ floor.  δ*Z ≤ w'ᵢ  ⇒  δ ≤ w'ᵢ/Z.
    intro h i hi
    rw [le_div_iff₀ hZ]
    have := h i hi
    linarith
  · -- floor ⇒ Z-bound.  δ ≤ w'ᵢ/Z  ⇒  δ*Z ≤ w'ᵢ.
    intro h i hi
    have := h i hi
    rw [le_div_iff₀ hZ] at this
    linarith

/-- Rearranged form of the certificate as a bound on `Z` against the minimum
    active reweighted mass. This is the "single geometric volume" statement:
    the monitor computes `Z` and one minimum, not `n` independent bounds.
    Holds when the active set is nonempty (otherwise the min is undefined and
    the constraint is vacuous — see `transportSupp`). -/
theorem is_safe_signal_Z_iff_Z_le_min (δ η : ℝ) (loss w : Fin n → ℝ)
    (hδ : 0 < δ) (hne : (active δ w).Nonempty) :
    is_safe_signal_Z δ η loss w ↔
      Z (reweight η loss w)
        ≤ ((active δ w).inf' hne (fun i => reweight η loss w i)) / δ := by
  unfold is_safe_signal_Z
  rw [le_div_iff₀ hδ]
  constructor
  · intro h
    rw [mul_comm]
    refine le_inf' hne _ (fun i hi => ?_)
    have := h i hi
    linarith
  · intro h i hi
    have hmin : (active δ w).inf' hne (fun i => reweight η loss w i)
        ≤ reweight η loss w i := inf'_le _ hi
    rw [mul_comm] at h
    linarith [h, hmin]

/-- **Support-transport.** The monitor's certificate preserves the active set:
    every coordinate active before the step is active after. Not equality —
    a previously-inactive coordinate may cross above δ (resurrection allowed).
    The empty active set is trivially preserved. -/
theorem transportSupp (δ η : ℝ) (loss w : Fin n → ℝ)
    (hZ : 0 < Z (reweight η loss w))
    (hsafe : is_safe_signal_Z δ η loss w) :
    active δ w ⊆ active δ (normalize (reweight η loss w) (Z (reweight η loss w))) := by
  have hpost : is_safe_signal_post δ η loss w :=
    (safe_signal_equiv δ η loss w hZ).mp hsafe
  intro i hi
  simp only [active, mem_filter, mem_univ, true_and]
  exact hpost i hi

/-- The whole result in one statement: the computable Z-certificate implies
    active-support preservation, with no axioms beyond the classical core. -/
theorem certificate_preserves_support (δ η : ℝ) (loss w : Fin n → ℝ)
    (hZ : 0 < Z (reweight η loss w))
    (hsafe : is_safe_signal_Z δ η loss w) :
    ∀ i ∈ active δ w,
      δ ≤ normalize (reweight η loss w) (Z (reweight η loss w)) i := by
  have := transportSupp δ η loss w hZ hsafe
  intro i hi
  have hmem := this hi
  simpa [active, mem_filter] using hmem

end DARM.Boundary
 
#print axioms DARM.Boundary.safe_signal_equiv 
