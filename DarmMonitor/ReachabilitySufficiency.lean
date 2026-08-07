import DarmMonitor.ReachabilityExact

/-
  ReachabilitySufficiency — the constructive half of R1b.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT REMAINED. `ReachabilityExact` proved two halves of R1b:
    * the reweighting channel is surjective onto positive vectors, so R1b is a
      question about achievable active sets rather than about the update rule;
    * necessity is sharp — a proper subset `B` requires `δ * |B| < 1`.

  This module supplies sufficiency: given `δ * |B| < 1`, a weight vector whose
  active set is exactly `B`.

  THE CONSTRUCTION.  v = 1 on B, v = ε off B, with

      ε = (1 - δ * |B|) / (2 * δ * n)      where n = |univ|

  Then `Z = |B| + (n - |B|) * ε` and the two obligations are:

      i ∈ B  stays active     ⟺  δ * Z ≤ 1
      i ∉ B  stays inactive   ⟺  δ * Z > ε

  For the first: `δ * (n - |B|) * ε ≤ δ * n * ε = (1 - δ|B|)/2`, so
  `δ * Z ≤ δ|B| + (1 - δ|B|)/2 = (1 + δ|B|)/2 < 1`.
  For the second: `δ * Z ≥ δ * |B| > ε`, which needs `ε < δ|B|` — supplied by
  `hεsmall` below rather than derived, since it constrains how small `δ|B|` may
  be relative to `n`. See the honest note on that hypothesis.

  WHAT THIS DOES AND DOES NOT CLOSE. Together with surjectivity, a weight-vector
  witness lifts immediately to a `loss` witness, so R1b's sufficiency direction
  is established for targets satisfying `hεsmall`. The fully unconditional
  statement — sufficiency from `δ * |B| < 1` alone — is NOT proved here; see the
  registered status at the end.
-/

namespace DARM
namespace ReachabilitySufficiency

open DARM.Boundary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The witness vector: unit mass on the target, `ε` elsewhere. -/
noncomputable def witness (B : Finset ι) (ε : ℝ) : ι → ℝ :=
  fun i => if i ∈ B then 1 else ε

lemma witness_pos {B : Finset ι} {ε : ℝ} (hε : 0 < ε) (i : ι) :
    0 < witness B ε i := by
  unfold witness
  split <;> [norm_num; exact hε]

/-- The partition function of the witness splits by membership. -/
lemma Z_witness (B : Finset ι) (ε : ℝ) :
    Z (witness B ε) = (B.card : ℝ) + ((Finset.univ \ B).card : ℝ) * ε := by
  have hsplit : ∀ i : ι, witness B ε i = (if i ∈ B then (1:ℝ) else ε) := fun _ => rfl
  simp only [Z, hsplit, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : Finset.univ.filter (fun i => i ∈ B) = B := by
    ext i; simp
  have h2 : Finset.univ.filter (fun i => i ∉ B) = Finset.univ \ B := by
    ext i; simp [Finset.mem_sdiff]
  rw [h1, h2]

/-- **Sufficiency.** If the margin floor admits `B` — that is, `δ * Z` of the
    witness stays at or below 1 while exceeding `ε` — then the active set of
    the witness is exactly `B`.

    The two margin hypotheses are the obligations named in the header, stated
    directly rather than derived, so the arithmetic of choosing `ε` is separated
    from the set-theoretic content.

    `0 < δ` is required and was missing from an earlier draft: without it,
    `hout : ε < δ * Z` is satisfiable with `Z ≤ 0` and `δ < 0`, so the
    positivity of the partition function does not follow. A negative margin
    floor is meaningless anyway, but the proof needs it stated. -/
theorem active_witness_eq
    (B : Finset ι) (δ ε : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hin : δ * Z (witness B ε) ≤ 1)
    (hout : ε < δ * Z (witness B ε)) :
    active δ (DARM.Boundary.normalize (witness B ε) (Z (witness B ε))) = B := by
  have hZpos : 0 < Z (witness B ε) := by
    by_contra h
    push_neg at h
    nlinarith [hε, hδ, hout]
  ext i
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold DARM.Boundary.normalize
  rw [le_div_iff₀ hZpos]
  constructor
  · -- active ⇒ in B: otherwise the coordinate is ε, contradicting hout
    intro h
    by_contra hB
    unfold witness at h
    rw [if_neg hB] at h
    unfold witness at hout
    linarith
  · -- in B ⇒ active: the coordinate is 1, and hin gives δ * Z ≤ 1
    intro hB
    unfold witness
    rw [if_pos hB]
    exact hin

/-- The choice of `ε` that discharges the first obligation. Stated as a lemma
    so the arithmetic is separable from `active_witness_eq`. -/
theorem eps_choice_bounds
    (B : Finset ι) (δ : ℝ) (hδ : 0 < δ)
    (hcap : δ * (B.card : ℝ) < 1)
    (hn : 0 < (Fintype.card ι : ℝ)) :
    δ * Z (witness B ((1 - δ * (B.card : ℝ)) / (2 * δ * (Fintype.card ι : ℝ)))) ≤ 1 := by
  set ε := (1 - δ * (B.card : ℝ)) / (2 * δ * (Fintype.card ι : ℝ)) with hεdef
  have hεpos : 0 < ε := by
    apply div_pos (by linarith) (by positivity)
  rw [Z_witness]
  have hcard : ((Finset.univ \ B).card : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Finset.card_le_univ (Finset.univ \ B)
  have hkey : δ * (((Finset.univ \ B).card : ℝ) * ε) ≤ (1 - δ * (B.card : ℝ)) / 2 := by
    have h1 : δ * (((Finset.univ \ B).card : ℝ) * ε)
        ≤ δ * ((Fintype.card ι : ℝ) * ε) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      exact mul_le_mul_of_nonneg_right hcard hεpos.le
    have h2 : δ * ((Fintype.card ι : ℝ) * ε) = (1 - δ * (B.card : ℝ)) / 2 := by
      rw [hεdef]
      field_simp
    linarith
  nlinarith

/-! ## Registered status of R1b

  CLOSED:
    * Surjectivity of the reweighting channel (`ReachabilityExact`).
    * Necessity, sharply: a proper subset requires `δ * |B| < 1`
      (`ReachabilityExact`).
    * Sufficiency, given the two margin obligations: `active_witness_eq` shows
      the witness realizes exactly `B`.
    * The `ε` choice discharging the first obligation: `eps_choice_bounds`.

 CLOSED, 2026-08-07. The second obligation IS satisfiable simultaneously with
  the first — see `ReachabilityClosed.lean`. Taking

      ε = min( (1 - δm)/(2δk),  δm/2 )

  discharges both for every admissible input, so `δ * |B| < 1` is sufficient as
  well as necessary and the biconditional holds.

  WHAT THIS FILE PREVIOUSLY RECORDED, AND WHY IT WAS WRONG. It said the
  conjecture "may in fact be false at the small-δ|B| end", on the grounds that
  `eps_choice_bounds`' ε violates the second obligation there. That much is
  true and still is. But nothing followed about OTHER choices of ε, and the
  note crossed from "this construction fails" to "the statement may be false" —
  a gap of exactly one existential quantifier. The doubt was an error of
  inference, not a feature of the mathematics.
-/

end ReachabilitySufficiency
end DARM

#print axioms DARM.ReachabilitySufficiency.witness_pos
#print axioms DARM.ReachabilitySufficiency.Z_witness
#print axioms DARM.ReachabilitySufficiency.active_witness_eq
#print axioms DARM.ReachabilitySufficiency.eps_choice_bounds
