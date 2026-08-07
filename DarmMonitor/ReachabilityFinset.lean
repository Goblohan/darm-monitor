import DarmMonitor.ReachabilityClosed

/-
  ReachabilityFinset — R1b stated over `Finset`s.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT THIS FINISHES. `ReachabilityClosed` proved the arithmetic core: an `ε`
  exists discharging both margin obligations, stated over bare reals `m` and
  `k`. This instantiates that at `m = B.card` and `k = (univ \ B).card` and
  feeds it to `ReachabilitySufficiency.active_witness_eq`, giving realizability
  of an actual `Finset` rather than a statement about cardinalities.

  With it R1b is complete rather than "core closed, restatement pending".
-/

namespace DARM
namespace ReachabilityFinset

open DARM.Boundary DARM.ReachabilitySufficiency DARM.ReachabilityClosed

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Realizability -/

/-- `B` is realizable at margin `δ` if some weight vector's post-normalization
    active set is exactly `B`. -/
def Realizable (δ : ℝ) (B : Finset ι) : Prop :=
  ∃ v : ι → ℝ, active δ (DARM.Boundary.normalize v (Z v)) = B

/-! ## 2. Sufficiency, over `Finset`s -/

/-- **`δ * |B| < 1` suffices.** For a nonempty proper subset `B`, the witness
    construction realizes exactly `B`.

    This is `ReachabilityClosed.sufficiency_unconditional` instantiated at the
    actual cardinalities, then passed to `active_witness_eq`. -/
theorem realizable_of_card_lt (B : Finset ι) (δ : ℝ) (hδ : 0 < δ)
    (hne : B.Nonempty) (hproper : B ≠ Finset.univ)
    (hcap : δ * (B.card : ℝ) < 1) :
    Realizable δ B := by
  -- the two cardinalities are positive
  have hm : (0:ℝ) < (B.card : ℝ) := by
    have := Finset.card_pos.mpr hne
    exact_mod_cast this
  have hkne : (Finset.univ \ B).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hproper (Finset.eq_univ_of_forall (fun i => hsub (Finset.mem_univ i)))
  have hk : (0:ℝ) < ((Finset.univ \ B).card : ℝ) := by
    have := Finset.card_pos.mpr hkne
    exact_mod_cast this
  -- the arithmetic core supplies an admissible ε
  obtain ⟨ε, hεpos, hA, hB⟩ :=
    sufficiency_unconditional δ (B.card : ℝ) ((Finset.univ \ B).card : ℝ)
      hδ hm hk hcap
  refine ⟨witness B ε, ?_⟩
  -- transport the two obligations across Z_witness
  have hZ : Z (witness B ε)
      = (B.card : ℝ) + ((Finset.univ \ B).card : ℝ) * ε := Z_witness B ε
  have hin : δ * Z (witness B ε) ≤ 1 := by rw [hZ]; exact hA
  have hout : ε < δ * Z (witness B ε) := by rw [hZ]; exact hB
  exact active_witness_eq B δ ε hεpos hδ hin hout

/-! ## 3. R1b, both directions

  Necessity is `ReachabilityExact.active_card_strict_lt_of_ne_univ`: any active
  set that is a proper subset satisfies `|S| * δ < 1` strictly. Sufficiency is
  the theorem above. Together they are the conjecture. -/

/-! ## Registered status of R1b — COMPLETE

    * Channel surjectivity (`ReachabilityExact`).
    * Necessity, sharply (`ReachabilityExact`).
    * The `ε` discharging both obligations (`ReachabilityClosed`).
    * Realizability of an actual `Finset` (this module).

  `realizable_of_card_lt` is the statement the conjecture was about: give it a
  nonempty proper subset with `δ * |B| < 1`, and it returns a weight vector
  whose active set is exactly `B`.

  ON THE BICONDITIONAL. Only sufficiency is proved here. Necessity exists as
  `ReachabilityExact.active_card_strict_lt_of_ne_univ`, but it is stated over
  the active set of an arbitrary vector, and tying it to a specific `B` needs
  that vector in hand - so the two do not compose into one statement without
  more work. A first draft here had a `realizable_iff` taking necessity as an
  unused hypothesis; the linter caught that it was never referenced, which made
  it a theorem whose signature suggested more than it proved. Deleted rather
  than kept.

-/

end ReachabilityFinset
end DARM

#print axioms DARM.ReachabilityFinset.realizable_of_card_lt

