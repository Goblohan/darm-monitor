import DarmMonitor.Assumptions

/-
  Minimality — necessity and independence cells for the assumption matrix.

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`.

  WHAT A CELL IS. The Dependency Atlas proposes a matrix recording, for each
  theorem, which hypotheses are necessary (N) and which are independent (I).
  Sufficiency is the theorem itself and needs no separate work. NECESSITY is
  the content: a hypothesis is necessary only if there is a model where it
  fails and the conclusion fails with it. Without such a countermodel, an "N"
  is an assertion.

  ON "INDEPENDENT" CELLS. Now that assumptions are explicit hypotheses rather
  than prose, independence is usually visible in the signature: A1 does not
  appear in `execution_confined_by_cap_bound`, so it is trivially independent
  of it. Such cells are real but carry no information beyond the statement.
  Only cells where an assumption is *implicitly* in play — via a shared model
  rather than a hypothesis — are worth a theorem. Recorded here so the matrix
  does not inflate its count with signature-reading.

  CELLS PROVED IN THE KERNEL SO FAR:
    N  A5 (non-negativity) for the capacity bound
         -- Assumptions.A5_nonneg_necessary
    I  A1 for coherence preservation
         -- Assumptions.A1_insufficient_for_coherence
         Non-trivial: A1 does not appear as a hypothesis, but one might
         expect the ratification counterexample to depend on the degenerate
         token predicate. It does not.
    N  is_safe_signal_Z for support transport
         -- this module, below
-/

namespace DARM
namespace Minimality

open DARM.Boundary

private lemma Z_eval :
    Z (reweight (0 : ℝ) ![0, 0] (![3, 1] : Fin 2 → ℝ)) = 4 := by
  rw [DARM.StrictExpansion.reweight_zero_eta]
  norm_num [Z, Fin.sum_univ_two]

private lemma one_active_before :
    (1 : Fin 2) ∈ active (1/2 : ℝ) (![3, 1] : Fin 2 → ℝ) := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  norm_num

/-- **Necessity cell: the safety certificate cannot be dropped from
    `transportSupp`.**

    Witness: `w = (3, 1)`, `δ = 1/2`, `η = 0` (so the update is pure
    renormalization). Both coordinates start above the floor. Total mass is 4,
    so after normalization they are `3/4` and `1/4`, and coordinate 1 falls
    below `δ`. Support is not preserved.

    Safety fails for exactly the same reason it must: it demands
    `δ * Z ≤ W i` for every active `i`, and here `δ * Z = 2 > 1 = W 1`.

    Note the contrast with A5. Non-negativity is NOT necessary for
    `transportSupp` — that theorem carries no sign hypothesis, because
    post-update membership `δ ≤ W i / Z` is literally the safety condition
    `δ * Z ≤ W i` once `Z > 0`. Non-negativity only becomes load-bearing
    where the active coordinates are SUMMED, which is the capacity bound. -/
theorem safety_necessary_for_transport :
    ∃ (δ η : ℝ) (loss w : Fin 2 → ℝ),
      0 < Z (reweight η loss w) ∧
      ¬ is_safe_signal_Z δ η loss w ∧
      ¬ (active δ w ⊆
          active δ (DARM.Boundary.normalize
            (reweight η loss w) (Z (reweight η loss w)))) := by
  refine ⟨1/2, 0, ![0, 0], ![3, 1], ?_, ?_, ?_⟩
  · -- total mass is 4
    rw [Z_eval]; norm_num
  · -- safety fails at coordinate 1: it demands 2 ≤ 1
    intro hs
    have h := hs 1 one_active_before
    rw [Z_eval, DARM.StrictExpansion.reweight_zero_eta] at h
    norm_num at h
  · -- and support is genuinely lost: coordinate 1 drops to 1/4 < 1/2
    intro hsub
    have h := hsub one_active_before
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at h
    unfold DARM.Boundary.normalize at h
    rw [Z_eval, DARM.StrictExpansion.reweight_zero_eta] at h
    norm_num at h

/-! ## Next cells, in order of expected cost

  C2. Is `hAgent : actor e = Actor.agent` necessary for
      `coherence_preserved_under_agent_event`? Expected YES, and the
      countermodel already exists: `ratification_breaks_coherence` is a
      non-agent event that breaks coherence. The work is restating it as a
      necessity cell against the coherence theorem specifically.

  C3. Is `massPos` (the second half of A5) necessary for the capacity bound?
      UNCLEAR, and possibly NO. If `Z = 0` then Lean's division gives
      `normalize v 0 i = 0`, so for `δ > 0` the active set is empty and the
      bound holds vacuously. If so this is a "not necessary" result, which is
      worth recording precisely because it contradicts the natural guess.

  C4. A4 versus capability confinement. Blocked: `Influence.lean` and
      `Basic.lean` share no types, so there is no single model in which both
      A4 and `capInvariant` can be stated. This is the standing structural
      gap, not a missing proof.
-/

end Minimality
end DARM

#print axioms DARM.Minimality.safety_necessary_for_transport
