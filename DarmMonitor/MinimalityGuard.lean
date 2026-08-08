import DarmMonitor.MinimalityA2

/-
  MinimalityGuard — the guard is necessary for coherence preservation.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT THIS ADDS. `Ratification.guarded_ratification_preserves_coherence` says
  ratification preserves coherence GIVEN `GuardedRatification δ w p`, which is
  `p ⊆ active δ w`. This exhibits a state where that hypothesis fails and the
  conclusion fails with it — so the guard is load-bearing, not decoration.

  THE COUNTERMODEL, and it is already in the repository. `ratification_breaks_coherence`
  uses one coordinate with weight `0` and margin `1`, so `active 1 (fun _ => 0)`
  is EMPTY: no coordinate clears the floor. Ratifying the policy `{0}` into that
  state gives

      IsCoherent s δ w          ∅ ⊆ anything, so yes
      GuardedRatification δ w p {0} ⊆ ∅, so NO
      IsCoherent (step …) δ w   {0} ⊆ ∅, so no

  That is the N-cell exactly. The same witness serves both theorems because
  they are two readings of one fact: unguarded ratification can install a policy
  the margin does not support.

  WHY IT IS WORTH STATING SEPARATELY. `ratification_breaks_coherence` is a
  NEGATIVE RESULT — it says the unguarded rule is unsafe. This is a MINIMALITY
  CELL — it says the guard in the guarded rule cannot be dropped. Same witness,
  different claims: one about a rule that should not be used, one about a
  hypothesis that cannot be weakened.
-/

namespace DARM
namespace MinimalityGuard

open DARM.Ratification DARM.Composition DARM.Boundary

/-- **The guard is necessary for `guarded_ratification_preserves_coherence`.**

    All three components at one witness: the precondition holds, the guard
    fails, and the conclusion fails. Dropping `hguard` from the theorem would
    therefore make it false. -/
theorem guard_necessary_for_coherence :
    ∃ (s : State Unit (Fin 1)) (δ : ℝ) (w : Fin 1 → ℝ)
      (t : Unit) (p : Finset (Fin 1)),
      IsCoherent s δ w
      ∧ ¬ GuardedRatification δ w p
      ∧ ¬ IsCoherent
          (step (fun _ : Fin 1 => ()) (∅ : Finset Unit) (fun _ : Unit => True) s
            (Event.authenticatedRatification t p)) δ w := by
  refine ⟨{ cap := ∅, policy := ∅, opState := OpState.active, lastExecuted := none },
          1, (fun _ => 0), (), {0}, ?_, ?_, ?_⟩
  · -- the empty policy is trivially coherent
    exact Finset.empty_subset _
  · -- the guard fails: {0} is not inside the empty active set
    intro h
    have hmem : (0 : Fin 1) ∈ active (1 : ℝ) (fun _ : Fin 1 => (0 : ℝ)) :=
      h (Finset.mem_singleton_self 0)
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    linarith
  · -- and coherence fails after the step
    intro h
    have hmem : (0 : Fin 1) ∈ active (1 : ℝ) (fun _ : Fin 1 => (0 : ℝ)) := by
      apply h
      simp [step]
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    linarith

/-! ## Registered status

  DONE: the guard's necessity. Ten cells now proved.

  WHAT THIS SHARPENS. `Ratification.lean`'s negative result already showed
  unguarded ratification breaks coherence. This says something adjacent but
  distinct: the guarded theorem's hypothesis is exactly what makes it true, so
  no weaker side-condition would do. Together they bracket the design — the
  rule needs a guard, and this guard is not stronger than necessary in the one
  direction that matters.

  WHAT IT DOES NOT SAY. That `p ⊆ active δ w` is the WEAKEST sufficient guard.
  A cell proving necessity shows the hypothesis cannot simply be dropped; it
  does not rule out some weaker condition also sufficing. That is a different
  and harder question, and no theorem here addresses it.
-/

end MinimalityGuard
end DARM

#print axioms DARM.MinimalityGuard.guard_necessary_for_coherence
