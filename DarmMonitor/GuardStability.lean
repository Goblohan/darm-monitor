import DarmMonitor.ExpansionSubsumption

/-
  GuardStability — the guard is stable under safe updates.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT THIS CONNECTS. `Ratification.lean` defines two things that turn out to be
  the same condition:

      GuardedRatification δ w p  :=  p ⊆ active δ w
      Ratifiable δ w             :=  (active δ w).powerset

  `p ⊆ S` and `p ∈ S.powerset` are interchangeable, so the guard the monitor
  checks IS membership in the ratifiable set. That identity is not stated
  anywhere, and neither is its consequence.

  THE CONSEQUENCE. `safe_update_expands_ratifiable_set` proves `Ratifiable` only
  grows under a Z-safe update. Composed with the identity, that says: a policy
  which passed the guard still passes it after any Z-safe update. The guard
  never retroactively invalidates a policy it previously admitted.

  WHY THIS IS WORTH STATING SEPARATELY. `safe_update_expands_ratifiable_set` is
  about a powerset — a set of sets, one of which happens to be the current
  policy. This is about the check the monitor actually runs on the actual
  policy. Same mathematics, different reading, and the second is the one a
  deployment cares about: it says a granted authority is not silently revoked
  by the continuous stratum.

  HOW IT WAS FOUND. Not by looking for it. A minimality question about the
  expansion witnesses turned out to be malformed, and reading the neighbouring
  theorems to understand why surfaced this. Nothing in either module's
  registered status could have pointed at it, because each describes only
  itself.
-/

namespace DARM
namespace GuardStability

open DARM.Boundary DARM.Ratification

/-! ## 1. The guard is powerset membership -/

/-- **The two conditions coincide.** `GuardedRatification` is exactly membership
    in `Ratifiable`. -/
theorem guard_iff_ratifiable {n : ℕ} (δ : ℝ) (w : Fin n → ℝ) (p : Finset (Fin n)) :
    GuardedRatification δ w p ↔ p ∈ Ratifiable δ w := by
  unfold GuardedRatification Ratifiable
  rw [Finset.mem_powerset]

/-! ## 2. Stability -/

/-- **A policy that passed the guard still passes it after a Z-safe update.**

    Immediate from `transportSupp`: the active set only grows, so a subset of
    it stays a subset. Stated because it is the operational form — the monitor
    checks the guard, not powerset membership, and this says that check cannot
    turn from pass to fail through a legitimate continuous update. -/
theorem guard_preserved_by_safe_update {n : ℕ} (δ η : ℝ) (loss w : Fin n → ℝ)
    (hZ : 0 < Z (reweight η loss w))
    (hsafe : is_safe_signal_Z δ η loss w)
    (p : Finset (Fin n))
    (hguard : GuardedRatification δ w p) :
    GuardedRatification δ
      (DARM.Boundary.normalize (reweight η loss w) (Z (reweight η loss w))) p := by
  unfold GuardedRatification at hguard ⊢
  exact hguard.trans (transportSupp δ η loss w hZ hsafe)

/-! ## Registered status

  DONE: the identity between the guard and ratifiable-set membership, and the
  stability corollary that follows from it plus
  `safe_update_expands_ratifiable_set`.

  WHAT THIS DOES NOT SAY. That the guard is stable under ARBITRARY updates —
  only under Z-safe ones. An unsafe update can shrink the active set and
  invalidate a previously-granted policy, which is precisely why the safety
  certificate is required. `MinimalityGuard` and `Minimality.safety_necessary_for_transport`
  cover the other side of that.

  THE METHODOLOGICAL POINT. This was found while investigating a minimality
  question that turned out to be malformed. Two definitions in one file were
  the same condition; nobody had written the equation. Per-module registered
  statuses cannot surface that kind of relationship, because each describes
  only its own module. Whether other such pairs exist across the other
  forty-eight modules has not been checked, and there is no cheap way to check
  it.
-/

end GuardStability
end DARM

#print axioms DARM.GuardStability.guard_iff_ratifiable
#print axioms DARM.GuardStability.guard_preserved_by_safe_update
