import DarmMonitor.A5RedundancyRational

/-
  A5Discharged — the remaining `hZ` sites, with the hypothesis discharged.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT THIS FINISHES. `Assumptions.lean` listed re-parameterizing the kernel
  theorems on A5 as NEXT, and warned it was not uniformly mechanical — the
  exponential and rational updates behave differently. This handles the sites
  that take the EXPONENTIAL form `hZ : 0 < Z (reweight η loss w)`, where
  `A5Redundancy.hZ_of_A5` applies directly.

  THE PREDICTION, AND IT HELD. All five sites — two in `StratumComposition`,
  one each in `Ratification`, `Reachability` and `GuardStability` — take `hZ`
  in the same form and in a position where the A5 form substitutes without
  further work. Each variant below is one application.

  WHAT IS DELIBERATELY NOT HERE. Sites taking `0 < Z w'` over an ARBITRARY
  vector — `BoundaryCore.safeZ_iff_safePost`, `BoundaryCore.transport_gen`,
  `Feasibility`, `ReachabilityExact` — cannot be discharged this way, because
  there is no `reweight` structure to exploit and A5 says nothing about an
  arbitrary `w'`. Those are correctly stated with the hypothesis explicit, and
  no A5 variant is possible.

  So the re-parameterization splits three ways: exponential sites (here),
  rational sites (`A5RedundancyRational`, conditional on the domain), and
  generic sites (not dischargeable at all).
-/

namespace DARM
namespace A5Discharged

open DARM.Boundary DARM.Assumptions DARM.Composition DARM.Ratification
open DARM.A5Redundancy

variable {n : ℕ} {CapId Token : Type} [DecidableEq CapId] [DecidableEq Token]

/-! ## 1. Cross-stratum coherence -/

/-- `coherence_preserved_under_agent_event` with `hZ` discharged by A5. -/
theorem coherence_preserved_under_agent_event_of_A5
    (requires : Fin n → CapId) (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop) [DecidablePred validToken]
    (s : State CapId (Fin n)) (e : Event CapId (Fin n) Token)
    (δ η : ℝ) (loss w : Fin n → ℝ)
    (hAgent : actor e = Actor.agent)
    (hw : WellFormedWeights w)
    (hsafe : is_safe_signal_Z δ η loss w)
    (hcoh : IsCoherent s δ w) :
    IsCoherent (step requires allowedCapLimit validToken s e) δ
      (DARM.Boundary.normalize (reweight η loss w) (Z (reweight η loss w))) :=
  coherence_preserved_under_agent_event requires allowedCapLimit validToken s e
    δ η loss w hAgent (hZ_of_A5 η loss hw) hsafe hcoh

/-- `coherence_preserved_under_suspend` with `hZ` discharged by A5. -/
theorem coherence_preserved_under_suspend_of_A5
    (requires : Fin n → CapId) (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop) [DecidablePred validToken]
    (s : State CapId (Fin n))
    (δ η : ℝ) (loss w : Fin n → ℝ)
    (hw : WellFormedWeights w)
    (hsafe : is_safe_signal_Z δ η loss w) :
    IsCoherent (step requires allowedCapLimit validToken s Event.externalSuspend) δ
      (DARM.Boundary.normalize (reweight η loss w) (Z (reweight η loss w))) :=
  coherence_preserved_under_suspend requires allowedCapLimit validToken s
    δ η loss w (hZ_of_A5 η loss hw) hsafe

/-! ## 2. Ratifiable set expansion -/

/-- `safe_update_expands_ratifiable_set` with `hZ` discharged by A5. -/
theorem safe_update_expands_ratifiable_set_of_A5
    (δ η : ℝ) (loss w : Fin n → ℝ)
    (hw : WellFormedWeights w)
    (hsafe : is_safe_signal_Z δ η loss w) :
    Ratifiable δ w
      ⊆ Ratifiable δ (DARM.Boundary.normalize (reweight η loss w)
          (Z (reweight η loss w))) :=
  safe_update_expands_ratifiable_set δ η loss w (hZ_of_A5 η loss hw) hsafe

/-! ## 3. Guard stability -/

/-- `guard_preserved_by_safe_update` with `hZ` discharged by A5. This is the
    form an operator wants: well-formed weights, a safe update, and a granted
    policy stays granted — nothing else to verify. -/
theorem guard_preserved_by_safe_update_of_A5
    (δ η : ℝ) (loss w : Fin n → ℝ)
    (hw : WellFormedWeights w)
    (hsafe : is_safe_signal_Z δ η loss w)
    (p : Finset (Fin n))
    (hguard : GuardedRatification δ w p) :
    GuardedRatification δ
      (DARM.Boundary.normalize (reweight η loss w) (Z (reweight η loss w))) p :=
  DARM.GuardStability.guard_preserved_by_safe_update δ η loss w
    (hZ_of_A5 η loss hw) hsafe p hguard

/-! ## Registered status

  DONE: every exponential-form `hZ` site now has an A5 variant. Together with
  `A5Redundancy.safe_signal_equiv_of_A5`, that is the boundary calculus stated
  so a deployment satisfying A5 has no positivity obligation left.

  THE THREE-WAY SPLIT, which is the actual finding. `Assumptions.lean` warned
  the re-parameterization was not uniformly mechanical, and it is not — but the
  non-uniformity is cleaner than expected:

    * EXPONENTIAL sites — discharged unconditionally (this module)
    * RATIONAL sites — discharged given the domain condition, and A5 alone is
      provably insufficient (`A5RedundancyRational`)
    * GENERIC sites, over an arbitrary post-update vector — not dischargeable,
      and correctly stated with the hypothesis explicit

  The third category is not a gap. `BoundaryCore.safeZ_iff_safePost` is about
  two arbitrary vectors and A5 constrains only the first; there is nothing to
  discharge.
-/

end A5Discharged
end DARM

#print axioms DARM.A5Discharged.coherence_preserved_under_agent_event_of_A5
#print axioms DARM.A5Discharged.coherence_preserved_under_suspend_of_A5
#print axioms DARM.A5Discharged.safe_update_expands_ratifiable_set_of_A5
#print axioms DARM.A5Discharged.guard_preserved_by_safe_update_of_A5
