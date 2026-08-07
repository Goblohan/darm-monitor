import DarmMonitor.Assumptions
import DarmMonitor.Ratification
import DarmMonitor.StratumComposition

/-
  MinimalityA1 — A1 is not load-bearing for the guarded ratification theorem.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  THE OPEN ITEM THIS CLOSES. `Assumptions.lean`'s registered status lists
  "A1 (decision above)" as open: A1 is formalized, satisfiable, exhibited
  failing for the trivial predicate, and proved INDEPENDENT of coherence
  preservation — but no cell says whether it is NECESSARY for anything.

  THE ANSWER IS NO, and the reason is visible in the proof rather than the
  statement. `guarded_ratification_preserves_coherence` takes `validToken` as a
  parameter carrying no unforgeability hypothesis, and its proof splits on
  token validity with both branches closing — the valid branch by the guard,
  the invalid branch by prior coherence. Nothing inspects what `validToken`
  actually accepts.

  So the theorem survives instantiation at the predicate where A1 fails. That
  is a negative minimality cell, the same shape as
  `Minimality.massPos_not_necessary_for_capacity`.

  WHAT THIS DOES AND DOES NOT SAY. It does not say A1 is a bad assumption. A
  deployed monitor genuinely needs unforgeable tokens; without them an attacker
  ratifies arbitrary policies directly. What it says is narrower and worth
  stating precisely: **no theorem currently in this kernel depends on A1**.
  Listing A1 in a minimal basis for the guarded theorem would be false, and
  claiming the kernel's results rest on unforgeability would overstate them.

  The gap is real: the kernel proves coherence is preserved under the guard,
  and says nothing about who is entitled to invoke it. That is the A1-shaped
  hole, and it is a hole in COVERAGE, not in the proofs that exist.
-/

namespace DARM
namespace MinimalityA1

open DARM.Assumptions DARM.Ratification DARM.Composition

/-! ## The negative cell -/

/-- **A1 is NOT necessary for guarded ratification coherence.**

    Instantiated at `fun _ => True`, for which
    `Assumptions.A1_fails_for_trivial_predicate` shows A1 fails, the theorem
    still holds. So A1 cannot appear in that theorem's minimal basis.

    The proof is a single application — which is the point. If A1 were
    load-bearing, this would not typecheck. -/
theorem A1_not_necessary_for_guarded_coherence
    {n : ℕ} {CapId Token : Type} [DecidableEq CapId] [DecidableEq Token]
    (requires : Fin n → CapId) (allowedCapLimit : Finset CapId)
    (s : State CapId (Fin n)) (t : Token) (p : Finset (Fin n))
    (δ : ℝ) (w : Fin n → ℝ)
    (hcoh : IsCoherent s δ w) (hguard : GuardedRatification δ w p) :
    IsCoherent
      (step requires allowedCapLimit (fun _ => True) s
        (Event.authenticatedRatification t p)) δ w :=
  guarded_ratification_preserves_coherence requires allowedCapLimit
    (fun _ => True) s t p δ w hcoh hguard

/-- The other half of the cell is `Assumptions.A1_fails_for_trivial_predicate`,
    which shows A1 genuinely fails at the trivial predicate. Without it the
    theorem above would be vacuous as a minimality claim — it would just be the
    original theorem at some arbitrary predicate. It is cited rather than
    restated here, since restating would mean guessing its index type. -/
example : True := trivial

/-! ## Registered status

  DONE: the A1 necessity question, answered negatively. A1 is satisfiable,
  independent of coherence preservation, and NOT necessary for the guarded
  ratification theorem. Three cells, and the matrix entry for A1 is now
  complete for this theorem.



  THE COVERAGE GAP THIS EXPOSED, now filled. The kernel proved what ratification
  does to coherence and said nothing about who may invoke it. `Entitlement.lean`
  supplies that: an unauthenticated ratification is a no-op, so a policy change
  implies the token was accepted — and `entitlement_vacuous_without_A1` shows
  that property is empty at the predicate where A1 fails.

  So A1's role is now exact. Idle for coherence, because both branches preserve
  it regardless of the token. Load-bearing for entitlement, because there the
  branches differ and A1 is what makes the difference matter. The negative cell
  above is still correct; it was never that A1 was a bad assumption, only that
  the theorem it supports had not been stated.
-/

end MinimalityA1
end DARM

#print axioms DARM.MinimalityA1.A1_not_necessary_for_guarded_coherence
