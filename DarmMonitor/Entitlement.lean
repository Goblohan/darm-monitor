import DarmMonitor.MinimalityA1

/-
  Entitlement — who may invoke ratification, and why A1 is an assumption for
  something after all.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  THE GAP THIS FILLS. `MinimalityA1` established that A1 (token unforgeability)
  is NOT necessary for `guarded_ratification_preserves_coherence`, because that
  proof splits on token validity and closes both branches. The registered note
  there said the real gap was that "the kernel says what ratification does to
  coherence and nothing about who may invoke it".

  It turns out `step` does check. From `Basic.lean`:

      | .authenticatedRatification token newPolicy =>
          if validToken token then { s with policy := newPolicy } else s

  An invalid token leaves the state UNCHANGED — not merely coherent, but
  identical. That is the entitlement property, and it was implemented without a
  theorem naming it.

  WHY THIS MAKES A1 LOAD-BEARING. `unauthenticated_is_noop` says an invalid
  token changes nothing. Its force depends entirely on `validToken` being hard
  to satisfy: if every token were valid — the trivial predicate, where A1 fails
  — the theorem would be vacuously true and protect nothing. So A1 is exactly
  the assumption that gives this theorem content, which is what a registered
  assumption ought to be for.

  Contrast with the coherence theorem, where A1 is idle: there both branches
  preserve coherence, so unforgeability buys nothing. Here the two branches do
  DIFFERENT things, and A1 is what makes the difference matter.
-/

namespace DARM
namespace Entitlement

open DARM.Assumptions

/-! ## 1. An unauthenticated ratification is a no-op -/

/-- **Entitlement.** A ratification event whose token fails `validToken`
    leaves the state completely unchanged — not just coherent, identical.

    This is the theorem the kernel was missing: it says who may change the
    policy, where the coherence results only said what happens to the margin
    when someone does. -/
theorem unauthenticated_is_noop
    {CapId ActionId Token : Type} [DecidableEq CapId] [DecidableEq ActionId] [DecidableEq Token]
    (requires : ActionId → CapId) (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop) [DecidablePred validToken]
    (s : State CapId ActionId) (t : Token) (p : Finset ActionId)
    (hbad : ¬ validToken t) :
    step requires allowedCapLimit validToken s
      (Event.authenticatedRatification t p) = s := by
  simp [step, hbad]

/-- **The policy changes only under a valid token.** Contrapositive form: if
    ratification altered the policy, the token was accepted. -/
theorem policy_change_implies_valid_token
    {CapId ActionId Token : Type} [DecidableEq CapId] [DecidableEq ActionId] [DecidableEq Token]
    (requires : ActionId → CapId) (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop) [DecidablePred validToken]
    (s : State CapId ActionId) (t : Token) (p : Finset ActionId)
    (hchanged : step requires allowedCapLimit validToken s
      (Event.authenticatedRatification t p) ≠ s) :
    validToken t := by
  by_contra hbad
  exact hchanged (unauthenticated_is_noop requires allowedCapLimit validToken s t p hbad)

/-! ## 2. Why A1 matters here and not for coherence

  The theorems above are true for ANY `validToken`, including the trivial one.
  What A1 supplies is that they are not vacuous. -/

/-- **Without A1 the entitlement theorem is empty.** At the trivial predicate —
    where `Assumptions.A1_fails_for_trivial_predicate` shows A1 fails — no token
    is ever rejected, so `unauthenticated_is_noop` has no instances and
    `policy_change_implies_valid_token` concludes something that was already
    true of everything.

    This is the precise sense in which A1 is load-bearing HERE and idle for the
    coherence theorem: coherence holds on both branches regardless, but
    entitlement is only a restriction if some token fails. -/
theorem entitlement_vacuous_without_A1
    {CapId ActionId Token : Type} [DecidableEq CapId] [DecidableEq ActionId] [DecidableEq Token]
    (requires : ActionId → CapId) (allowedCapLimit : Finset CapId)
    (s : State CapId ActionId) (t : Token) (p : Finset ActionId) :
    step requires allowedCapLimit (fun _ => True) s
      (Event.authenticatedRatification t p)
      = { s with policy := p } := by
  simp [step]

/-! ## Registered status

  DONE: the entitlement property, named and proved. An unauthenticated
  ratification is a no-op; a policy change implies the token was accepted.

  AND A1'S ROLE IS NOW PRECISE. It is not necessary for coherence preservation
  (`MinimalityA1`) and it is exactly what gives entitlement content
  (`entitlement_vacuous_without_A1`). A registered assumption that was doing no
  work now has a theorem it is the assumption for.

  WHAT THIS DOES NOT ADDRESS. `validToken` remains an opaque predicate — the
  kernel proves nothing about how tokens are issued, checked, or revoked, and
  nothing here constitutes a cryptographic argument. The claim is narrow: given
  a predicate hard to satisfy, the monitor's policy cannot be changed without
  satisfying it. Whether any real token scheme achieves that is outside the
  model, as the non-claims section of the README has always said.
-/

end Entitlement
end DARM

#print axioms DARM.Entitlement.unauthenticated_is_noop
#print axioms DARM.Entitlement.policy_change_implies_valid_token
#print axioms DARM.Entitlement.entitlement_vacuous_without_A1
