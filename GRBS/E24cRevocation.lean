/-
  E24c — REVOCATION

  The principal withdraws intents between broker steps. revoke removes every
  intent equal to a given one; revokeTool removes every intent for a tool.
  Because the broker's check and consumption happen under one lock, every
  action lies wholly before or wholly after a revocation: in the model,
  revocation is a registry transformation between steps.

  Proved: a revoked intent is gone; revocation never grants (whatever executes
  afterwards was authorized by an intent held before it, other than the
  revoked one); revoking the only fitting intent blocks the proposal; revoking
  a tool blocks every proposal for it, whatever else the registry holds.

  NOT claimed: an action already committed (its intent consumed and its
  prepared record durable) before the revocation is read cannot be recalled;
  its effect completes. How the principal's revocation reaches the broker
  (an append-only file the broker only reads) is an implementation fact,
  tested in Python.
-/
import E24bResourceIntents

namespace DARM.E24c

open DARM.Broker (Proposal)
open DARM.E24b (Intent Registry step)

def revoke (reg : Registry) (r : Intent) : Registry :=
  { intents := reg.intents.filter (fun i => i != r) }

def revokeTool (reg : Registry) (t : String) : Registry :=
  { intents := reg.intents.filter (fun i => i.tool != t) }

theorem revoked_intent_gone (reg : Registry) (r : Intent) :
    r ∉ (revoke reg r).intents := by
  simp [revoke, List.mem_filter]

/-- Revocation only takes authority away. -/
theorem revocation_never_grants (cfg : DARM.Broker3.Config) (reg : Registry) (r : Intent)
    (p : Proposal) (c : DARM.E24.Premise) (e : DARM.Kernel.Invocation)
    (h : (step cfg (revoke reg r) p c).1 = some e) :
    ∃ i, i ∈ reg.intents ∧ i ≠ r ∧ i.fits p = true := by
  obtain ⟨i, _, hmem, hfit, _⟩ :=
    DARM.E24b.execution_requires_fitting_intent cfg (revoke reg r) p c e h
  simp [revoke, List.mem_filter, bne_iff_ne] at hmem
  exact ⟨i, hmem.1, hmem.2, hfit⟩

/-- Revoking the only intent that fits a proposal blocks it. -/
theorem revoking_sole_authority_blocks (cfg : DARM.Broker3.Config) (reg : Registry)
    (r : Intent) (p : Proposal) (c : DARM.E24.Premise)
    (hsole : ∀ i ∈ reg.intents, i.fits p = true → i = r) :
    (step cfg (revoke reg r) p c).1 = none := by
  cases h : (step cfg (revoke reg r) p c).1 with
  | none => rfl
  | some e =>
    obtain ⟨i, hmem, hne, hfit⟩ := revocation_never_grants cfg reg r p c e h
    exact absurd (hsole i hmem hfit) hne

/-- Revoking a tool blocks every proposal for it, whatever else is held. -/
theorem revoked_tool_executes_nothing (cfg : DARM.Broker3.Config) (reg : Registry)
    (p : Proposal) (c : DARM.E24.Premise) :
    (step cfg (revokeTool reg p.tool) p c).1 = none := by
  cases h : (step cfg (revokeTool reg p.tool) p c).1 with
  | none => rfl
  | some e =>
    obtain ⟨i, _, hmem, hfit, _⟩ :=
      DARM.E24b.execution_requires_fitting_intent cfg (revokeTool reg p.tool) p c e h
    simp [revokeTool, List.mem_filter, bne_iff_ne] at hmem
    simp [DARM.E24b.Intent.fits] at hfit
    exact absurd hfit.1 hmem.2

/-! ## Witnesses (B3's write configuration) -/

theorem revoked_report_intent_blocks :
    ((step DARM.Broker3.writeCfg (revoke ⟨[DARM.E24b.forThisReport]⟩ DARM.E24b.forThisReport)
      DARM.Broker3.agentWritesReport DARM.E24.claimUserAsked).1).isNone = true := by
  decide +kernel

/-- A targeted revocation leaves other intents in force. -/
theorem targeted_revocation_leaves_others :
    ((step DARM.Broker3.writeCfg
        (revoke ⟨[DARM.E24b.forAnotherFile, DARM.E24b.forThisReport]⟩ DARM.E24b.forAnotherFile)
      DARM.Broker3.agentWritesReport DARM.E24.claimUserAsked).1).isSome = true := by
  decide +kernel

end DARM.E24c

#print axioms DARM.E24c.revoked_intent_gone
#print axioms DARM.E24c.revocation_never_grants
#print axioms DARM.E24c.revoking_sole_authority_blocks
#print axioms DARM.E24c.revoked_tool_executes_nothing
#print axioms DARM.E24c.revoked_report_intent_blocks
#print axioms DARM.E24c.targeted_revocation_leaves_others
