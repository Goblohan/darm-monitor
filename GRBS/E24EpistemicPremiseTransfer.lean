/-
  E24 — EPISTEMIC PREMISE TRANSFER

  Layer 1 (epistemic core): a premise is warranted only if the principal
  asserted it or attested it. Generation is not warrant; an agent's
  assertion carries exactly the warrant of an untrusted source; a
  derivation is warranted only if every premise is (conservation, as R5);
  a principal attestation (an identity step) repairs a premise.

  Layer 2 (action intent): the premise behind an action is "the principal
  wants this done". By Layer 1 the agent's claim to that is worthless, so
  execution requires a principal-held, single-use intent, in addition to
  B3's full check. The agent's claimed trigger cannot affect the decision.

  NOT claimed: that registered intents are the principal's true wishes;
  intent granularity is per tool, so an authorized intent does not fix
  WHICH content is sent beyond what B3's rules fix.
-/
import B3BrokerModel

namespace DARM.E24

/-! ## Layer 1: warrant -/

inductive Source where
  | principal
  | agent
  | external
  deriving DecidableEq, Repr

structure Premise where
  claim : String
  source : Source
  deriving Repr

/-- Claims the principal has attested through a channel the agent cannot write. -/
structure Attestations where
  claims : List String

def warranted (att : Attestations) (p : Premise) : Bool :=
  p.source == Source.principal || att.claims.contains p.claim

/-- Generation is not warrant. -/
theorem generation_is_not_warrant (att : Attestations) (c : String)
    (h : att.claims.contains c = false) :
    warranted att { claim := c, source := Source.agent } = false := by
  simpa [warranted] using h

/-- The agent's assertion adds nothing over an untrusted external source. -/
theorem agent_assertion_adds_nothing (att : Attestations) (c : String) :
    warranted att { claim := c, source := Source.agent } =
      warranted att { claim := c, source := Source.external } := by
  rfl

/-- A principal attestation (an identity step) repairs any premise. -/
theorem repair_by_identity_step (att : Attestations) (c : String) (s : Source) :
    warranted { claims := c :: att.claims } { claim := c, source := s } = true := by
  simp [warranted]

structure Derivation where
  premises : List Premise
  conclusion : String

def derivationWarranted (att : Attestations) (d : Derivation) : Bool :=
  d.premises.all (warranted att)

/-- Conservation: one unwarranted premise blocks the whole derivation. -/
theorem unwarranted_premise_blocks_derivation (att : Attestations) (d : Derivation)
    (p : Premise) (hp : p ∈ d.premises) (hw : warranted att p = false) :
    derivationWarranted att d = false := by
  unfold derivationWarranted
  cases h : d.premises.all (warranted att) with
  | false => rfl
  | true =>
    rw [List.all_eq_true] at h
    have hx := h p hp
    rw [hw] at hx
    cases hx

/-! ## Layer 2: action intent -/

open DARM.Broker (Proposal)

/-- Principal-held, single-use authorizations for kinds of action (by tool),
    written through a channel the agent cannot write. -/
structure IntentRegistry where
  intents : List String

/-- The intent gate over B3. `_claimed` is the agent's stated reason for
    acting: by Layer 1 it carries no warrant, and the gate never reads it.
    An executed intent is consumed. -/
def intentStep (cfg : DARM.Broker3.Config) (reg : IntentRegistry) (p : Proposal)
    (_claimed : Premise) : Option DARM.Kernel.Invocation × IntentRegistry :=
  if reg.intents.contains p.tool then
    match DARM.Broker3.brokerStep cfg p with
    | some e => (some e, { intents := reg.intents.erase p.tool })
    | none => (none, reg)
  else (none, reg)

/-- The agent's claimed reason cannot affect the outcome. -/
theorem claimed_reason_irrelevant (cfg : DARM.Broker3.Config) (reg : IntentRegistry)
    (p : Proposal) (c1 c2 : Premise) :
    intentStep cfg reg p c1 = intentStep cfg reg p c2 := rfl

/-- Execution requires a registered intent AND B3's full admission. -/
theorem execution_requires_intent (cfg : DARM.Broker3.Config) (reg : IntentRegistry)
    (p : Proposal) (c : Premise) (e : DARM.Kernel.Invocation)
    (h : (intentStep cfg reg p c).1 = some e) :
    reg.intents.contains p.tool = true ∧ DARM.Broker3.brokerStep cfg p = some e := by
  unfold intentStep at h
  split at h
  · rename_i hc
    refine ⟨hc, ?_⟩
    revert h
    cases DARM.Broker3.brokerStep cfg p with
    | none => intro h; simp at h
    | some e' => intro h; simp at h; rw [h]
  · simp at h

/-! ## Witnesses (B3's write configuration) -/

def claimUserAsked : Premise :=
  { claim := "the user asked me to write this report", source := Source.agent }

def oneWrite : IntentRegistry := { intents := ["write_file"] }

theorem authorized_write_executes :
    ((intentStep DARM.Broker3.writeCfg oneWrite DARM.Broker3.agentWritesReport
      claimUserAsked).1).isSome = true := by
  decide +kernel

/-- A hijacked agent cannot turn one authorized write into two. -/
theorem hijacked_second_write_blocked :
    ((intentStep DARM.Broker3.writeCfg
        (intentStep DARM.Broker3.writeCfg oneWrite DARM.Broker3.agentWritesReport
          claimUserAsked).2
        DARM.Broker3.agentWritesReport claimUserAsked).1).isNone = true := by
  decide +kernel

/-- Clean arguments are not enough: without an intent, nothing executes. -/
theorem clean_arguments_without_intent_blocked :
    ((intentStep DARM.Broker3.writeCfg { intents := [] } DARM.Broker3.agentWritesReport
      claimUserAsked).1).isNone = true := by
  decide +kernel

/-- A rejected attempt does not consume the principal's intent. -/
theorem rejected_attempt_keeps_intent :
    (intentStep DARM.Broker3.writeCfg oneWrite DARM.Broker3.contentBuysNothing
      claimUserAsked).2.intents = ["write_file"] := by
  decide +kernel

end DARM.E24

#print axioms DARM.E24.generation_is_not_warrant
#print axioms DARM.E24.unwarranted_premise_blocks_derivation
#print axioms DARM.E24.claimed_reason_irrelevant
#print axioms DARM.E24.execution_requires_intent
#print axioms DARM.E24.hijacked_second_write_blocked
#print axioms DARM.E24.rejected_attempt_keeps_intent
