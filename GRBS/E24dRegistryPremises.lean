/-
  E24d-R — PREMISES OVER A REGISTRY

  E24d Part 3 proves premise-bound redemption for one intent. The broker holds
  several, each with its own premises, and redeems the first intent that fits
  the proposal AND whose premises all hold, skipping and keeping the rest. This
  file models that rule exactly. Premises are data (observations the broker
  makes: a path present, a path absent), as in the broker's intent syntax, so a
  consumed intent can be removed from the registry by equality. The world is
  what the broker observes; sat is evaluated by the broker, never read from the
  proposal.

  Proved: whatever executes was authorized by a fitting intent whose premises
  all hold, and admitted by B3; if every fitting intent has a false premise,
  nothing executes and nothing is spent; premises never widen B3; exactly the
  redeemed intent is consumed; the agent's claim is irrelevant. Witnesses: a
  conditional intent is skipped while its premise fails and a plain one is
  redeemed instead, the conditional one kept.

  NOT claimed: that the broker observes the world correctly (its race-free
  observation, B5's); that a premise still holds during the effect; digest
  premises (if_digest) are modeled only as presence here. The broker orders
  intents broadest first; the witnesses fix an order explicitly.
-/
import E24dRedemption

namespace DARM.E24dR

open DARM.Broker (Proposal)
open DARM.E24b (Intent)

/-- A premise, as data: something the broker can observe. -/
inductive Obs where
  | present (path : String)
  | absent (path : String)
  deriving DecidableEq, Repr

/-- The world, as the broker observes it: which paths are present. -/
abbrev World := List String

def sat (w : World) : Obs → Bool
  | .present x => w.contains x
  | .absent x => !(w.contains x)

structure PIntent where
  intent : Intent
  premises : List Obs
  deriving DecidableEq, Repr

structure PRegistry where
  intents : List PIntent
  deriving DecidableEq, Repr

/-- The broker's test: the intent fits the proposal, and its premises all hold. -/
def usable (w : World) (p : Proposal) (i : PIntent) : Bool :=
  i.intent.fits p && i.premises.all (sat w)

/-- The broker's rule: redeem the first usable intent, if B3 admits. -/
def stepR (cfg : DARM.Broker3.Config) (w : World) (reg : PRegistry) (p : Proposal)
    (_claimed : DARM.E24.Premise) : Option DARM.Kernel.Invocation × PRegistry :=
  match reg.intents.find? (usable w p) with
  | none => (none, reg)
  | some i =>
    match DARM.Broker3.brokerStep cfg p with
    | some e => (some e, { intents := reg.intents.erase i })
    | none => (none, reg)

/-- Whatever find? returns satisfies its predicate (proved directly). -/
theorem find_sat {α : Type} {q : α → Bool} {l : List α} {a : α}
    (h : l.find? q = some a) : q a = true := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.find?_cons] at h
    split at h
    · rename_i hx
      simp at h
      subst h
      exact hx
    · exact ih h

/-- Whatever executes was authorized by a fitting intent whose premises all
    hold, and admitted by B3. -/
theorem executed_implies_usable (cfg : DARM.Broker3.Config) (w : World) (reg : PRegistry)
    (p : Proposal) (c : DARM.E24.Premise) (e : DARM.Kernel.Invocation)
    (h : (stepR cfg w reg p c).1 = some e) :
    ∃ i, i ∈ reg.intents ∧ i.intent.fits p = true ∧ (∀ q ∈ i.premises, sat w q = true) ∧
      DARM.Broker3.brokerStep cfg p = some e := by
  unfold stepR at h
  revert h
  cases hf : reg.intents.find? (usable w p) with
  | none => intro h; simp at h
  | some i =>
    cases hb : DARM.Broker3.brokerStep cfg p with
    | none => intro h; simp at h
    | some e' =>
      intro h
      simp at h
      subst h
      have hu := find_sat hf
      unfold usable at hu
      simp only [Bool.and_eq_true, List.all_eq_true] at hu
      exact ⟨i, List.mem_of_find?_eq_some hf, hu.1, hu.2, rfl⟩

/-- If every intent that fits has some premise false, nothing executes and
    nothing is spent, whoever proposes, in any order. -/
theorem no_redemption_without_a_usable_intent (cfg : DARM.Broker3.Config) (w : World)
    (reg : PRegistry) (p : Proposal) (c : DARM.E24.Premise)
    (hno : ∀ i ∈ reg.intents, i.intent.fits p = true → ∃ q ∈ i.premises, sat w q = false) :
    stepR cfg w reg p c = (none, reg) := by
  unfold stepR
  cases hf : reg.intents.find? (usable w p) with
  | none => rfl
  | some i =>
    exfalso
    have hu := find_sat hf
    unfold usable at hu
    simp only [Bool.and_eq_true, List.all_eq_true] at hu
    obtain ⟨q, hq, hqf⟩ := hno i (List.mem_of_find?_eq_some hf) hu.1
    have := hu.2 q hq
    rw [hqf] at this
    exact Bool.false_ne_true this

/-- Premises never admit what B3 rejects. -/
theorem premises_never_widen (cfg : DARM.Broker3.Config) (w : World) (reg : PRegistry)
    (p : Proposal) (c : DARM.E24.Premise) (e : DARM.Kernel.Invocation)
    (h : (stepR cfg w reg p c).1 = some e) : DARM.Broker3.brokerStep cfg p = some e := by
  obtain ⟨_, _, _, _, hb⟩ := executed_implies_usable cfg w reg p c e h
  exact hb

/-- Exactly the redeemed intent is consumed. -/
theorem execution_consumes_a_usable_intent (cfg : DARM.Broker3.Config) (w : World)
    (reg : PRegistry) (p : Proposal) (c : DARM.E24.Premise) (e : DARM.Kernel.Invocation)
    (h : (stepR cfg w reg p c).1 = some e) :
    ∃ i, reg.intents.find? (usable w p) = some i ∧
      (stepR cfg w reg p c).2 = { intents := reg.intents.erase i } := by
  unfold stepR at h ⊢
  revert h
  cases hf : reg.intents.find? (usable w p) with
  | none => intro h; simp at h
  | some i =>
    cases hb : DARM.Broker3.brokerStep cfg p with
    | none => intro h; simp at h
    | some e' => intro _; exact ⟨i, rfl, rfl⟩

theorem claim_irrelevant (cfg : DARM.Broker3.Config) (w : World) (reg : PRegistry)
    (p : Proposal) (c1 c2 : DARM.E24.Premise) :
    stepR cfg w reg p c1 = stepR cfg w reg p c2 := rfl

/-! ## Witnesses: the broker's several-intent behavior (B3's write configuration) -/

def flag : String := "/workspace/reports/final.flag"
def condReport : PIntent := ⟨DARM.E24b.forThisReport, [.present flag]⟩
def plainReport : PIntent := ⟨DARM.E24b.forThisReport, []⟩

/-- With the flag absent and only the conditional intent: refused, and kept. -/
theorem conditional_alone_blocks_and_is_kept :
    ((stepR DARM.Broker3.writeCfg [] ⟨[condReport]⟩ DARM.Broker3.agentWritesReport
      DARM.E24.claimUserAsked).1).isNone = true ∧
    (stepR DARM.Broker3.writeCfg [] ⟨[condReport]⟩ DARM.Broker3.agentWritesReport
      DARM.E24.claimUserAsked).2 = ⟨[condReport]⟩ := by
  decide +kernel

/-- With the flag absent: the conditional intent is skipped, the plain one
    redeemed instead, and the conditional one kept. -/
theorem skips_unmet_redeems_plain_keeps_conditional :
    ((stepR DARM.Broker3.writeCfg [] ⟨[condReport, plainReport]⟩ DARM.Broker3.agentWritesReport
      DARM.E24.claimUserAsked).1).isSome = true ∧
    (stepR DARM.Broker3.writeCfg [] ⟨[condReport, plainReport]⟩ DARM.Broker3.agentWritesReport
      DARM.E24.claimUserAsked).2 = ⟨[condReport]⟩ := by
  decide +kernel

/-- With the flag present: the conditional intent is usable, and redeemed first. -/
theorem met_premise_redeems_conditional :
    (stepR DARM.Broker3.writeCfg [flag] ⟨[condReport, plainReport]⟩ DARM.Broker3.agentWritesReport
      DARM.E24.claimUserAsked).2 = ⟨[plainReport]⟩ := by
  decide +kernel

end DARM.E24dR

#print axioms DARM.E24dR.executed_implies_usable
#print axioms DARM.E24dR.no_redemption_without_a_usable_intent
#print axioms DARM.E24dR.premises_never_widen
#print axioms DARM.E24dR.execution_consumes_a_usable_intent
#print axioms DARM.E24dR.skips_unmet_redeems_plain_keeps_conditional
