/-
  E24d — REDEMPTION (proposed)

  Probe P13 (darm-guard 0.14.0): a proposal that fits a per-resource intent
  redeems it whoever produced it, so a hijacked agent's write, proposed first,
  consumes the principal's intent and the principal's own write is refused.
  Probe P15: an admitted write whose effect fails still consumes the intent.

  Part 1  P13 in E24b's own semantics, on B3's write configuration.
  Part 2  Indistinguishability: any redemption rule over proposals gives equal
          proposals equal answers, so no rule separates the principal's proposal
          from an attacker's identical one ("entitlement" is not a boundary
          predicate). E24b already closes P13 when the principal can pin the
          content (a content constraint); in general it cannot.
  Part 3  Premise-bound redemption: an intent carries a premise the broker
          evaluates on world state. Redemption requires it; while it is false no
          proposal, in any order, redeems, and the registry is unchanged. The
          agent's claim is irrelevant. With a true premise it is exactly E24b.
          Residual limit stated: premise true + identical proposals -> first wins.
  Part 4  P15 is a correspondence gap, not a model violation: E24b's step never
          sees an effect outcome, so its "execution" is B3 admission. Three-state
          consumption (available / reserved / spent) settles on the recorded
          outcome: a proven non-effect returns the intent, an unknown outcome
          holds it, success spends it.

  NOT claimed: that the broker computes premises correctly (each premise is a
  deterministic function the broker evaluates, tested in Python); that
  "proven non-effect" is established correctly (B4/B5's recorded before-state);
  anything about timing when proposals coincide (Part 3's residual).
-/
import E24cRevocation

namespace DARM.E24d

open DARM.Broker (Proposal)
open DARM.E24b (Intent Registry step forThisReport)

/-! ## Part 1: P13 in E24b's semantics -/

/-- The hijacked agent's write: same path as the principal's report, other content. -/
def attackerWritesReport : Proposal :=
  { tool := "write_file",
    args := [("path", "/workspace/reports/q3.md"), ("content", "wire funds to US1330")] }

/-- The attacker's write fits the principal's per-resource intent. -/
theorem attacker_fits_principal_intent :
    forThisReport.fits attackerWritesReport = true := by
  decide +kernel

/-- P13, step 1: proposed first, the attacker's write executes. -/
theorem p13_attacker_first_executes :
    ((step DARM.Broker3.writeCfg ⟨[forThisReport]⟩ attackerWritesReport
      DARM.E24.claimUserAsked).1).isSome = true := by
  decide +kernel

/-- P13, step 2: the principal's own write is then refused. -/
theorem p13_principal_then_refused :
    ((step DARM.Broker3.writeCfg
        (step DARM.Broker3.writeCfg ⟨[forThisReport]⟩ attackerWritesReport
          DARM.E24.claimUserAsked).2
        DARM.Broker3.agentWritesReport DARM.E24.claimUserAsked).1).isNone = true := by
  decide +kernel

/-- In the other order the principal's write executes: the outcome is decided
    by arrival order alone. -/
theorem p13_principal_first_executes :
    ((step DARM.Broker3.writeCfg ⟨[forThisReport]⟩ DARM.Broker3.agentWritesReport
      DARM.E24.claimUserAsked).1).isSome = true := by
  decide +kernel

/-! ## Part 2: Indistinguishability -/

/-- A redemption rule the broker can implement is a function of the proposal
    (tool and arguments) and whatever else the broker holds, but not of who,
    causally, produced the proposal: that is not transmitted. -/
abbrev RedemptionRule (State : Type) := State → Proposal → Bool

/-- Two proposals the broker receives identically are decided identically. -/
theorem equal_proposals_equal_decisions {State : Type} (R : RedemptionRule State)
    (s : State) (p q : Proposal) (h : p = q) : R s p = R s q := by
  rw [h]

/-- Entitlement-exact: a rule redeems exactly the principal's proposals. -/
def EntitlementExact {State : Type} (R : RedemptionRule State) (s : State)
    (origin : List (Proposal × Bool)) : Prop :=
  ∀ x ∈ origin, R s x.1 = x.2

/-- If the principal's and an attacker's proposals are identical, no rule is
    entitlement-exact (the R22 pattern, for redemption). -/
theorem no_exact_rule {State : Type} (s : State) (p : Proposal) :
    ∀ R : RedemptionRule State, ¬ EntitlementExact R s [(p, true), (p, false)] := by
  intro R h
  have h1 := h (p, true) (by simp)
  have h2 := h (p, false) (by simp)
  simp only at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- E24b's own step is such a rule: its decision depends on the proposal alone,
    never on the claimed reason (E24b.claimed_reason_irrelevant) nor on origin. -/
theorem e24b_step_is_observable (cfg : DARM.Broker3.Config) (reg : Registry)
    (p q : Proposal) (h : p = q) (c : DARM.E24.Premise) :
    step cfg reg p c = step cfg reg q c := by
  rw [h]

/-- Partial repair inside E24b: when the principal can pin the content, the
    intent no longer fits the attacker's write, and P13 closes. -/
def pinnedReport : Intent :=
  { tool := "write_file",
    constraints := [("path", "/workspace/reports/q3.md"), ("content", "Q3 summary")] }

theorem pinned_content_refuses_attacker :
    ((step DARM.Broker3.writeCfg ⟨[pinnedReport]⟩ attackerWritesReport
      DARM.E24.claimUserAsked).1).isNone = true := by
  decide +kernel

theorem pinned_content_keeps_intent_for_principal :
    ((step DARM.Broker3.writeCfg
        (step DARM.Broker3.writeCfg ⟨[pinnedReport]⟩ attackerWritesReport
          DARM.E24.claimUserAsked).2
        DARM.Broker3.agentWritesReport DARM.E24.claimUserAsked).1).isSome = true := by
  decide +kernel

/-! ## Part 3: Premise-bound redemption -/

/-- A premise-bound intent: an E24b intent and a premise over world state that
    the broker evaluates itself. The premise never sees the proposal. -/
structure PIntent (World : Type) where
  base : Intent
  premise : World → Bool

/-- Premise-bound step for one intent: redemption requires the premise at the
    boundary, then proceeds exactly as E24b. -/
def stepP {World : Type} (cfg : DARM.Broker3.Config) (w : World) (i : PIntent World)
    (reg : Registry) (p : Proposal) (c : DARM.E24.Premise) :
    Option DARM.Kernel.Invocation × Registry :=
  if i.premise w then step cfg reg p c else (none, reg)

/-- Soundness: whatever executes did so with the premise true at the boundary. -/
theorem executed_implies_premise {World : Type} (cfg : DARM.Broker3.Config) (w : World)
    (i : PIntent World) (reg : Registry) (p : Proposal) (c : DARM.E24.Premise)
    (e : DARM.Kernel.Invocation) (h : (stepP cfg w i reg p c).1 = some e) :
    i.premise w = true := by
  unfold stepP at h
  cases hp : i.premise w
  · rw [hp] at h; simp at h
  · rfl

/-- While the premise is false, no proposal executes, in any order, and no
    intent is spent. -/
theorem no_redemption_without_premise {World : Type} (cfg : DARM.Broker3.Config)
    (w : World) (i : PIntent World) (reg : Registry) (hw : i.premise w = false) :
    ∀ p c, stepP cfg w i reg p c = (none, reg) := by
  intro p c; unfold stepP; rw [hw]; rfl

/-- The agent's claimed reason cannot move the decision. -/
theorem claim_irrelevant {World : Type} (cfg : DARM.Broker3.Config) (w : World)
    (i : PIntent World) (reg : Registry) (p : Proposal) (c1 c2 : DARM.E24.Premise) :
    stepP cfg w i reg p c1 = stepP cfg w i reg p c2 := rfl

/-- Conservative: with the premise true, premise binding is exactly E24b. -/
theorem conservative_over_e24b {World : Type} (cfg : DARM.Broker3.Config) (w : World)
    (i : PIntent World) (reg : Registry) (p : Proposal) (c : DARM.E24.Premise)
    (hw : i.premise w = true) : stepP cfg w i reg p c = step cfg reg p c := by
  unfold stepP; rw [hw]; rfl

/-- Premise binding never widens B3 (inherits E24b.intent_never_widens). -/
theorem premise_never_widens {World : Type} (cfg : DARM.Broker3.Config) (w : World)
    (i : PIntent World) (reg : Registry) (p : Proposal) (c : DARM.E24.Premise)
    (e : DARM.Kernel.Invocation) (h : (stepP cfg w i reg p c).1 = some e) :
    DARM.Broker3.brokerStep cfg p = some e := by
  have hp := executed_implies_premise cfg w i reg p c e h
  rw [conservative_over_e24b cfg w i reg p c hp] at h
  exact DARM.E24b.intent_never_widens cfg reg p c e h

/-- Conditional witness: "write the report if the figures are final". -/
structure Figures where
  final : Bool

def ifFinal : PIntent Figures := ⟨forThisReport, fun w => w.final⟩

/-- Figures not final: the attacker's write is refused and the intent kept... -/
theorem conditional_refuses_attacker :
    stepP DARM.Broker3.writeCfg ⟨false⟩ ifFinal ⟨[forThisReport]⟩ attackerWritesReport
      DARM.E24.claimUserAsked = (none, ⟨[forThisReport]⟩) :=
  no_redemption_without_premise _ _ _ _ rfl _ _

/-- ...and so is the principal's own write, for the same reason: the premise is
    about the world, not about who proposes. -/
theorem conditional_refuses_principal_too :
    stepP DARM.Broker3.writeCfg ⟨false⟩ ifFinal ⟨[forThisReport]⟩
      DARM.Broker3.agentWritesReport DARM.E24.claimUserAsked = (none, ⟨[forThisReport]⟩) :=
  no_redemption_without_premise _ _ _ _ rfl _ _

/-- Residual limit, stated rather than hidden: with the premise true and an
    unpinned intent, the attacker's write, arriving first, still executes. -/
theorem residual_race_when_premise_true :
    ((stepP DARM.Broker3.writeCfg ⟨true⟩ ifFinal ⟨[forThisReport]⟩ attackerWritesReport
      DARM.E24.claimUserAsked).1).isSome = true := by
  decide +kernel

/-! ## Part 4: P15 and three-state consumption -/

/-- E24b's step has no effect outcome in its signature: it consumes on B3
    admission. So a failed effect after admission is a correspondence gap
    between the model's "execution" and the world, not a model violation. -/
theorem e24b_consumes_on_admission (cfg : DARM.Broker3.Config) (reg : Registry)
    (p : Proposal) (c : DARM.E24.Premise) (e : DARM.Kernel.Invocation)
    (h : (step cfg reg p c).1 = some e) :
    ∃ i, reg.intents.find? (fun i => i.fits p) = some i ∧
      (step cfg reg p c).2 = { intents := reg.intents.erase i } :=
  DARM.E24b.execution_consumes_the_matched_intent cfg reg p c e h

/-- Outcomes as the broker records them (B4/B5). -/
inductive Outcome | succeeded | provenNoEffect | unknown
  deriving Repr, DecidableEq

/-- Registry with reservations: admission moves an intent from `available` to
    `reserved` (keyed by request); the recorded outcome settles it. -/
structure Registry3 where
  available : List Intent
  reserved : List (Nat × Intent)
  deriving Repr, DecidableEq

def reserve (r : Registry3) (req : Nat) (i : Intent) : Registry3 :=
  { available := r.available.erase i, reserved := (req, i) :: r.reserved }

def settle (r : Registry3) (req : Nat) (i : Intent) : Outcome → Registry3
  | .succeeded => { r with reserved := r.reserved.erase (req, i) }
  | .provenNoEffect => { available := i :: r.available, reserved := r.reserved.erase (req, i) }
  | .unknown => r

/-- P15 closed: a proven non-effect returns the intent to the principal. -/
theorem no_burn (r : Registry3) (req : Nat) (i : Intent) :
    i ∈ (settle (reserve r req i) req i .provenNoEffect).available := by
  simp [settle]

/-- An unknown outcome holds the reservation: the intent is neither returned
    nor released while an effect may have happened. -/
theorem unknown_holds (r : Registry3) (req : Nat) (i : Intent) :
    settle (reserve r req i) req i .unknown = reserve r req i := rfl

/-- Success spends the reservation: nothing about it remains reserved. -/
theorem success_spends (r : Registry3) (req : Nat) (i : Intent) (hr : (req, i) ∉ r.reserved) :
    (req, i) ∉ (settle (reserve r req i) req i .succeeded).reserved := by
  simp [settle, reserve, hr]

/-- Success does not return the intent: the available intents are exactly
    those left after reservation. -/
theorem success_not_returned (r : Registry3) (req : Nat) (i : Intent) :
    (settle (reserve r req i) req i .succeeded).available = r.available.erase i := rfl


/-! ## Part 5: Intent completeness -- safety without identifying the proposer -/

/-- The principal's acceptance judgment over proposals: which effects they would
    accept. It is a specification, never evaluated by the broker. -/
abbrev Acceptable := Proposal → Prop

/-- An intent is complete for `acc` if every proposal that fits it is acceptable. -/
def Complete (acc : Acceptable) (i : Intent) : Prop :=
  ∀ p : Proposal, i.fits p = true → acc p

/-- Safety without entitlement: if every intent in the registry is complete,
    whatever E24b executes is acceptable -- whoever proposed it, in any order.
    The race then costs the principal availability, never safety. -/
theorem complete_intents_execute_only_acceptable (acc : Acceptable)
    (cfg : DARM.Broker3.Config) (reg : Registry) (p : Proposal) (c : DARM.E24.Premise)
    (e : DARM.Kernel.Invocation) (hc : ∀ i ∈ reg.intents, Complete acc i)
    (h : (step cfg reg p c).1 = some e) : acc p := by
  obtain ⟨i, _, hmem, hfit, _⟩ := DARM.E24b.execution_requires_fitting_intent cfg reg p c e h
  exact hc i hmem p hfit

/-- The acceptance judgment for the P13 scenario: the principal accepts exactly
    their Q3 summary at the report path. -/
def acceptsQ3Summary : Acceptable := fun p =>
  p.tool = "write_file" ∧ p.args = [("path", "/workspace/reports/q3.md"), ("content", "Q3 summary")]

/-- P13's root cause, stated precisely: the path-only intent is incomplete --
    the attacker's write fits it and is not acceptable. -/
theorem path_only_intent_incomplete : ¬ Complete acceptsQ3Summary forThisReport := by
  intro h
  have := h attackerWritesReport attacker_fits_principal_intent
  simp [acceptsQ3Summary, attackerWritesReport] at this

/-- The pinned intent fits only proposals with the principal's exact path and
    content (under the broker's no-repeated-names parse, P14, which this
    witness checks on the principal's own write). -/
theorem pinned_fits_principal : pinnedReport.fits DARM.Broker3.agentWritesReport = true := by
  decide +kernel

theorem pinned_rejects_attacker_fit : pinnedReport.fits attackerWritesReport = false := by
  decide +kernel

/-! ## Part 6: Completeness relative to B3 admission -/

/-- Completeness relative to the boundary: every proposal that fits the intent
    AND is admitted by B3 is acceptable. This is the notion the broker needs:
    B3's own obligations may supply the rest of the constraint. -/
def CompleteUnder (cfg : DARM.Broker3.Config) (acc : Acceptable) (i : Intent) : Prop :=
  ∀ p e, i.fits p = true → DARM.Broker3.brokerStep cfg p = some e → acc p

/-- Safety from relative completeness: if every intent is complete under B3,
    whatever E24b executes is acceptable, whoever proposed it, in any order. -/
theorem complete_under_b3_execute_only_acceptable (cfg : DARM.Broker3.Config)
    (acc : Acceptable) (reg : Registry) (p : Proposal) (c : DARM.E24.Premise)
    (e : DARM.Kernel.Invocation) (hc : ∀ i ∈ reg.intents, CompleteUnder cfg acc i)
    (h : (step cfg reg p c).1 = some e) : acc p := by
  obtain ⟨i, _, hmem, hfit, hb⟩ := DARM.E24b.execution_requires_fitting_intent cfg reg p c e h
  exact hc i hmem p e hfit hb

/-- The effect a write proposal denotes, independent of argument order and of
    repeated identical arguments: every argument is the given path or the given
    content, and both are present. -/
def WritesExactly (path content : String) : Acceptable := fun p =>
  p.tool = "write_file" ∧
  (∀ a ∈ p.args, (a.1 = "path" ∧ a.2 = path) ∨ (a.1 = "content" ∧ a.2 = content)) ∧
  (∃ a ∈ p.args, a.1 = "path") ∧ (∃ a ∈ p.args, a.1 = "content")

/-- Admission under B3's write configuration: every argument key has a rule,
    so it is `path` or `content` (deny by default, K4). -/
theorem admitted_write_keys (p : Proposal) (e : DARM.Kernel.Invocation)
    (h : DARM.Broker3.brokerStep DARM.Broker3.writeCfg p = some e) :
    ∀ a ∈ p.args, a.1 = "path" ∨ a.1 = "content" := by
  intro a ha
  unfold DARM.Broker3.brokerStep at h
  split at h
  · rename_i hk
    have hadm := (DARM.Broker3.k4_admit_iff _ _ _).mp hk
    unfold DARM.Kernel4.admissible at hadm
    simp only [Bool.and_eq_true] at hadm
    obtain ⟨⟨⟨⟨_, htool⟩, _⟩, hargs⟩, _⟩ := hadm
    unfold DARM.Kernel4.argsAllowed at hargs
    unfold DARM.Broker3.canonicalize at hargs
    cases ht : DARM.Kernel4.findTool DARM.Broker3.writeCfg.policy p.tool with
    | none => rw [ht] at hargs; simp at hargs
    | some tp =>
      rw [ht] at hargs
      simp only [List.all_eq_true, List.mem_map] at hargs
      have hA := hargs _ ⟨a, ha, rfl⟩
      unfold DARM.Kernel4.argAllowed at hA
      have htp : tp.rules.map (·.key) = ["path", "content"] := by
        revert ht
        unfold DARM.Kernel4.findTool
        simp [DARM.Broker3.writeCfg, DARM.Kernel4.writePolicy]
        intro _ htp; subst htp; rfl
      cases hr : DARM.Kernel4.findRule tp a.1 with
      | none => simp only [hr] at hA; exact absurd hA (by simp)
      | some r =>
        unfold DARM.Kernel4.findRule at hr
        have hk : r.key = a.1 := by
          have := List.find?_some hr; simpa using this
        have hm : r ∈ tp.rules := List.mem_of_find?_eq_some hr
        have : r.key ∈ tp.rules.map (·.key) := List.mem_map_of_mem hm
        rw [htp] at this
        simp at this
        rcases this with h1 | h1
        · left; rw [← hk, h1]
        · right; rw [← hk, h1]
  · simp at h

/-- The pinned intent is complete under B3: any admitted proposal that fits it
    writes exactly the principal's content to the principal's path. -/
theorem pinned_complete_under_b3 :
    CompleteUnder DARM.Broker3.writeCfg
      (WritesExactly "/workspace/reports/q3.md" "Q3 summary") pinnedReport := by
  intro p e hfit hb
  have hkeys := admitted_write_keys p e hb
  unfold Intent.fits pinnedReport at hfit
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_cons, List.all_nil, Bool.and_true] at hfit
  obtain ⟨htool, hpath, hcontent⟩ := hfit
  unfold DARM.E24b.constraintHolds at hpath hcontent
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, beq_iff_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at hpath hcontent
  obtain ⟨⟨ap, hap, hapk⟩, hpall⟩ := hpath
  obtain ⟨⟨ac, hac, hack⟩, hcall⟩ := hcontent
  refine ⟨htool.symm, ?_, ⟨ap, hap, hapk⟩, ⟨ac, hac, hack⟩⟩
  intro a ha
  rcases hkeys a ha with hk | hk
  · left; refine ⟨hk, ?_⟩
    rcases hpall a ha with h1 | h1
    · exact absurd hk h1
    · exact h1
  · right; refine ⟨hk, ?_⟩
    rcases hcall a ha with h1 | h1
    · exact absurd hk h1
    · exact h1

/-- P13 closed for pinnable content, as a safety theorem: with the pinned
    intent, whatever executes -- attacker's or principal's, in any order --
    writes exactly the principal's summary. -/
theorem pinned_registry_executes_only_principal_effect (p : Proposal)
    (c : DARM.E24.Premise) (e : DARM.Kernel.Invocation)
    (h : (step DARM.Broker3.writeCfg ⟨[pinnedReport]⟩ p c).1 = some e) :
    WritesExactly "/workspace/reports/q3.md" "Q3 summary" p :=
  complete_under_b3_execute_only_acceptable _ _ _ p c e
    (by intro i hi; simp at hi; subst hi; exact pinned_complete_under_b3) h

end DARM.E24d

#print axioms DARM.E24d.p13_attacker_first_executes
#print axioms DARM.E24d.p13_principal_then_refused
#print axioms DARM.E24d.no_exact_rule
#print axioms DARM.E24d.pinned_content_refuses_attacker
#print axioms DARM.E24d.executed_implies_premise
#print axioms DARM.E24d.no_redemption_without_premise
#print axioms DARM.E24d.conservative_over_e24b
#print axioms DARM.E24d.premise_never_widens
#print axioms DARM.E24d.residual_race_when_premise_true
#print axioms DARM.E24d.no_burn
#print axioms DARM.E24d.success_spends
#print axioms DARM.E24d.complete_intents_execute_only_acceptable
#print axioms DARM.E24d.path_only_intent_incomplete
#print axioms DARM.E24d.admitted_write_keys
#print axioms DARM.E24d.complete_under_b3_execute_only_acceptable
#print axioms DARM.E24d.pinned_complete_under_b3
#print axioms DARM.E24d.pinned_registry_executes_only_principal_effect
