/-
  E24b — PER-RESOURCE INTENTS

  Discharges E24's stated limit ("intent granularity is per tool"). An intent
  names a tool plus constraints on named arguments; no constraints is E24's
  per-tool intent. A constraint (k, v) holds if some argument is named k AND
  every argument named k has value v, so it holds for any proposal, including
  ones with repeated names (which the broker's parser refuses anyway, P14):
  the theorems do not depend on lookup order.

  Proved: the claimed reason is irrelevant; execution requires a fitting
  intent AND B3's admission (binding); hence no intent can widen what B3
  admits (attenuation); execution consumes exactly the matched intent, and
  non-execution changes nothing. Witnesses on B3's write configuration: an
  intent for the report authorizes it once; an intent for another file does
  not; a repeated path argument defeats the constraint; a tool-only intent
  behaves as in E24; with a tool-wide intent listed first, it is the one
  consumed.

  NOT claimed: that the broker lists the broadest intent first (a load-time
  ordering, tested in Python), or that paths name files uniquely (the
  broker's normal-form check and race-free resolution; hard links are
  outside the model).
-/
import E24EpistemicPremiseTransfer

namespace DARM.E24b

open DARM.Broker (Proposal)

structure Intent where
  tool : String
  constraints : List (String × String)
  deriving Repr, DecidableEq

structure Registry where
  intents : List Intent
  deriving Repr, DecidableEq

/-- Some argument is named `c.1`, and every argument so named has value `c.2`. -/
def constraintHolds (args : List (String × String)) (c : String × String) : Bool :=
  args.any (fun a => a.1 == c.1) && args.all (fun a => a.1 != c.1 || a.2 == c.2)

def Intent.fits (i : Intent) (p : Proposal) : Bool :=
  i.tool == p.tool && i.constraints.all (constraintHolds p.args)

/-- The intent gate over B3, per resource. The first fitting intent is the one
    consumed, and only if B3 admits. -/
def step (cfg : DARM.Broker3.Config) (reg : Registry) (p : Proposal)
    (_claimed : DARM.E24.Premise) : Option DARM.Kernel.Invocation × Registry :=
  match reg.intents.find? (fun i => i.fits p) with
  | none => (none, reg)
  | some i =>
    match DARM.Broker3.brokerStep cfg p with
    | some e => (some e, { intents := reg.intents.erase i })
    | none => (none, reg)

theorem claimed_reason_irrelevant (cfg : DARM.Broker3.Config) (reg : Registry)
    (p : Proposal) (c1 c2 : DARM.E24.Premise) :
    step cfg reg p c1 = step cfg reg p c2 := rfl

/-- Whatever `find?` returns fits the proposal (proved directly, rather than
    through a library lemma whose signature varies across Lean versions). -/
theorem find_fits {l : List Intent} {p : Proposal} {i : Intent}
    (h : l.find? (fun i => i.fits p) = some i) : i.fits p = true := by
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

/-- Binding: execution requires an intent in the registry that fits this very
    proposal, AND B3's admission. -/
theorem execution_requires_fitting_intent (cfg : DARM.Broker3.Config) (reg : Registry)
    (p : Proposal) (c : DARM.E24.Premise) (e : DARM.Kernel.Invocation)
    (h : (step cfg reg p c).1 = some e) :
    ∃ i, reg.intents.find? (fun i => i.fits p) = some i ∧ i ∈ reg.intents ∧
      i.fits p = true ∧ DARM.Broker3.brokerStep cfg p = some e := by
  unfold step at h
  revert h
  cases hf : reg.intents.find? (fun i => i.fits p) with
  | none => intro h; simp at h
  | some i =>
    cases hb : DARM.Broker3.brokerStep cfg p with
    | none => intro h; simp at h
    | some e' =>
      intro h
      simp at h
      subst h
      exact ⟨i, rfl, List.mem_of_find?_eq_some hf, find_fits hf, rfl⟩

/-- Attenuation: no intent, however written, admits what B3 rejects. -/
theorem intent_never_widens (cfg : DARM.Broker3.Config) (reg : Registry)
    (p : Proposal) (c : DARM.E24.Premise) (e : DARM.Kernel.Invocation)
    (h : (step cfg reg p c).1 = some e) :
    DARM.Broker3.brokerStep cfg p = some e := by
  obtain ⟨_, _, _, _, hb⟩ := execution_requires_fitting_intent cfg reg p c e h
  exact hb

/-- Execution consumes exactly the matched intent. -/
theorem execution_consumes_the_matched_intent (cfg : DARM.Broker3.Config) (reg : Registry)
    (p : Proposal) (c : DARM.E24.Premise) (e : DARM.Kernel.Invocation)
    (h : (step cfg reg p c).1 = some e) :
    ∃ i, reg.intents.find? (fun i => i.fits p) = some i ∧
      (step cfg reg p c).2 = { intents := reg.intents.erase i } := by
  unfold step at h ⊢
  revert h
  cases hf : reg.intents.find? (fun i => i.fits p) with
  | none => intro h; simp at h
  | some i =>
    cases hb : DARM.Broker3.brokerStep cfg p with
    | none => intro h; simp at h
    | some e' => intro _; exact ⟨i, rfl, rfl⟩

/-- Without execution, the registry is unchanged: no intent is spent. -/
theorem no_execution_keeps_registry (cfg : DARM.Broker3.Config) (reg : Registry)
    (p : Proposal) (c : DARM.E24.Premise)
    (h : (step cfg reg p c).1 = none) :
    (step cfg reg p c).2 = reg := by
  unfold step at h ⊢
  revert h
  cases hf : reg.intents.find? (fun i => i.fits p) with
  | none => intro _; rfl
  | some i =>
    cases hb : DARM.Broker3.brokerStep cfg p with
    | none => intro _; rfl
    | some e' => intro h; simp at h

/-! ## Witnesses (B3's write configuration, as in E24) -/

/-- The report write's own path argument, read from the proposal. -/
def reportPath : List (String × String) :=
  DARM.Broker3.agentWritesReport.args.filter (fun a => a.1 == "path")

def forThisReport : Intent := { tool := "write_file", constraints := reportPath }
def forAnotherFile : Intent :=
  { tool := "write_file", constraints := [("path", "/workspace/another.md")] }
def anyWrite : Intent := { tool := "write_file", constraints := [] }

/-- The constraint is real: exactly one path, so the witnesses are not vacuous. -/
theorem report_constraint_nonempty : reportPath.length = 1 := by
  decide +kernel

theorem bound_intent_authorizes_its_file :
    ((step DARM.Broker3.writeCfg ⟨[forThisReport]⟩ DARM.Broker3.agentWritesReport
      DARM.E24.claimUserAsked).1).isSome = true := by
  decide +kernel

theorem intent_for_another_file_blocks :
    ((step DARM.Broker3.writeCfg ⟨[forAnotherFile]⟩ DARM.Broker3.agentWritesReport
      DARM.E24.claimUserAsked).1).isNone = true := by
  decide +kernel

theorem bound_intent_used_once :
    ((step DARM.Broker3.writeCfg
        (step DARM.Broker3.writeCfg ⟨[forThisReport]⟩ DARM.Broker3.agentWritesReport
          DARM.E24.claimUserAsked).2
        DARM.Broker3.agentWritesReport DARM.E24.claimUserAsked).1).isNone = true := by
  decide +kernel

/-- A second path argument that disagrees defeats the constraint. -/
def reportPlusAnotherPath : Proposal :=
  { DARM.Broker3.agentWritesReport with
    args := DARM.Broker3.agentWritesReport.args ++ [("path", "/workspace/another.md")] }

theorem repeated_path_defeats_constraint :
    ((step DARM.Broker3.writeCfg ⟨[forThisReport]⟩ reportPlusAnotherPath
      DARM.E24.claimUserAsked).1).isNone = true := by
  decide +kernel

/-- A tool-only intent decides exactly as E24's per-tool intent. -/
theorem tool_only_intent_as_in_E24 :
    ((step DARM.Broker3.writeCfg ⟨[anyWrite]⟩ DARM.Broker3.agentWritesReport
      DARM.E24.claimUserAsked).1).isSome =
    ((DARM.E24.intentStep DARM.Broker3.writeCfg DARM.E24.oneWrite
      DARM.Broker3.agentWritesReport DARM.E24.claimUserAsked).1).isSome := by
  decide +kernel

theorem rejected_attempt_keeps_intent :
    (step DARM.Broker3.writeCfg ⟨[anyWrite]⟩ DARM.Broker3.contentBuysNothing
      DARM.E24.claimUserAsked).2.intents = [anyWrite] := by
  decide +kernel

/-- With the tool-wide intent listed first (the broker's load order), it is
    the one consumed, and the narrower intent remains. -/
theorem broadest_listed_first_is_consumed :
    (step DARM.Broker3.writeCfg ⟨[anyWrite, forThisReport]⟩ DARM.Broker3.agentWritesReport
      DARM.E24.claimUserAsked).2.intents = [forThisReport] := by
  decide +kernel

end DARM.E24b

#print axioms DARM.E24b.claimed_reason_irrelevant
#print axioms DARM.E24b.execution_requires_fitting_intent
#print axioms DARM.E24b.intent_never_widens
#print axioms DARM.E24b.execution_consumes_the_matched_intent
#print axioms DARM.E24b.no_execution_keeps_registry
#print axioms DARM.E24b.report_constraint_nonempty
#print axioms DARM.E24b.intent_for_another_file_blocks
#print axioms DARM.E24b.repeated_path_defeats_constraint
#print axioms DARM.E24b.broadest_listed_first_is_consumed
