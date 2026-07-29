/-
  DARM Reference-Monitor Core — minimal executable formal model.

  STATUS: [SPEC] until `lake build` exits 0. Do not describe as verified before then.

  REGISTERED ASSUMPTIONS (not proven here, and not provable in this model):
  A1. Token unforgeability. `validToken` is opaque. Nothing here shows the agent
      cannot produce a token satisfying it. All suspension-absorbing results hold
      only modulo A1.
  A2. Capability bound is external. `allowedCapLimit` is supplied by the TCB.
      `autonomousExpandCap` lets the agent grow `cap` monotonically up to that
      bound. Lemma 1 bounds capability; it does not restrict growth.
      GATING (added): `requires : ActionId -> CapId` names the capability each
      action consumes, and `allowedActions` now filters `policy` by whether
      that capability is held. Before this, `cap` was written by `step` and
      read by nothing, so Lemma 1 constrained state with no effect on
      behaviour. Lemma 7 is the consequence that was previously unstatable:
      an executable action's required capability lies within the TCB bound.
  A3. Single-writer semantics. No concurrency, no interleaving, no side channels.
  A4. No influence model. Nothing here bounds the agent's causal influence over
      whoever holds the ratification token (Negative Result 1).
-/

import Mathlib.Data.Finset.Basic

/-- Operational states. Kept explicit rather than collapsed to booleans. -/
inductive OpState
  | active
  | degraded
  | uncertain
  | suspended
  | terminated
deriving DecidableEq, Repr

/-- Who originated an event. Separate from whether the event is authenticated. -/
inductive Actor
  | agent
  | human
  | external
deriving DecidableEq, Repr

structure State (CapId ActionId : Type) where
  cap : Finset CapId
  policy : Finset ActionId
  opState : OpState
  lastExecuted : Option ActionId

inductive Event (CapId ActionId Token : Type) where
  | autonomousPropose : Finset ActionId → Event CapId ActionId Token
  | autonomousExpandCap : CapId → Event CapId ActionId Token
  | authenticatedRatification : Token → Finset ActionId → Event CapId ActionId Token
  | externalSuspend : Event CapId ActionId Token
  | execute : ActionId → Event CapId ActionId Token

def actor {CapId ActionId Token : Type} (e : Event CapId ActionId Token) : Actor :=
  match e with
  | .autonomousPropose _ => .agent
  | .autonomousExpandCap _ => .agent
  | .authenticatedRatification _ _ => .human
  | .externalSuspend => .external
  | .execute _ => .agent

/-- Execution eligibility = policy gated by operational state.
    Capabilities are never mutated to implement suspension (Model B). -/
def allowedActions {CapId ActionId : Type} [DecidableEq CapId]
    (requires : ActionId → CapId) (s : State CapId ActionId) : Finset ActionId :=
  match s.opState with
  | .active => s.policy.filter (fun a => requires a ∈ s.cap)
  | .degraded => s.policy.filter (fun a => requires a ∈ s.cap)
  | .uncertain => ∅
  | .suspended => ∅
  | .terminated => ∅

@[reducible]
def canExecute {CapId ActionId : Type} [DecidableEq CapId]
    (requires : ActionId → CapId) (s : State CapId ActionId) (a : ActionId) : Prop :=
  a ∈ allowedActions requires s

/-- The reference monitor. Every branch is a total function on states;
    rejected events yield a null transition. -/
def step {CapId ActionId Token : Type}
    [DecidableEq CapId] [DecidableEq ActionId] [DecidableEq Token]
    (requires : ActionId → CapId)
    (allowedCapLimit : Finset CapId) (validToken : Token → Prop) [DecidablePred validToken]
    (s : State CapId ActionId) (e : Event CapId ActionId Token) : State CapId ActionId :=
  match e with
  | .autonomousPropose newPolicy =>
      if newPolicy ⊆ s.policy then { s with policy := newPolicy } else s
  | .autonomousExpandCap c =>
      if c ∈ allowedCapLimit then { s with cap := insert c s.cap } else s
  | .authenticatedRatification token newPolicy =>
      if validToken token then { s with policy := newPolicy } else s
  | .externalSuspend =>
      { s with opState := .suspended, policy := ∅ }
  | .execute a =>
      if canExecute requires s a then { s with lastExecuted := some a } else s

def capInvariant {CapId ActionId : Type}
    (allowedCapLimit : Finset CapId) (s : State CapId ActionId) : Prop :=
  s.cap ⊆ allowedCapLimit

section Lemmas

variable {CapId ActionId Token : Type}
  [DecidableEq CapId] [DecidableEq ActionId] [DecidableEq Token]
  (requires : ActionId → CapId)
  (allowedCapLimit : Finset CapId) (validToken : Token → Prop) [DecidablePred validToken]

/-- Lemma 1. Capability stays within the externally supplied bound. See A2. -/
theorem step_preserves_capInvariant
    (s : State CapId ActionId) (e : Event CapId ActionId Token)
    (h : capInvariant allowedCapLimit s) :
    capInvariant allowedCapLimit (step requires allowedCapLimit validToken s e) := by
  cases e with
  | autonomousPropose _ =>
      simp only [step, capInvariant]
      split <;> exact h
  | autonomousExpandCap c =>
      simp only [step, capInvariant]
      split
      · rename_i hc
        exact Finset.insert_subset hc h
      · exact h
  | authenticatedRatification _ _ =>
      simp only [step, capInvariant]
      split <;> exact h
  | externalSuspend =>
      simp only [step, capInvariant]
      exact h
  | execute _ =>
      simp only [step, capInvariant]
      split <;> exact h

/-- Lemma 2. No agent event expands policy. Ratification is excluded by `hAgent`. -/
theorem step_agent_policy_monotone
    (s : State CapId ActionId) (e : Event CapId ActionId Token)
    (hAgent : actor e = Actor.agent) :
    (step requires allowedCapLimit validToken s e).policy ⊆ s.policy := by
  cases e with
  | autonomousPropose newPolicy =>
      simp only [step]
      split
      · rename_i h_sub; exact h_sub
      · exact subset_rfl
  | autonomousExpandCap c =>
      simp only [step]
      split <;> exact subset_rfl
  | authenticatedRatification _ _ => simp [actor] at hAgent
  | externalSuspend => simp [actor] at hAgent
  | execute a =>
      simp only [step]
      split <;> exact subset_rfl

/-- Lemma 3. Unauthorized execution is a null transition.
    Non-trivial because authorized execution does mutate `lastExecuted`. -/
theorem unauthorized_execution_is_blocked
    (s : State CapId ActionId) (a : ActionId) (h : ¬ canExecute requires s a) :
    step requires allowedCapLimit validToken s (.execute a) = s := by
  simp only [step, if_neg h]

/-- Companion to Lemma 3: authorized execution is *not* a null transition,
    which is what makes Lemma 3 say something. -/
theorem authorized_execution_records
    (s : State CapId ActionId) (a : ActionId) (h : canExecute requires s a) :
    (step requires allowedCapLimit validToken s (.execute a)).lastExecuted = some a := by
  simp only [step, if_pos h]

/-- Lemma 4. Single-step: suspension survives any agent event. -/
theorem suspension_is_irreversible_under_agent_events
    (s : State CapId ActionId) (e : Event CapId ActionId Token)
    (hSusp : s.opState = .suspended) (hAgent : actor e = Actor.agent) :
    (step requires allowedCapLimit validToken s e).opState = .suspended := by
  cases e with
  | autonomousPropose newPolicy =>
      simp only [step]
      split <;> exact hSusp
  | autonomousExpandCap c =>
      simp only [step]
      split <;> exact hSusp
  | authenticatedRatification _ _ => simp [actor] at hAgent
  | externalSuspend => simp [actor] at hAgent
  | execute a =>
      have h_no_exec : ¬ canExecute requires s a := by
        simp [canExecute, allowedActions, hSusp]
      simp only [step, if_neg h_no_exec]
      exact hSusp

/-- Lemma 5. Multi-step: suspension is absorbing over any pure-agent trace.
    Holds modulo A1 — a forged token escapes this. -/
theorem suspended_absorbing
    (es : List (Event CapId ActionId Token)) :
    ∀ (s : State CapId ActionId), s.opState = .suspended →
      (∀ e ∈ es, actor e = Actor.agent) →
      (es.foldl (step requires allowedCapLimit validToken) s).opState = .suspended := by
  induction es with
  | nil => intro s hs _; exact hs
  | cons e es ih =>
      intro s hs hAll
      simp only [List.foldl_cons]
      refine ih _ ?_ ?_
      · exact suspension_is_irreversible_under_agent_events requires allowedCapLimit validToken s e hs
          (hAll e (by simp))
      · intro e' he'; exact hAll e' (by simp [he'])

/-- Lemma 6. Multi-step: policy never grows over a pure-agent trace.
    This is the bound on what the agent can do, as opposed to what label it wears. -/
theorem policy_monotone_absorbing
    (es : List (Event CapId ActionId Token)) :
    ∀ (s : State CapId ActionId),
      (∀ e ∈ es, actor e = Actor.agent) →
      (es.foldl (step requires allowedCapLimit validToken) s).policy ⊆ s.policy := by
  induction es with
  | nil => intro s _; exact subset_rfl
  | cons e es ih =>
      intro s hAll
      simp only [List.foldl_cons]
      have h_step := step_agent_policy_monotone requires allowedCapLimit validToken s e (hAll e (by simp))
      have h_rest := ih (step requires allowedCapLimit validToken s e)
        (fun e' he' => hAll e' (by simp [he']))
      exact h_rest.trans h_step

/-- Lemma 7. **Capability gating is behaviourally meaningful.**
    If capability stays within the TCB bound, then every executable action
    consumes a capability inside that bound.

    This is the theorem that could not be stated before gating: previously
    `cap` was write-only, so `capInvariant` constrained nothing observable.
    It is the formal content of registered assumption A2 — the external bound
    now bounds *behaviour*, not just a field. -/
theorem execution_confined_by_cap_bound
    (s : State CapId ActionId) (a : ActionId)
    (hCap : capInvariant allowedCapLimit s)
    (hExec : canExecute requires s a) :
    requires a ∈ allowedCapLimit := by
  have hmem : requires a ∈ s.cap := by
    have h := hExec
    unfold canExecute allowedActions at h
    split at h
    · exact (Finset.mem_filter.mp h).2
    · exact (Finset.mem_filter.mp h).2
    · simp at h
    · simp at h
    · simp at h
  exact hCap hmem

end Lemmas

#print axioms step_preserves_capInvariant
#print axioms step_agent_policy_monotone
#print axioms unauthorized_execution_is_blocked
#print axioms authorized_execution_records
#print axioms suspension_is_irreversible_under_agent_events
#print axioms suspended_absorbing
#print axioms policy_monotone_absorbing
#print axioms execution_confined_by_cap_bound
