/-
  B7 — IDEMPOTENCY KEYS: AT-MOST-ONCE EFFECT (DARM Guard 0.8.1)

  B6's cas_retry_idempotent is a FINAL-STATE property: it cannot tell "no
  second effect" from "a second effect landing in the same state". A keyless
  retry in DARM Guard does the latter (it writes again, same content). The
  property that prevents a repeated effect is the idempotency key, modelled
  here: a completed key short-circuits before any effect.

  Proved: once a key is recorded, handling it again changes nothing
  (keyed_repeat_no_effect); submitting the same keyed request any number of
  times yields exactly one effect (at_most_once), counted as effects, not
  inferred from state.

  Not modelled: prepared/executed/done are one step here; in the
  implementation a crash between them leaves the key pending until startup
  reconciliation (tested by probes P3, P7). The key table's persistence
  across restarts rests on the audit log (A5).
-/

namespace DARM.Idempotency

inductive KState where
  | pending
  | done
  deriving DecidableEq, Repr

structure Entry where
  hash : Nat
  state : KState

inductive Outcome where
  | executed
  | alreadyApplied
  | rejectedMismatch
  | rejectedUnresolved
  deriving DecidableEq, Repr

structure St where
  table : String → Option Entry
  effects : List Nat   -- one element per effect actually performed

/-- One keyed request, mirroring broker.py lines 541-553. -/
def handleKeyed (s : St) (k : String) (h : Nat) : St × Outcome :=
  match s.table k with
  | some e =>
    if e.hash = h then
      (if e.state = KState.done then (s, Outcome.alreadyApplied) else (s, Outcome.rejectedUnresolved))
    else (s, Outcome.rejectedMismatch)
  | none =>
    ({ table := fun x => if x = k then some ⟨h, KState.done⟩ else s.table x,
       effects := s.effects ++ [h] }, Outcome.executed)

/-- Once a key is recorded, handling it again changes nothing. -/
theorem keyed_repeat_no_effect (s : St) (k : String) (h : Nat) (e : Entry)
    (hk : s.table k = some e) : (handleKeyed s k h).1 = s := by
  by_cases h1 : e.hash = h <;> by_cases h2 : e.state = KState.done <;>
    simp [handleKeyed, hk, h1, h2]

def repeatN (s : St) (k : String) (h : Nat) : Nat → St
  | 0 => s
  | n + 1 => (handleKeyed (repeatN s k h n) k h).1

/-- The same keyed request, submitted any number of times (at least once),
    yields exactly one effect. -/
theorem at_most_once (s : St) (k : String) (h : Nat) (hk : s.table k = none) (n : Nat) :
    (repeatN s k h (n + 1)).effects = s.effects ++ [h] ∧
    (repeatN s k h (n + 1)).table k = some ⟨h, KState.done⟩ := by
  induction n with
  | zero => simp [repeatN, handleKeyed, hk]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [show repeatN s k h (n + 1 + 1) = (handleKeyed (repeatN s k h (n + 1)) k h).1 from rfl]
    simp [handleKeyed, h2, h1]

end DARM.Idempotency

#print axioms DARM.Idempotency.keyed_repeat_no_effect
#print axioms DARM.Idempotency.at_most_once

/-! ## B7b: attempts that fail (DARM Guard 0.8.2)

The model above assumes every first attempt produces its effect. The
implementation can also fail an attempt (a conflict, a refused symlink), and
reconciliation can leave one unresolved. 0.8.1 marked every closed key done,
so a retry after a failure was reported 'already applied' (probes P11, P12).
Here a key records what happened, and 'already applied' is returned only
for a key whose effect is in the effect log. The governed effect is the file
mutation itself; a failed attempt leaves the file as it was.

Not modelled: the mapping from reconciliation verdicts (confirmedSuccess to
done, confirmedFailure to failed, unresolved stays pending). confirmedSuccess
is state correspondence, not attribution (B5), so a foreign write of the
identical content would also map to done.
-/

namespace DARM.Idempotency2

inductive KState where
  | pending
  | done
  | failed
  deriving DecidableEq, Repr

structure Entry where
  hash : Nat
  state : KState

inductive Outcome where
  | executed
  | failedExec
  | alreadyApplied
  | rejectedFailed
  | rejectedMismatch
  | rejectedUnresolved
  deriving DecidableEq, Repr

structure St where
  table : String → Option Entry
  effects : List Nat

/-- One keyed attempt; `ok` is whether a first execution succeeds. -/
def handle (s : St) (k : String) (h : Nat) (ok : Bool) : St × Outcome :=
  match s.table k with
  | some e =>
    if e.hash = h then
      (if e.state = KState.done then (s, Outcome.alreadyApplied)
       else if e.state = KState.failed then (s, Outcome.rejectedFailed)
       else (s, Outcome.rejectedUnresolved))
    else (s, Outcome.rejectedMismatch)
  | none =>
    if ok then
      ({ table := fun x => if x = k then some ⟨h, KState.done⟩ else s.table x,
         effects := s.effects ++ [h] }, Outcome.executed)
    else
      ({ table := fun x => if x = k then some ⟨h, KState.failed⟩ else s.table x,
         effects := s.effects }, Outcome.failedExec)

theorem repeat_no_effect (s : St) (k : String) (h : Nat) (ok : Bool) (e : Entry)
    (hk : s.table k = some e) : (handle s k h ok).1 = s := by
  by_cases h1 : e.hash = h <;> by_cases h2 : e.state = KState.done <;>
    by_cases h3 : e.state = KState.failed <;> simp [handle, hk, h1, h2, h3]

/-- Every done key's effect is in the effect log. -/
def Sound (s : St) : Prop :=
  ∀ k e, s.table k = some e → e.state = KState.done → e.hash ∈ s.effects

theorem handle_preserves_sound (s : St) (k : String) (h : Nat) (ok : Bool) (hs : Sound s) :
    Sound (handle s k h ok).1 := by
  cases hk : s.table k with
  | some e => rw [repeat_no_effect s k h ok e hk]; exact hs
  | none =>
    intro x e' hx hd
    by_cases hxk : x = k
    · subst hxk
      cases ok
      · simp [handle, hk] at hx; subst hx; simp at hd
      · simp [handle, hk] at hx; subst hx; simp [handle, hk]
    · have hx' : s.table x = some e' := by cases ok <;> simpa [handle, hk, hxk] using hx
      have hin := hs x e' hx' hd
      cases ok <;> simp [handle, hk, hin]

/-- 'Already applied' is returned only for an effect that is in the log. -/
theorem already_applied_sound (s : St) (k : String) (h : Nat) (ok : Bool) (hs : Sound s)
    (hout : (handle s k h ok).2 = Outcome.alreadyApplied) : h ∈ s.effects := by
  cases hk : s.table k with
  | none => cases ok <;> simp [handle, hk] at hout
  | some e =>
    simp only [handle, hk] at hout
    split at hout
    · rename_i h1
      split at hout
      · rename_i h2
        rw [← h1]
        exact hs k e hk h2
      · split at hout <;> simp at hout
    · simp at hout

def run (s : St) (k : String) (h : Nat) : List Bool → St
  | [] => s
  | ok :: oks => run (handle s k h ok).1 k h oks

theorem run_stable (s : St) (k : String) (h : Nat) (e : Entry) (hk : s.table k = some e)
    (oks : List Bool) : run s k h oks = s := by
  induction oks with
  | nil => rfl
  | cons ok oks ih => simp only [run, repeat_no_effect s k h ok e hk]; exact ih

/-- Any number of attempts with one key: one effect if the first attempt
    succeeded, none if it failed. Never two. -/
theorem at_most_once_with_failures (s : St) (k : String) (h : Nat) (hk : s.table k = none)
    (ok : Bool) (oks : List Bool) :
    (run s k h (ok :: oks)).effects = s.effects ++ (if ok then [h] else []) := by
  have hex : ∃ e, (handle s k h ok).1.table k = some e := by
    cases ok <;> simp [handle, hk]
  obtain ⟨e, he⟩ := hex
  simp only [run]
  rw [run_stable _ k h e he oks]
  cases ok <;> simp [handle, hk]

end DARM.Idempotency2

#print axioms DARM.Idempotency2.handle_preserves_sound
#print axioms DARM.Idempotency2.already_applied_sound
#print axioms DARM.Idempotency2.at_most_once_with_failures
