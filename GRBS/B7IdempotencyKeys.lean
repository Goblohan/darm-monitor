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
