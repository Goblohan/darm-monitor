/-
  E27b — EXECUTION IDENTITY IN A HISTORY

  E27 derives, from B8's definitions, that an attested file at a path
  consistent with the log forces the log's latest entry for it to be the write
  under that request identifier. This file connects that entry to the broker
  operation, in the world's actual history, that produced it.

  A history is a list of events, each a broker operation (write, delete,
  rename) or a foreign action (delete, tamper, create, move), applied in order.
  Each broker operation appends exactly its own entries to the log (apply_log;
  a rename appends two: the destination's write and the source's delete);
  foreign actions append nothing (foreign_log). So every entry in the final log
  was there at the start or was appended by a broker operation occurring in the
  history (log_provenance), and an entry write rid d at t can only come from a
  write of d to t under rid, or a rename under rid that landed d at t
  (write_entry_from).

  Result: from the empty world, in any history, if the final world is
  consistent and the file at t carries attestation (rid, d), the history
  contains a broker operation under rid that put d at t, a write or a rename
  (attested_file_was_placed_by_broker). When it is the write, E27's
  logged_write_corresponds says it corresponds to an invocation carrying the
  pinned payload; when it is a rename, identity holds under the rename's
  request.

  NOT claimed: which invocation a rename corresponds to (E26's ExecCorresponds
  covers writes only); anything about histories that do not start from the
  empty world beyond what their initial log already contains; B8's attestation
  binding the path (it does not; see E27's witness).
-/
import E27ExecutionIdentity

namespace DARM.E27b

open DARM.EffectIntegrity2

inductive Foreign where
  | del (t : String)
  | tamper (t d : String)
  | create (t d : String)
  | move (s t : String)

inductive Event where
  | broker (op : BrokerOp)
  | foreign (f : Foreign)

def applyForeign (w : World) : Foreign → World
  | .del t => foreignDelete w t
  | .tamper t d => tamper w t d
  | .create t d => create w t d
  | .move s t => foreignMove w s t

def step (w : World) : Event → World
  | .broker op => apply w op
  | .foreign f => applyForeign w f

/-- The world after a history, events applied in order. -/
def evolve (w : World) : List Event → World
  | [] => w
  | e :: es => evolve (step w e) es

/-- The entries a broker operation appends, newest first. -/
def logOf : BrokerOp → List Entry
  | .wr r t d => [⟨r, t, Op.write d⟩]
  | .dl r t => [⟨r, t, Op.del⟩]
  | .mv r s t d => [⟨r, t, Op.write d⟩, ⟨r, s, Op.del⟩]

theorem apply_log (w : World) (op : BrokerOp) : (apply w op).log = logOf op ++ w.log := by
  cases op <;> rfl

theorem foreign_log (w : World) (f : Foreign) : (applyForeign w f).log = w.log := by
  cases f <;> rfl

/-- Every entry in the final log was there at the start, or was appended by a
    broker operation occurring in the history. -/
theorem log_provenance (h : List Event) :
    ∀ (w : World) (e : Entry), e ∈ (evolve w h).log →
      e ∈ w.log ∨ ∃ op, Event.broker op ∈ h ∧ e ∈ logOf op := by
  induction h with
  | nil => intro w e he; exact Or.inl he
  | cons ev rest ih =>
    intro w e he
    rcases ih (step w ev) e he with h1 | ⟨op, hop, hin⟩
    · cases ev with
      | broker op =>
        simp only [step, apply_log, List.mem_append] at h1
        rcases h1 with h2 | h2
        · exact Or.inr ⟨op, by simp, h2⟩
        · exact Or.inl h2
      | foreign f =>
        simp only [step, foreign_log] at h1
        exact Or.inl h1
    · exact Or.inr ⟨op, by simp [hop], hin⟩

/-- An entry write rid d at t comes from a write of d to t under rid, or from
    a rename under rid that landed d at t. -/
theorem write_entry_from (op : BrokerOp) (rid : Nat) (t d : String)
    (h : (⟨rid, t, Op.write d⟩ : Entry) ∈ logOf op) :
    op = BrokerOp.wr rid t d ∨ ∃ s, op = BrokerOp.mv rid s t d := by
  cases op with
  | wr r x y =>
    simp [logOf] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inl rfl
  | dl r x => simp [logOf] at h
  | mv r s x y =>
    simp [logOf] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inr ⟨s, rfl⟩

/-- The latest entry for a path is in the log. -/
theorem latest_mem {log : List Entry} {t : String} {e : Entry}
    (h : latest log t = some e) : e ∈ log := by
  induction log with
  | nil => simp [latest] at h
  | cons x rest ih =>
    simp only [latest] at h
    split at h
    · simp at h
      simp [h]
    · simp [ih h]

/-- Execution identity in a history: from the empty world, if the final world
    is consistent and the file at t carries attestation (rid, d), the history
    contains a broker operation under rid that put d at t. -/
theorem attested_file_was_placed_by_broker (h : List Event)
    (hc : Consistent (evolve empty h)) (t : String) (f : File) (rid : Nat) (d : String)
    (hf : (evolve empty h).files t = some f) (hatt : f.att = some (rid, d)) :
    ∃ op, Event.broker op ∈ h ∧ (op = BrokerOp.wr rid t d ∨ ∃ s, op = BrokerOp.mv rid s t d) := by
  have hl := (DARM.E27.consistent_attested_identifies_write _ hc t f rid d hf hatt).1
  rcases log_provenance h empty _ (latest_mem hl) with h0 | ⟨op, hop, hin⟩
  · simp [empty] at h0
  · exact ⟨op, hop, write_entry_from op rid t d hin⟩

end DARM.E27b

#print axioms DARM.E27b.apply_log
#print axioms DARM.E27b.log_provenance
#print axioms DARM.E27b.write_entry_from
#print axioms DARM.E27b.latest_mem
#print axioms DARM.E27b.attested_file_was_placed_by_broker
