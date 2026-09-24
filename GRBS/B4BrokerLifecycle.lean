/-
  B4 — BROKER LIFECYCLE: EVIDENCE BEFORE EFFECT (DARM Guard 0.7.1)

  The lifecycle of an ADMITTED request (admission is B3/E24's job), with
  each failure point the implementation guards against as an explicit
  fault: the prepared append fails; a crash before the effect; a crash
  after the effect; the outcome append fails.

  Proved: every effect has a prior 'prepared' record (an invariant that
  every step preserves under any faults, hence across any sequence of
  requests); a failed prepared append performs nothing; a 'none' response
  means nothing was performed; for every effect that happened, the log
  reads succeeded or unknown, never none (no silent effect).

  Assumed (the two mechanisms 0.7.1 added): an append that returns has
  reached durable storage (fsync); the effect is all-or-nothing (atomic
  rename). Not modeled: concurrency (discharged by a lock), truncation of
  the most recent log entries (needs an external checkpoint).
-/

namespace DARM.Lifecycle

inductive Event where
  | prepared (rid : Nat)
  | outcome (rid : Nat)
  deriving DecidableEq, Repr

structure State where
  log : List Event
  effects : List Nat

inductive Response where
  | none
  | succeeded
  | outcomeUnrecorded
  | unknown
  deriving DecidableEq, Repr

structure Faults where
  prepareFails : Bool
  crashBeforeEffect : Bool
  crashAfterEffect : Bool
  outcomeFails : Bool

/-- One admitted request, under the given faults. -/
def step (s : State) (rid : Nat) (f : Faults) : State × Response :=
  if f.prepareFails then (s, Response.none)
  else if f.crashBeforeEffect then
    ({ log := s.log ++ [Event.prepared rid], effects := s.effects }, Response.unknown)
  else if f.crashAfterEffect then
    ({ log := s.log ++ [Event.prepared rid], effects := s.effects ++ [rid] }, Response.unknown)
  else if f.outcomeFails then
    ({ log := s.log ++ [Event.prepared rid], effects := s.effects ++ [rid] },
     Response.outcomeUnrecorded)
  else
    ({ log := s.log ++ [Event.prepared rid, Event.outcome rid], effects := s.effects ++ [rid] },
     Response.succeeded)

/-- The invariant: every effect has a prior prepared record. -/
def EvidenceBeforeEffect (s : State) : Prop :=
  ∀ r, r ∈ s.effects → Event.prepared r ∈ s.log

theorem log_only (s : State) (e : List Event) (h : EvidenceBeforeEffect s) :
    EvidenceBeforeEffect { log := s.log ++ e, effects := s.effects } := by
  intro r hr
  exact List.mem_append.mpr (Or.inl (h r hr))

theorem extend (s : State) (rid : Nat) (extra : List Event) (h : EvidenceBeforeEffect s) :
    EvidenceBeforeEffect
      { log := s.log ++ (Event.prepared rid :: extra), effects := s.effects ++ [rid] } := by
  intro r hr
  rw [List.mem_append] at hr
  rcases hr with hr | hr
  · exact List.mem_append.mpr (Or.inl (h r hr))
  · have hr' : r = rid := by simpa using hr
    subst hr'
    simp

/-- Every step preserves the invariant, under any combination of faults. -/
theorem step_preserves (s : State) (rid : Nat) (f : Faults) (h : EvidenceBeforeEffect s) :
    EvidenceBeforeEffect (step s rid f).1 := by
  unfold step
  split
  · exact h
  · split
    · exact log_only s _ h
    · split
      · exact extend s rid [] h
      · split
        · exact extend s rid [] h
        · exact extend s rid [Event.outcome rid] h

def runAll : State → List (Nat × Faults) → State
  | s, [] => s
  | s, (rid, f) :: rest => runAll (step s rid f).1 rest

theorem initial_ok : EvidenceBeforeEffect { log := [], effects := [] } := by
  intro r hr
  simp at hr

/-- Across ANY sequence of requests and faults, every effect has prior evidence. -/
theorem runAll_preserves (s : State) (reqs : List (Nat × Faults)) (h : EvidenceBeforeEffect s) :
    EvidenceBeforeEffect (runAll s reqs) := by
  induction reqs generalizing s with
  | nil => exact h
  | cons x rest ih =>
    rcases x with ⟨rid, f⟩
    exact ih _ (step_preserves s rid f h)

/-- Fail closed: if the prepared record cannot be written, nothing happens. -/
theorem prepare_fails_nothing_performed (s : State) (rid : Nat) (f : Faults)
    (hf : f.prepareFails = true) : (step s rid f).1 = s := by
  simp [step, hf]

/-- Honest responses: 'none' means nothing was performed. -/
theorem none_means_nothing_performed (s : State) (rid : Nat) (f : Faults)
    (h : (step s rid f).2 = Response.none) : (step s rid f).1.effects = s.effects := by
  cases f with
  | mk pf cb ca of =>
    cases pf <;> cases cb <;> cases ca <;> cases of <;> simp_all [step]

/-- Reading the log: succeeded, unknown (prepared, no outcome), or none. -/
def status (log : List Event) (rid : Nat) : Response :=
  if Event.outcome rid ∈ log then Response.succeeded
  else if Event.prepared rid ∈ log then Response.unknown
  else Response.none

/-- No silent effect: for every effect, the log never reads 'none'. -/
theorem no_silent_effect (s : State) (r : Nat) (hs : EvidenceBeforeEffect s)
    (hr : r ∈ s.effects) : status s.log r ≠ Response.none := by
  have hp := hs r hr
  unfold status
  split
  · simp
  · simp

/-- The end-to-end guarantee from an empty start. -/
theorem no_silent_effect_ever (reqs : List (Nat × Faults)) (r : Nat)
    (hr : r ∈ (runAll { log := [], effects := [] } reqs).effects) :
    status (runAll { log := [], effects := [] } reqs).log r ≠ Response.none :=
  no_silent_effect _ r (runAll_preserves _ reqs initial_ok) hr

end DARM.Lifecycle

#print axioms DARM.Lifecycle.runAll_preserves
#print axioms DARM.Lifecycle.prepare_fails_nothing_performed
#print axioms DARM.Lifecycle.none_means_nothing_performed
#print axioms DARM.Lifecycle.no_silent_effect_ever
