/-
  B10 — ABORT AFTER DISPATCH: WHAT THE WITNESS MAY RECORD

  Source finding (darmd M3, appliance 0.1.2 / core 0.5.2, src/main.rs):
  the witness 'abort' handler appends ABORTED with no check for a prior
  DISPATCHED. The executor sends abort on post-dispatch failures, including
  unlinkat(tmp) failing after a verified EXCHANGE, when the new content is
  already live. An ABORTED record then sits over an effect that happened:
  a silent effect of the kind B4 rules out in the model.

  Model. One permit. The world bit `eff` says whether the effect reached the
  governed target. Effects happen only after DISPATCHED (Consistent). On an
  abort message the witness sees only whether DISPATCHED was recorded; the
  message carries no evidence about `eff`. An abort policy maps that one bit
  to a terminal record. A record is honest when RECEIPTED means the effect
  happened, ABORTED means it did not, and UNKNOWN claims nothing.

  Proved:
    naive_silent_effect         darmd 0.5.2's policy records ABORTED over a
                                dispatched effect that happened
    naive_not_honest            so that policy is not honest
    post_dispatch_must_be_unknown  every honest policy records UNKNOWN after
                                DISPATCHED (deletion witness: drop the
                                DISPATCHED check and honesty fails)
    honest_iff                  exact characterization of honest policies
    guarded_honest              the proposed patch is honest
    guarded_conservative        and changes nothing before DISPATCHED
    guarded_latches             and suspends, so settle's latch now fires on
                                this path too

  Assumed: the witness learns nothing about `eff` from an abort message.
  Confirmed from source: ABORTED is terminal in darmd. Ledger replay
  (main.rs lines 220-231) removes the permit from the open set, and
  recover() reconciles only open permits, so a DISPATCHED-then-ABORTED
  permit is never reconciled. The witness's executed_keys and the
  kernel's per-key versions also miss the effect.

  NOT claimed: that suspension must be system-wide rather than per key.
  This module proves the record must be UNKNOWN and that UNKNOWN latches
  under darmd's existing settle semantics. Necessity of the system-wide
  scope needs a model of cross-key dependence and is left open.
-/

namespace DARM.AbortAfterDispatch

/-- Terminal ledger record for a permit. -/
inductive Term where
  | receipted
  | aborted
  | unknown
deriving DecidableEq, Repr

/-- Is the record honest about the world bit `eff`? -/
def honest : Term → Bool → Bool
  | .receipted, eff => eff
  | .aborted, eff => !eff
  | .unknown, _ => true

/-- Worlds consistent with the ledger: no effect without DISPATCHED. -/
def Consistent (dispatched eff : Bool) : Bool := !eff || dispatched

/-- On abort, the witness sees only whether DISPATCHED was recorded. -/
abbrev AbortPolicy := Bool → Term

/-- darmd 0.5.2: ABORTED regardless of DISPATCHED. -/
def naive : AbortPolicy := fun _ => .aborted

/-- Proposed patch: UNKNOWN after DISPATCHED, ABORTED before. -/
def guarded : AbortPolicy := fun d => if d then .unknown else .aborted

/-- A policy is honest if its record is honest in every consistent world. -/
def HonestPolicy (P : AbortPolicy) : Prop :=
  ∀ d eff : Bool, Consistent d eff = true → honest (P d) eff = true

/-! ## The flaw -/

/-- Dispatched, effect happened, recorded ABORTED: a silent effect. -/
theorem naive_silent_effect :
    Consistent true true = true ∧ honest (naive true) true = false := by
  decide

theorem naive_not_honest : ¬ HonestPolicy naive := by
  intro h
  have h1 := h true true (by decide)
  exact absurd h1 (by decide)

/-! ## Necessity -/

/-- After DISPATCHED, the only honest record is UNKNOWN. -/
theorem post_dispatch_must_be_unknown (P : AbortPolicy) (h : HonestPolicy P) :
    P true = .unknown := by
  have h1 := h true true (by decide)
  have h2 := h true false (by decide)
  cases hp : P true with
  | receipted =>
      rw [hp] at h2
      exact absurd h2 (by decide)
  | aborted =>
      rw [hp] at h1
      exact absurd h1 (by decide)
  | unknown => rfl

/-- Exact characterization of honest abort policies. -/
theorem honest_iff (P : AbortPolicy) :
    HonestPolicy P ↔ (P true = .unknown ∧ P false ≠ .receipted) := by
  constructor
  · intro h
    refine ⟨post_dispatch_must_be_unknown P h, ?_⟩
    intro hr
    have h0 := h false false (by decide)
    rw [hr] at h0
    exact absurd h0 (by decide)
  · intro ⟨ht, hf⟩ d eff hc
    cases d <;> cases eff
    · cases hp : P false with
      | receipted => exact absurd hp hf
      | aborted => simp [honest]
      | unknown => simp [honest]
    · exact absurd hc (by decide)
    · simp [ht, honest]
    · simp [ht, honest]

/-! ## The patch -/

theorem guarded_honest : HonestPolicy guarded :=
  (honest_iff guarded).mpr ⟨rfl, by decide⟩

theorem guarded_conservative : guarded false = naive false := rfl

/-! ## Latching, under darmd's settle semantics (UNKNOWN ⇒ SUSPENDED) -/

structure WState where
  terminal : Term
  suspended : Bool
deriving DecidableEq, Repr

def onAbort (P : AbortPolicy) (d suspended : Bool) : WState :=
  let t := P d
  { terminal := t, suspended := suspended || t == .unknown }

theorem guarded_latches (s : Bool) : (onAbort guarded true s).suspended = true := by
  cases s <;> decide

/-- With the current handler the abort path never latches. -/
theorem naive_never_latches (s : Bool) : (onAbort naive true s).suspended = s := by
  cases s <;> decide

end DARM.AbortAfterDispatch

#print axioms DARM.AbortAfterDispatch.post_dispatch_must_be_unknown
#print axioms DARM.AbortAfterDispatch.honest_iff
#print axioms DARM.AbortAfterDispatch.guarded_honest
