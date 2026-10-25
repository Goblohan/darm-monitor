/-
  B10b — ABORT AFTER DISPATCH, WITH EXECUTOR EVIDENCE

  B10 assumed the witness learns nothing on abort but whether DISPATCHED was
  recorded; then the only honest record after DISPATCHED is UNKNOWN. Testing
  patch v1 (UNKNOWN + SUSPENDED for every post-dispatch abort) on darmd showed
  that is honest but over-conservative: write_exchange_race and
  rename_destination_race regressed to PROPOSAL_DENIED:PROFILE_SUSPENDED,
  because darmd's correct stale-detection rollback now halts the system.

  B10b adds one bit to the abort message: `ev`, the executor's claim that the
  effect provably did not happen (a failed atomic rename, or a swap-back whose
  result is checked and whose state is re-verified). Evidence is SOUND when
  ev = true implies eff = false.

  Proved:
    honest_iff              exact characterization of honest policies over
                            (dispatched, evidence)
    v1_honest, v2_honest    both patches are honest
    v1_over_suspends        v1 latches in a consistent world with proven rollback
                            (what the full-suite run observed)
    v2_least_latching       v2 latches only where honesty forces a latch: every
                            honest policy latches wherever v2 does
    v2_latches_iff          v2 latches exactly when dispatched without evidence
    no_evidence_recovers_b10  a policy that ignores evidence must latch after
                            DISPATCHED (B10 as a corollary)
    v2_needs_sound_evidence if evidence could be unsound, v2 can record ABORTED
                            over a live effect: v2's honesty rests on the
                            executor's evidence, and this states that trust

  NOT claimed: that darmd's executor computes `ev` soundly. That is an
  implementation obligation, checked by the Gate 7 cases, not by this model.
-/
import B10AbortAfterDispatch

namespace DARM.AbortEvidence

open DARM.AbortAfterDispatch (Term honest)

/-- Consistent worlds: no effect without DISPATCHED, and evidence is sound. -/
def Consistent (d ev eff : Bool) : Bool := (!eff || d) && (!ev || !eff)

/-- On abort the witness sees DISPATCHED and the executor's evidence bit. -/
abbrev Policy := Bool → Bool → Term

def HonestPolicy (P : Policy) : Prop :=
  ∀ d ev eff : Bool, Consistent d ev eff = true → honest (P d ev) eff = true

/-- Patch v1: ignore evidence; UNKNOWN after DISPATCHED. -/
def v1 : Policy := fun d _ => if d then .unknown else .aborted

/-- Patch v2: UNKNOWN only after DISPATCHED without evidence. -/
def v2 : Policy := fun d ev => if d && !ev then .unknown else .aborted

def latches (P : Policy) (d ev : Bool) : Bool := P d ev == .unknown

/-! ## Characterization -/

theorem honest_iff (P : Policy) :
    HonestPolicy P ↔
      (P true false = .unknown ∧ P true true ≠ .receipted ∧
       P false false ≠ .receipted ∧ P false true ≠ .receipted) := by
  constructor
  · intro h
    have a1 := h true false true (by decide)
    have a2 := h true false false (by decide)
    have b := h true true false (by decide)
    have c := h false false false (by decide)
    have e := h false true false (by decide)
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases hp : P true false with
      | receipted => rw [hp] at a2; exact absurd a2 (by decide)
      | aborted => rw [hp] at a1; exact absurd a1 (by decide)
      | unknown => rfl
    · intro hr; rw [hr] at b; exact absurd b (by decide)
    · intro hr; rw [hr] at c; exact absurd c (by decide)
    · intro hr; rw [hr] at e; exact absurd e (by decide)
  · intro ⟨h1, h2, h3, h4⟩ d ev eff hc
    cases d <;> cases ev <;> cases eff
    -- d = false, ev = false, eff = false
    · cases hp : P false false with
      | receipted => exact absurd hp h3
      | aborted => simp [honest]
      | unknown => simp [honest]
    · exact absurd hc (by decide)
    -- d = false, ev = true, eff = false
    · cases hp : P false true with
      | receipted => exact absurd hp h4
      | aborted => simp [honest]
      | unknown => simp [honest]
    · exact absurd hc (by decide)
    -- d = true, ev = false
    · simp [h1, honest]
    · simp [h1, honest]
    -- d = true, ev = true, eff = false
    · cases hp : P true true with
      | receipted => exact absurd hp h2
      | aborted => simp [honest]
      | unknown => simp [honest]
    · exact absurd hc (by decide)

/-! ## The two patches -/

theorem v1_honest : HonestPolicy v1 :=
  (honest_iff v1).mpr ⟨rfl, by decide, by decide, by decide⟩

theorem v2_honest : HonestPolicy v2 :=
  (honest_iff v2).mpr ⟨rfl, by decide, by decide, by decide⟩

/-- Dispatched, rollback proven, effect absent: v1 still latches. -/
theorem v1_over_suspends :
    Consistent true true false = true ∧ latches v1 true true = true := by
  decide

theorem v2_latches_iff (d ev : Bool) : latches v2 d ev = (d && !ev) := by
  cases d <;> cases ev <;> decide

/-- v2 latches only where every honest policy must. -/
theorem v2_least_latching (P : Policy) (h : HonestPolicy P) (d ev : Bool)
    (hl : latches v2 d ev = true) : latches P d ev = true := by
  have hu := ((honest_iff P).mp h).1
  cases d <;> cases ev
  · exact absurd hl (by decide)
  · exact absurd hl (by decide)
  · simp [latches, hu]
  · exact absurd hl (by decide)

/-- B10 as a corollary: a policy that ignores evidence must latch after DISPATCHED. -/
theorem no_evidence_recovers_b10 (P : Policy) (h : HonestPolicy P)
    (hind : ∀ d, P d true = P d false) (ev : Bool) : P true ev = .unknown := by
  have hu := ((honest_iff P).mp h).1
  cases ev
  · exact hu
  · rw [hind true]; exact hu

/-- If evidence could be unsound (ev = true while the effect happened), v2 records
    ABORTED over a live effect. v2's honesty rests on the executor's evidence. -/
theorem v2_needs_sound_evidence :
    Consistent true true true = false ∧ honest (v2 true true) true = false := by
  decide

end DARM.AbortEvidence

#print axioms DARM.AbortEvidence.honest_iff
#print axioms DARM.AbortEvidence.v2_least_latching
#print axioms DARM.AbortEvidence.v1_over_suspends
