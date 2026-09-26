/-
  B6c — RENAME AS ONE COMPOUND COMPARE-AND-SWAP

  B6 proves compare-and-swap slot by slot (casOpt). A rename touches two
  slots, and two independent single-slot operations can half-apply: delete
  the source, then find the destination occupied and fail to write it, losing
  the content. casMove is the compound transition: if the source holds the
  expected value and the destination is absent, move; otherwise change
  nothing, in either slot.

  Proved (generic over any type with decidable equality): casMove applies
  exactly when the source matches and the destination is absent; on conflict
  both slots are unchanged; content is moved, never copied or lost. For B6's
  strings, casMove is B6's delete on the source and create on the destination
  taken together: its success is the conjunction of theirs. A witness shows
  the independent pair losing content where casMove does not.

  Bridges to B9 (attestations erased): B9's normal run (claim, reattest, place)
  ends in exactly casMove's applied state, and B9's recovery of a claim whose
  destination is occupied ends in exactly casMove's conflict state. So B9's
  multi-step protocol, crash recovery included, realizes this single atomic
  transition on the source and destination.

  NOT claimed: the private slot is outside casMove (B9 proves it is empty at
  the end of both runs); the bridges are shown on B9's witness states, not for
  all states.
-/
import B6EffectIntegrity
import B9RenameProtocol

namespace DARM.CompoundRename

open DARM.EffectIntegrity (casOpt)
open DARM.RenameProtocol (FS Val claim reattest place recover start blocked)

/-- Move `v` from `src` to an absent `dst`, or change nothing. -/
def casMove {α : Type} [DecidableEq α] (src dst : Option α) (v : α) :
    (Option α × Option α) × Bool :=
  if src = some v ∧ dst = none then ((none, some v), true) else ((src, dst), false)

theorem casMove_applies_iff {α : Type} [DecidableEq α] (src dst : Option α) (v : α) :
    (casMove src dst v).2 = true ↔ src = some v ∧ dst = none := by
  unfold casMove
  split <;> simp_all

theorem casMove_conflict_preserves {α : Type} [DecidableEq α] (src dst : Option α) (v : α)
    (h : ¬ (src = some v ∧ dst = none)) :
    (casMove src dst v).1 = (src, dst) := by
  unfold casMove
  rw [if_neg h]

theorem casMove_moves {α : Type} [DecidableEq α] (src dst : Option α) (v : α)
    (h : src = some v ∧ dst = none) :
    (casMove src dst v).1 = (none, some v) := by
  unfold casMove
  rw [if_pos h]

/-- Moved, never copied or lost: the same contents, before and after. -/
theorem casMove_conserves {α : Type} [DecidableEq α] (src dst : Option α) (v : α) :
    [(casMove src dst v).1.1, (casMove src dst v).1.2].filterMap id = [src, dst].filterMap id := by
  unfold casMove
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    rfl
  · rfl

/-- For B6's strings: casMove is the source delete and the destination create,
    taken together. It succeeds exactly when both would, and then has both effects. -/
theorem casMove_is_both_casOpts (src dst : Option String) (v : String) :
    (casMove src dst v).2 = ((casOpt src (some v) none).2 && (casOpt dst none (some v)).2) ∧
    ((casMove src dst v).2 = true →
      (casMove src dst v).1 = ((casOpt src (some v) none).1, (casOpt dst none (some v)).1)) := by
  unfold casMove casOpt
  by_cases h1 : src = some v <;> by_cases h2 : dst = none <;> simp_all

/-- Independently, the source delete can apply while the destination create
    fails, losing the content; casMove leaves both slots as they were. -/
theorem independent_pair_can_lose :
    (casOpt (some "a") (some "a") none).1 = none ∧
    (casOpt (some "b") none (some "a")).2 = false ∧
    (casMove (some "a") (some "b") "a").1 = (some "a", some "b") := by
  decide +kernel

/-! ## Bridges to B9 (attestations erased) -/

def erase : Option Val → Option String
  | some (Val.mine _) => some "mine"
  | some Val.foreign => some "foreign"
  | none => none

def proj (s : FS) : Option String × Option String := (erase s.src, erase s.dst)

theorem normal_run_realizes_casMove :
    proj (place (reattest (claim start))) = (casMove (erase start.src) (erase start.dst) "mine").1 := by
  decide +kernel

theorem occupied_recovery_realizes_conflict :
    proj (recover (claim blocked)) = (casMove (erase blocked.src) (erase blocked.dst) "mine").1 := by
  decide +kernel

end DARM.CompoundRename

#print axioms DARM.CompoundRename.casMove_applies_iff
#print axioms DARM.CompoundRename.casMove_conflict_preserves
#print axioms DARM.CompoundRename.casMove_conserves
#print axioms DARM.CompoundRename.casMove_is_both_casOpts
#print axioms DARM.CompoundRename.independent_pair_can_lose
#print axioms DARM.CompoundRename.normal_run_realizes_casMove
#print axioms DARM.CompoundRename.occupied_recovery_realizes_conflict
