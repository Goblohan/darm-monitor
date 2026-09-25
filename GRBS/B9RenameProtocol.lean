/-
  B9 — THE RENAME PROTOCOL: CLAIM, INSPECT, RE-ATTEST, PLACE

  B5 classifies one target's outcome; a rename touches three locations and
  needs recovery, not only classification. B9 models the protocol the broker
  will run, over three slots (source, private name, destination), each empty
  or holding our file (old or new attestation) or foreign content:

    claim     rename source -> private name (moves whatever is there)
    inspect   foreign content claimed -> roll back
    re-attest our file gets the attestation naming the destination
    place     private name -> destination, only if the destination is empty;
              occupied -> roll back

  Rollback returns the claimed file to the source with its original
  attestation (foreign content returns untouched). Recovery after a crash
  reads the private name, which the prepared record names in advance.

  Proved, over every state of three scenarios (normal, destination occupied,
  source replaced), by exhaustive evaluation (decide): each ends as intended;
  our file is in exactly one slot in every state and foreign content is
  never lost or duplicated; a crash after any step recovers to the start or
  the intended end; our file never sits at the source carrying the new
  attestation.

  Assumed: no foreign process guesses the private name (a random suffix).
  Not modelled: content digests (inspect is modelled as ours vs foreign).
-/

namespace DARM.RenameProtocol

inductive Att where
  | old
  | new
  deriving DecidableEq, Repr

inductive Val where
  | mine (a : Att)
  | foreign
  deriving DecidableEq, Repr

structure FS where
  src : Option Val
  priv : Option Val
  dst : Option Val
  deriving DecidableEq, Repr

def claim (s : FS) : FS :=
  match s.src, s.priv with
  | some v, none => { s with src := none, priv := some v }
  | _, _ => s

def reattest (s : FS) : FS :=
  match s.priv with
  | some (Val.mine _) => { s with priv := some (Val.mine Att.new) }
  | _ => s

def place (s : FS) : FS :=
  match s.priv, s.dst with
  | some v, none => { s with priv := none, dst := some v }
  | _, _ => s

/-- The claimed file returns to the source: ours with its original
    attestation, foreign content untouched. -/
def rollback (s : FS) : FS :=
  match s.priv, s.src with
  | some (Val.mine _), none => { s with priv := none, src := some (Val.mine Att.old) }
  | some Val.foreign, none => { s with priv := none, src := some Val.foreign }
  | _, _ => s

/-- Every state the broker's run passes through, in order. -/
def protocol (s : FS) : List FS :=
  let s1 := claim s
  match s1.priv with
  | some Val.foreign => [s, s1, rollback s1]
  | _ =>
    let s2 := reattest s1
    match s2.dst with
    | none => [s, s1, s2, place s2]
    | some _ => [s, s1, s2, rollback s2]

/-- Recovery after a crash, from the private name alone. -/
def recover (s : FS) : FS :=
  match s.priv with
  | some (Val.mine Att.new) => if s.dst = none then place s else rollback s
  | some _ => rollback s
  | none => s

def start : FS := ⟨some (Val.mine Att.old), none, none⟩
def final : FS := ⟨none, none, some (Val.mine Att.new)⟩
def blocked : FS := ⟨some (Val.mine Att.old), none, some Val.foreign⟩
def swapped : FS := ⟨some Val.foreign, none, none⟩

def mineIn : Option Val → Nat
  | some (Val.mine _) => 1
  | _ => 0
def foreignIn : Option Val → Nat
  | some Val.foreign => 1
  | _ => 0
def mineCount (s : FS) : Nat := mineIn s.src + mineIn s.priv + mineIn s.dst
def foreignCount (s : FS) : Nat := foreignIn s.src + foreignIn s.priv + foreignIn s.dst

/-- 1. Outcomes. -/
theorem normal_ends_placed : (protocol start).getLast? = some final := by decide
theorem occupied_destination_restores : (protocol blocked).getLast? = some blocked := by decide
theorem replaced_source_restores : (protocol swapped).getLast? = some swapped := by decide

/-- 2. Conservation: our file is in exactly one slot in every state, and
    foreign content is never lost or duplicated. -/
theorem our_file_never_lost_or_duplicated :
    ∀ s ∈ protocol start ++ protocol blocked, mineCount s = 1 := by decide
theorem foreign_content_conserved :
    (∀ s ∈ protocol blocked, foreignCount s = 1) ∧ (∀ s ∈ protocol swapped, foreignCount s = 1) := by
  decide

/-- 3. Recovery: a crash after any step recovers to the start or the intended end. -/
theorem recovery_normal : ∀ s ∈ protocol start, recover s = start ∨ recover s = final := by decide
theorem recovery_occupied : ∀ s ∈ protocol blocked, recover s = blocked := by decide
theorem recovery_replaced : ∀ s ∈ protocol swapped, recover s = swapped := by decide

/-- 4. Attestation honesty: our file never sits at the source carrying the
    attestation that names the destination. -/
theorem new_attestation_never_at_source :
    ∀ s ∈ protocol start ++ protocol blocked ++ protocol swapped,
      s.src ≠ some (Val.mine Att.new) := by decide

/-- 5. A foreign file appears at the destination during the window, after the
    re-attestation and before the place (NOREPLACE then fails). Rollback must
    undo the re-attestation: the file returns to the source with its original
    attestation, and the foreign file is untouched. -/
def lateTrace : List FS :=
  let s1 := claim start
  let s2 := reattest s1
  let s3 := { s2 with dst := some Val.foreign }
  [start, s1, s2, s3, rollback s3]

theorem late_occupation_restores : lateTrace.getLast? = some blocked := by decide
theorem late_occupation_conserves :
    ∀ s ∈ lateTrace, mineCount s = 1 := by decide
theorem late_occupation_recovers :
    ∀ s ∈ lateTrace, recover s = start ∨ recover s = final ∨ recover s = blocked := by decide
theorem late_occupation_honest :
    ∀ s ∈ lateTrace, s.src ≠ some (Val.mine Att.new) := by decide

/-! ## Recovery from ANY state (after tests/rename_recovery_edges.py)

The theorems above cover the protocol's own traces. These cover all 64
states of the three slots. Found necessary when the implementation was
shown to diverge from B9 in two places: a blocked roll-back changed the
attestation (B9: all or nothing), and recovery stamped our attestation on
foreign content (B9 cannot express this: foreign content has no
attestation field here, so that fix rests on the runtime test). -/

def vals : List (Option Val) := [none, some (Val.mine Att.old), some (Val.mine Att.new), some Val.foreign]

def cross (xs : List (Option Val)) (f : Option Val → List FS) : List FS :=
  match xs with
  | [] => []
  | x :: rest => f x ++ cross rest f

def allStates : List FS :=
  cross vals (fun a => cross vals (fun b => vals.map (fun c => ⟨a, b, c⟩)))

theorem all_states_count : allStates.length = 64 := by decide

/-- Our file, present exactly once, is never lost or duplicated by recovery. -/
theorem recover_conserves_ours :
    ∀ s ∈ allStates, mineCount s = 1 → mineCount (recover s) = 1 := by decide

/-- Foreign content is never lost or duplicated by recovery. -/
theorem recover_conserves_foreign :
    ∀ s ∈ allStates, foreignCount (recover s) = foreignCount s := by decide

/-- All or nothing: if recovery leaves the private name occupied, it changed nothing. -/
theorem recover_all_or_nothing :
    ∀ s ∈ allStates, (recover s).priv ≠ none → recover s = s := by decide

/-- Unresolved, defined: the private name stays occupied only when the source is. -/
theorem recover_stuck_only_if_source_occupied :
    ∀ s ∈ allStates, (recover s).priv = none ∨ s.src ≠ none := by decide

/-- Recovery can be re-run safely. -/
theorem recover_idempotent :
    ∀ s ∈ allStates, recover (recover s) = recover s := by decide

end DARM.RenameProtocol

#print axioms DARM.RenameProtocol.normal_ends_placed
#print axioms DARM.RenameProtocol.our_file_never_lost_or_duplicated
#print axioms DARM.RenameProtocol.foreign_content_conserved
#print axioms DARM.RenameProtocol.recovery_normal
#print axioms DARM.RenameProtocol.recovery_occupied
#print axioms DARM.RenameProtocol.new_attestation_never_at_source
#print axioms DARM.RenameProtocol.late_occupation_restores
#print axioms DARM.RenameProtocol.late_occupation_recovers
#print axioms DARM.RenameProtocol.recover_conserves_ours
#print axioms DARM.RenameProtocol.recover_all_or_nothing
#print axioms DARM.RenameProtocol.recover_idempotent
