/-
  B8 TRACE CHECK: replay a trace exported from the running broker through
  B8's own `apply`, comparing the typed log and the governed files after
  every step. A step with no operation (a read, a rejection, a duplicate)
  must leave the state unchanged. Used with `decide`, so the kernel itself
  evaluates B8's definitions against the observed trace, and the Python
  transcription of the model is no longer trusted for that trace. What
  remains trusted is the projection: how the audit log and files become a
  Snapshot.
-/
import B8TypedEffectLog

namespace DARM.TraceCheck
open DARM.EffectIntegrity2

/-- What the running broker was observed to be after a step: its typed log
    (newest first, as in B8) and the governed files. -/
structure Snapshot where
  log : List Entry
  files : List (String × Option File)

def agrees (w : World) (s : Snapshot) : Bool :=
  decide (w.log = s.log) && s.files.all (fun p => decide (w.files p.1 = p.2))

/-- Replay through B8's `apply`, comparing every step. -/
def checkTrace : World → List (Option BrokerOp × Snapshot) → Bool
  | _, [] => true
  | w, (op, s) :: rest =>
    let w' := match op with
      | some o => DARM.EffectIntegrity2.apply w o
      | none => w
    agrees w' s && checkTrace w' rest

/-! Sanity: the checker accepts a correct trace and rejects a wrong one. -/

def goodTrace : List (Option BrokerOp × Snapshot) :=
  [ (some (BrokerOp.wr 1 "a" "d0"),
      ⟨[⟨1, "a", Op.write "d0"⟩], [("a", some ⟨"d0", some (1, "d0")⟩)]⟩),
    (none,
      ⟨[⟨1, "a", Op.write "d0"⟩], [("a", some ⟨"d0", some (1, "d0")⟩)]⟩),
    (some (BrokerOp.dl 2 "a"),
      ⟨[⟨2, "a", Op.del⟩, ⟨1, "a", Op.write "d0"⟩], [("a", none)]⟩) ]

/-- Wrong on purpose: after the delete, the file is claimed to still exist. -/
def badTrace : List (Option BrokerOp × Snapshot) :=
  [ (some (BrokerOp.wr 1 "a" "d0"),
      ⟨[⟨1, "a", Op.write "d0"⟩], [("a", some ⟨"d0", some (1, "d0")⟩)]⟩),
    (some (BrokerOp.dl 2 "a"),
      ⟨[⟨2, "a", Op.del⟩, ⟨1, "a", Op.write "d0"⟩], [("a", some ⟨"d0", some (1, "d0")⟩)]⟩) ]

theorem good_trace_accepted : checkTrace DARM.EffectIntegrity2.empty goodTrace = true := by decide
theorem bad_trace_rejected : checkTrace DARM.EffectIntegrity2.empty badTrace = false := by decide

/-! ## With recorded before-states: B6/B9's precondition, composed with B8

Each step also carries the pre-state the broker recorded for the paths it
touched (a content digest, or none for absent). The checker verifies that
the replayed world held exactly that state before applying the operation,
and that the operation produced the observed state. This composes the
broker's recorded precondition with B8's transition semantics inside one
kernel check. It does not show the broker obtained or enforced that
pre-state atomically on the filesystem: that remains B6/B9 plus the
implementation evidence. -/

abbrev Before := List (String × Option String)

def beforeMatches (w : World) (bs : Before) : Bool :=
  bs.all (fun p => decide ((w.files p.1).map File.digest = p.2))

def checkTraceB : World → List (Option BrokerOp × Before × Snapshot) → Bool
  | _, [] => true
  | w, (op, bs, s) :: rest =>
    let w' := match op with
      | some o => DARM.EffectIntegrity2.apply w o
      | none => w
    beforeMatches w bs && agrees w' s && checkTraceB w' rest

def goodTraceB : List (Option BrokerOp × Before × Snapshot) :=
  [ (some (BrokerOp.wr 1 "a" "d0"), [("a", none)],
      ⟨[⟨1, "a", Op.write "d0"⟩], [("a", some ⟨"d0", some (1, "d0")⟩)]⟩),
    (some (BrokerOp.wr 2 "a" "d1"), [("a", some "d0")],
      ⟨[⟨2, "a", Op.write "d1"⟩, ⟨1, "a", Op.write "d0"⟩], [("a", some ⟨"d1", some (2, "d1")⟩)]⟩) ]

/-- One recorded before-state wrong (d9 instead of d0); every after-state unchanged. -/
def badBeforeTraceB : List (Option BrokerOp × Before × Snapshot) :=
  [ (some (BrokerOp.wr 1 "a" "d0"), [("a", none)],
      ⟨[⟨1, "a", Op.write "d0"⟩], [("a", some ⟨"d0", some (1, "d0")⟩)]⟩),
    (some (BrokerOp.wr 2 "a" "d1"), [("a", some "d9")],
      ⟨[⟨2, "a", Op.write "d1"⟩, ⟨1, "a", Op.write "d0"⟩], [("a", some ⟨"d1", some (2, "d1")⟩)]⟩) ]

theorem good_before_accepted :
    checkTraceB DARM.EffectIntegrity2.empty goodTraceB = true := by decide
theorem bad_before_rejected :
    checkTraceB DARM.EffectIntegrity2.empty badBeforeTraceB = false := by decide
/-- Without before-states, the same wrong trace passes: the new check is not redundant. -/
theorem after_only_checker_blind :
    checkTrace DARM.EffectIntegrity2.empty (badBeforeTraceB.map (fun x => (x.1, x.2.2))) = true := by
  decide

end DARM.TraceCheck

#print axioms DARM.TraceCheck.good_trace_accepted
#print axioms DARM.TraceCheck.bad_trace_rejected
#print axioms DARM.TraceCheck.good_before_accepted
#print axioms DARM.TraceCheck.bad_before_rejected
#print axioms DARM.TraceCheck.after_only_checker_blind
