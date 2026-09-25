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

end DARM.TraceCheck

#print axioms DARM.TraceCheck.good_trace_accepted
#print axioms DARM.TraceCheck.bad_trace_rejected
