/-
  B9 RECOVERY CHECK: observations of the running broker's startup recovery,
  replayed against B9's own definitions. Each observation is the three slots
  (source, private name, destination) before and after a recovery:
    full         a complete recovery: recover before = after
    interrupted  a recovery that crashed between moving the file back and
                 restoring its attestation: moveBack before = after
  Checked with decide. Trusted: the projection of the real files onto B9's
  slots (whose content is ours, which attestation it carries). B9 cannot
  express foreign content carrying our attestation; the exporter refuses
  such a state, so that property is checked at runtime, not here.
-/
import B9RenameProtocol

namespace DARM.RecoveryCheck
open DARM.RenameProtocol

inductive Obs where
  | full (before after : FS)
  | interrupted (before after : FS)

def checkObs : List Obs → Bool
  | [] => true
  | Obs.full b a :: rest => decide (recover b = a) && checkObs rest
  | Obs.interrupted b a :: rest => decide (moveBack b = a) && checkObs rest

/-! Sanity: a roll-forward accepted; the same recovery observed as a roll-back rejected. -/

def goodObs : List Obs :=
  [ Obs.full (FS.mk none (some (Val.mine Att.new)) none) (FS.mk none none (some (Val.mine Att.new))) ]
def badObs : List Obs :=
  [ Obs.full (FS.mk none (some (Val.mine Att.new)) none) (FS.mk (some (Val.mine Att.old)) none none) ]

theorem good_recovery_accepted : checkObs goodObs = true := by decide
theorem bad_recovery_rejected : checkObs badObs = false := by decide

end DARM.RecoveryCheck

#print axioms DARM.RecoveryCheck.good_recovery_accepted
#print axioms DARM.RecoveryCheck.bad_recovery_rejected
