/-
  E27 — EXECUTION IDENTITY

  E26.6 assumed that the operation corresponding to an authorized invocation is
  the one actually applied (its hypothesis hWorld). This file derives that at
  the level of B8's log, from B8's own definitions.

  In B8, a path consistent with the log holds, if its latest entry is
  write r d, exactly the file with content d attested (r, d); if a delete,
  nothing; if there is no entry, only unattested files. So an attested file at
  a consistent path forces the log's latest entry for it to be the write under
  that request identifier, with that content (attested_identifies_write). With
  E26: if an invocation carries the pinned payload and the pinned file is
  consistently attested with the pinned content, the logged operation
  corresponds to that invocation (logged_write_corresponds). No foreign action
  writes the log (the four *_leaves_log theorems): in the model only the broker
  appends entries, the analogue of attestation unforgeability.

  Witness: B8's attestation is (request, digest), with no path. After a broker
  write at /a and a foreign move to /b, the file at /b carries a valid-looking
  attestation and no log entry, and it is flagged: in B8, identity rests on the
  log (attestation_alone_does_not_bind_location). The runtime binds identity
  twice: it signs (request, target, digest) and verify_world rejects an
  attestation whose target is not the file's location ("attestation forged or
  moved"). B8 models only the log half; refining its attestation to carry the
  path would model the other.

  NOT claimed: that a logged entry was produced by a particular broker
  operation in a particular history (renames log entries of their own; that
  connection is the next step); anything about the runtime beyond what B8
  models; cryptographic unforgeability itself (the model's analogue is that
  foreign actions do not touch the log).
-/
import E26InvocationExecutionCorrespondence

namespace DARM.E27

open DARM.EffectIntegrity2

/-- The log's latest entry for a path names that path. -/
theorem latest_target {log : List Entry} {t : String} {e : Entry}
    (h : latest log t = some e) : e.target = t := by
  induction log with
  | nil => simp [latest] at h
  | cons x rest ih =>
    simp only [latest] at h
    split at h
    · rename_i hx
      simp at h
      rw [← h]
      exact hx
    · exact ih h

/-- Execution identity at the log: an attested file at a path consistent with
    the log forces the latest entry for it to be the write under that request
    identifier, with that content. -/
theorem attested_identifies_write (log : List Entry) (t : String) (f : File)
    (rid : Nat) (d : String)
    (hexp : expected log t (some f)) (hatt : f.att = some (rid, d)) :
    latest log t = some ⟨rid, t, Op.write d⟩ ∧ f.digest = d := by
  unfold expected at hexp
  cases hl : latest log t with
  | none =>
    simp only [hl] at hexp
    have := hexp f rfl
    rw [hatt] at this
    simp at this
  | some e =>
    obtain ⟨r, x, o⟩ := e
    have hx : x = t := latest_target hl
    cases o with
    | write d0 =>
      simp only [hl, Option.some.injEq] at hexp
      subst hexp
      simp at hatt
      obtain ⟨rfl, rfl⟩ := hatt
      subst hx
      exact ⟨rfl, rfl⟩
    | del =>
      simp only [hl] at hexp
      simp at hexp

/-- The same, for any consistent world. -/
theorem consistent_attested_identifies_write (w : World) (hc : Consistent w)
    (t : String) (f : File) (rid : Nat) (d : String)
    (hf : w.files t = some f) (hatt : f.att = some (rid, d)) :
    latest w.log t = some ⟨rid, t, Op.write d⟩ ∧ f.digest = d := by
  have h := hc t
  rw [hf] at h
  exact attested_identifies_write w.log t f rid d h hatt

/-- The bridge to E26, replacing E26.6's assumption at the level of the log:
    if an invocation carries the pinned payload and the pinned file is
    consistently attested with the pinned content, the logged write corresponds
    to that invocation. -/
theorem logged_write_corresponds (w : World) (hc : Consistent w)
    (inv : DARM.Kernel.Invocation)
    (hinv : DARM.E26.invocationWritesExactly "/workspace/reports/q3.md" "Q3 summary" inv)
    (f : File) (rid : Nat)
    (hf : w.files "/workspace/reports/q3.md" = some f)
    (hatt : f.att = some (rid, "Q3 summary")) :
    latest w.log "/workspace/reports/q3.md" =
        some ⟨rid, "/workspace/reports/q3.md", Op.write "Q3 summary"⟩ ∧
      DARM.E26.ExecCorresponds inv (BrokerOp.wr rid "/workspace/reports/q3.md" "Q3 summary") := by
  refine ⟨(consistent_attested_identifies_write w hc _ f rid _ hf hatt).1, ?_⟩
  exact ⟨hinv.1, rid, _, _, DARM.E26.path_arg_of_invocationWritesExactly inv hinv,
    DARM.E26.content_arg_of_invocationWritesExactly inv hinv, rfl⟩

/-! ## No foreign action writes the log -/

theorem foreign_delete_leaves_log (w : World) (t : String) :
    (foreignDelete w t).log = w.log := rfl
theorem tamper_leaves_log (w : World) (t d : String) :
    (tamper w t d).log = w.log := rfl
theorem create_leaves_log (w : World) (t d : String) :
    (create w t d).log = w.log := rfl
theorem foreign_move_leaves_log (w : World) (s t : String) :
    (foreignMove w s t).log = w.log := rfl

/-! ## Witness: B8's attestation does not bind location -/

/-- A broker write at /a, then a foreign move to /b. -/
def movedWorld : World := foreignMove (brokerWrite empty 7 "/a" "x") "/a" "/b"

/-- The file at /b carries a valid-looking attestation (its digest matches),
    yet no log entry names /b, and verification flags it. -/
theorem attestation_alone_does_not_bind_location :
    movedWorld.files "/b" = some ⟨"x", some (7, "x")⟩ ∧
    latest movedWorld.log "/b" = none ∧
    flagged movedWorld "/b" = true := by
  simp [movedWorld, foreignMove, brokerWrite, empty, latest, flagged]

end DARM.E27

#print axioms DARM.E27.latest_target
#print axioms DARM.E27.attested_identifies_write
#print axioms DARM.E27.consistent_attested_identifies_write
#print axioms DARM.E27.logged_write_corresponds
#print axioms DARM.E27.create_leaves_log
#print axioms DARM.E27.attestation_alone_does_not_bind_location
