/-
  B8 — TYPED EFFECT LOG: WRITES AND DELETES (DARM Guard, delete_file design)

  tests/delete_before.py showed that with B6's write-only log, a legitimate
  deletion is indistinguishable from a foreign one: verify_world reports
  "the log records a write but the file is gone" for both, even when the
  deletion is logged. B8 types the log (write with digest, or delete) and
  verifies each target against its LATEST entry: a write requires the file
  with exactly that content and attestation; a delete requires the file
  absent; no entry requires no attestation.

  Proved: any sequence of broker writes and deletes verifies clean
  (legitimate_ops_never_flagged); a foreign delete or tamper of a file whose
  latest entry is a write is flagged; creating an unlogged, unattested file
  is still not flagged (the R23-D gap, carried over and stated).

  Rename (Part 2): one atomic step over two targets: a delete entry for the
  source and a write entry for the destination under one request, the source
  removed, the destination re-attested. Not modelled: the implementation's
  crash window between moving and re-attesting, and evidence naming two
  targets (B4's prepared record and B5's reconciliation name one).

  Representation: the model's log is newest-first (the real audit log is
  chronological; the model is its reverse). Not re-proved here: truncation
  detection (B6, for write-only logs).
-/

namespace DARM.EffectIntegrity2

inductive Op where
  | write (d : String)
  | del
  deriving DecidableEq

structure Entry where
  rid : Nat
  target : String
  op : Op
  deriving DecidableEq

structure File where
  digest : String
  att : Option (Nat × String)
  deriving DecidableEq

structure World where
  log : List Entry                 -- newest first
  files : String → Option File

def empty : World := { log := [], files := fun _ => none }

def latest : List Entry → String → Option Entry
  | [], _ => none
  | e :: rest, t => if e.target = t then some e else latest rest t

def brokerWrite (w : World) (rid : Nat) (t d : String) : World :=
  { log := ⟨rid, t, Op.write d⟩ :: w.log,
    files := fun x => if x = t then some ⟨d, some (rid, d)⟩ else w.files x }

def brokerDelete (w : World) (rid : Nat) (t : String) : World :=
  { log := ⟨rid, t, Op.del⟩ :: w.log,
    files := fun x => if x = t then none else w.files x }

/-- A rename: the source's delete and the destination's write, one request,
    one step; the moved content is re-attested under the new request. -/
def brokerRename (w : World) (rid : Nat) (src dst d : String) : World :=
  { log := ⟨rid, dst, Op.write d⟩ :: ⟨rid, src, Op.del⟩ :: w.log,
    files := fun x => if x = dst then some ⟨d, some (rid, d)⟩
                      else if x = src then none else w.files x }

/-- What the latest log entry for a target requires of the file. -/
def expected (log : List Entry) (t : String) (actual : Option File) : Prop :=
  match latest log t with
  | some ⟨r, _, Op.write d⟩ => actual = some ⟨d, some (r, d)⟩
  | some ⟨_, _, Op.del⟩ => actual = none
  | none => ∀ f, actual = some f → f.att = none

def Consistent (w : World) : Prop := ∀ t, expected w.log t (w.files t)

/-- Verification of one target against its latest entry. -/
def flagged (w : World) (t : String) : Bool :=
  match latest w.log t with
  | some ⟨r, _, Op.write d⟩ => w.files t != some ⟨d, some (r, d)⟩
  | some ⟨_, _, Op.del⟩ => (w.files t).isSome
  | none =>
    match w.files t with
    | some f => f.att.isSome
    | none => false

theorem empty_consistent : Consistent empty := by
  intro t f hf
  simp [empty] at hf

theorem write_preserves (w : World) (rid : Nat) (t d : String) (h : Consistent w) :
    Consistent (brokerWrite w rid t d) := by
  intro x
  by_cases hx : x = t
  · subst hx
    simp [expected, brokerWrite, latest]
  · have hne : ¬ t = x := fun e => hx e.symm
    have h1 : latest (brokerWrite w rid t d).log x = latest w.log x := by
      simp [brokerWrite, latest, hne]
    have h2 : (brokerWrite w rid t d).files x = w.files x := by
      simp [brokerWrite, hx]
    unfold expected
    rw [h1, h2]
    exact h x

theorem delete_preserves (w : World) (rid : Nat) (t : String) (h : Consistent w) :
    Consistent (brokerDelete w rid t) := by
  intro x
  by_cases hx : x = t
  · subst hx
    simp [expected, brokerDelete, latest]
  · have hne : ¬ t = x := fun e => hx e.symm
    have h1 : latest (brokerDelete w rid t).log x = latest w.log x := by
      simp [brokerDelete, latest, hne]
    have h2 : (brokerDelete w rid t).files x = w.files x := by
      simp [brokerDelete, hx]
    unfold expected
    rw [h1, h2]
    exact h x

theorem rename_preserves (w : World) (rid : Nat) (src dst d : String) (h : Consistent w) :
    Consistent (brokerRename w rid src dst d) := by
  intro x
  by_cases hd : x = dst
  · subst hd
    simp [expected, brokerRename, latest]
  · by_cases hs : x = src
    · subst hs
      have hne : ¬ dst = x := fun e => hd e.symm
      simp [expected, brokerRename, latest, hne, hd]
    · have hne1 : ¬ dst = x := fun e => hd e.symm
      have hne2 : ¬ src = x := fun e => hs e.symm
      have h1 : latest (brokerRename w rid src dst d).log x = latest w.log x := by
        simp [brokerRename, latest, hne1, hne2]
      have h2 : (brokerRename w rid src dst d).files x = w.files x := by
        simp [brokerRename, hd, hs]
      unfold expected
      rw [h1, h2]
      exact h x

inductive BrokerOp where
  | wr (rid : Nat) (t d : String)
  | dl (rid : Nat) (t : String)
  | mv (rid : Nat) (src dst d : String)

def apply (w : World) : BrokerOp → World
  | BrokerOp.wr r t d => brokerWrite w r t d
  | BrokerOp.dl r t => brokerDelete w r t
  | BrokerOp.mv r s t d => brokerRename w r s t d

def run (w : World) : List BrokerOp → World
  | [] => w
  | op :: ops => run (apply w op) ops

theorem run_consistent (w : World) (ops : List BrokerOp) (h : Consistent w) :
    Consistent (run w ops) := by
  induction ops generalizing w with
  | nil => exact h
  | cons op ops ih =>
    apply ih
    cases op with
    | wr r t d => exact write_preserves w r t d h
    | dl r t => exact delete_preserves w r t h
    | mv r s t d => exact rename_preserves w r s t d h

theorem nothing_flagged (w : World) (h : Consistent w) (t : String) : flagged w t = false := by
  have ht := h t
  unfold expected at ht
  unfold flagged
  cases hl : latest w.log t with
  | none =>
    rw [hl] at ht
    cases hf : w.files t with
    | none => rfl
    | some f => simp [ht f hf]
  | some e =>
    rw [hl] at ht
    obtain ⟨r, t', op⟩ := e
    cases op with
    | write d => simp [ht]
    | del => simp [ht]

/-- No false positives: any sequence of broker writes and deletes verifies clean. -/
theorem legitimate_ops_never_flagged (ops : List BrokerOp) (t : String) :
    flagged (run empty ops) t = false :=
  nothing_flagged _ (run_consistent empty ops empty_consistent) t

/-! ## Foreign operations -/

def foreignDelete (w : World) (t : String) : World :=
  { w with files := fun x => if x = t then none else w.files x }

def tamper (w : World) (t d' : String) : World :=
  { w with files := fun x => if x = t then (w.files t).map (fun f => { f with digest := d' })
                             else w.files x }

def create (w : World) (t d : String) : World :=
  { w with files := fun x => if x = t then some ⟨d, none⟩ else w.files x }

theorem foreign_delete_detected (w : World) (t : String) (r : Nat) (d : String)
    (hl : latest w.log t = some ⟨r, t, Op.write d⟩) :
    flagged (foreignDelete w t) t = true := by
  simp [flagged, foreignDelete, hl]

theorem foreign_tamper_detected (w : World) (t : String) (r : Nat) (d d' : String)
    (h : Consistent w) (hl : latest w.log t = some ⟨r, t, Op.write d⟩) (hne : d' ≠ d) :
    flagged (tamper w t d') t = true := by
  have hf : w.files t = some ⟨d, some (r, d)⟩ := by
    have ht := h t
    unfold expected at ht
    rw [hl] at ht
    exact ht
  simp [flagged, tamper, hl, hf, hne]

def foreignMove (w : World) (src dst : String) : World :=
  { w with files := fun x => if x = dst then w.files src else if x = src then none else w.files x }

/-- A move outside the broker is flagged at both paths: the source no longer
    holds its logged write, and the destination holds an attested file that
    the log never placed there. -/
theorem foreign_move_detected (w : World) (src dst : String) (r : Nat) (d : String)
    (h : Consistent w) (hne : src ≠ dst)
    (hl : latest w.log src = some ⟨r, src, Op.write d⟩) (hd : latest w.log dst = none) :
    flagged (foreignMove w src dst) src = true ∧ flagged (foreignMove w src dst) dst = true := by
  have hf : w.files src = some ⟨d, some (r, d)⟩ := by
    have ht := h src
    unfold expected at ht
    rw [hl] at ht
    exact ht
  constructor
  · simp [flagged, foreignMove, hl, hne]
  · simp [flagged, foreignMove, hd, hf]

/-- The R23-D gap, carried over: an unlogged, unattested creation is not flagged. -/
theorem foreign_creation_undetected (w : World) (t d : String) (hl : latest w.log t = none) :
    flagged (create w t d) t = false := by
  simp [flagged, create, hl]

end DARM.EffectIntegrity2

#print axioms DARM.EffectIntegrity2.legitimate_ops_never_flagged
#print axioms DARM.EffectIntegrity2.foreign_delete_detected
#print axioms DARM.EffectIntegrity2.foreign_tamper_detected
#print axioms DARM.EffectIntegrity2.foreign_creation_undetected
#print axioms DARM.EffectIntegrity2.rename_preserves
#print axioms DARM.EffectIntegrity2.foreign_move_detected
