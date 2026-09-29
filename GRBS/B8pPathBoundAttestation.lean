/-
  B8p — PATH-BOUND ATTESTATION

  B8's attestation is (request, digest). The runtime signs (request, target,
  digest) and rejects an attestation whose target is not the file's location.
  This module models the attestation as the runtime signs it, beside B8 (which
  stays unchanged and is shown to be this model with the path forgotten).

  Proved: in any history from the empty world, every attestation present was
  minted by a broker operation in that history with exactly that request,
  target and digest (evolve_inv), since foreign actions can move, copy or keep
  attestations but never mint them, the model's form of unforgeability. Hence
  a file at t whose attestation names t was placed there by a broker write or
  rename under that request, with no appeal to the log
  (attested_at_location_was_placed): a second route to E27's execution
  identity.

  The two mechanisms are complementary, not redundant. Move witness: after a
  foreign move, the attestation names the old path, so the path check rejects
  it without the log (moved_file_names_its_origin). Replay witness: a file
  copied away, deleted by the broker, and copied back carries an attestation
  that names its location and was really minted, so the attestation accepts
  it; the log's latest entry for that path is the delete, so the log catches
  it (replay_accepted_by_attestation_caught_by_log). The attestation binds
  origin and location; the log binds freshness and order.

  Refinement: forgetting the path commutes with writes and creations
  (proj_write, proj_create), so B8 is this model's abstraction.

  NOT claimed: cryptographic unforgeability itself (modeled as: foreign actions
  never mint an attestation); that the file's content still matches the
  attested digest (tampering keeps the attestation and changes the content,
  which the digest comparison catches, as in B8).
-/
import B8TypedEffectLog

namespace DARM.B8p

open DARM.EffectIntegrity2 (Entry Op BrokerOp World latest brokerWrite)

/-- A file whose attestation names request, target and digest, as the runtime signs it. -/
structure FileP where
  digest : String
  att : Option (Nat × String × String)
  deriving DecidableEq

structure WorldP where
  log : List Entry
  files : String → Option FileP

def emptyP : WorldP := { log := [], files := fun _ => none }

def put (w : WorldP) (t : String) (v : Option FileP) : String → Option FileP :=
  fun x => if x = t then v else w.files x

def writeP (w : WorldP) (rid : Nat) (t d : String) : WorldP :=
  { log := ⟨rid, t, Op.write d⟩ :: w.log, files := put w t (some ⟨d, some (rid, t, d)⟩) }

def deleteP (w : WorldP) (rid : Nat) (t : String) : WorldP :=
  { log := ⟨rid, t, Op.del⟩ :: w.log, files := put w t none }

def renameP (w : WorldP) (rid : Nat) (src dst d : String) : WorldP :=
  { log := ⟨rid, dst, Op.write d⟩ :: ⟨rid, src, Op.del⟩ :: w.log,
    files := fun x => if x = dst then some ⟨d, some (rid, dst, d)⟩
                      else if x = src then none else w.files x }

def applyP (w : WorldP) : BrokerOp → WorldP
  | .wr r t d => writeP w r t d
  | .dl r t => deleteP w r t
  | .mv r s t d => renameP w r s t d

/-- Foreign actions: they may move, copy or keep attestations, never mint them. -/
inductive ForeignP where
  | del (t : String)
  | tamper (t d' : String)
  | create (t d : String)
  | move (s t : String)
  | copy (s t : String)

def applyForeignP (w : WorldP) : ForeignP → WorldP
  | .del t => { w with files := put w t none }
  | .tamper t d' => { w with files := fun x =>
      if x = t then (w.files t).map (fun f => { f with digest := d' }) else w.files x }
  | .create t d => { w with files := put w t (some ⟨d, none⟩) }
  | .move s t => { w with files := fun x =>
      if x = t then w.files s else if x = s then none else w.files x }
  | .copy s t => { w with files := put w t (w.files s) }

inductive EventP where
  | broker (op : BrokerOp)
  | foreign (f : ForeignP)

def stepP (w : WorldP) : EventP → WorldP
  | .broker op => applyP w op
  | .foreign f => applyForeignP w f

def evolveP (w : WorldP) : List EventP → WorldP
  | [] => w
  | e :: es => evolveP (stepP w e) es

/-- The attestation (r, t, d) was minted by a broker operation in the history. -/
def Minted (h : List EventP) (r : Nat) (t d : String) : Prop :=
  ∃ op, EventP.broker op ∈ h ∧ (op = BrokerOp.wr r t d ∨ ∃ s, op = BrokerOp.mv r s t d)

/-- Every attestation present was minted in the history so far. -/
def AttInv (h : List EventP) (w : WorldP) : Prop :=
  ∀ x f r t d, w.files x = some f → f.att = some (r, t, d) → Minted h r t d

theorem minted_mono {done : List EventP} {e : EventP} {r : Nat} {t d : String}
    (hm : Minted done r t d) : Minted (done ++ [e]) r t d := by
  obtain ⟨op, hop, h⟩ := hm
  exact ⟨op, List.mem_append_left _ hop, h⟩

theorem minted_new {done : List EventP} {op : BrokerOp} {r : Nat} {t d : String}
    (h : op = BrokerOp.wr r t d ∨ ∃ s, op = BrokerOp.mv r s t d) :
    Minted (done ++ [EventP.broker op]) r t d :=
  ⟨op, by simp, h⟩

/-- One step preserves the invariant: broker operations mint what they place;
    foreign actions only move, copy, keep or remove attestations. -/
theorem step_inv (done : List EventP) (w : WorldP) (e : EventP) (h : AttInv done w) :
    AttInv (done ++ [e]) (stepP w e) := by
  intro x f r t d hf ha
  cases e with
  | broker op =>
    cases op with
    | wr r0 t0 d0 =>
      simp only [stepP, applyP, writeP, put] at hf
      by_cases hx : x = t0
      · rw [if_pos hx] at hf
        cases hf
        simp at ha
        obtain ⟨rfl, rfl, rfl⟩ := ha
        exact minted_new (Or.inl rfl)
      · rw [if_neg hx] at hf
        exact minted_mono (h x f r t d hf ha)
    | dl r0 t0 =>
      simp only [stepP, applyP, deleteP, put] at hf
      by_cases hx : x = t0
      · rw [if_pos hx] at hf
        cases hf
      · rw [if_neg hx] at hf
        exact minted_mono (h x f r t d hf ha)
    | mv r0 s t0 d0 =>
      simp only [stepP, applyP, renameP] at hf
      by_cases hx : x = t0
      · rw [if_pos hx] at hf
        cases hf
        simp at ha
        obtain ⟨rfl, rfl, rfl⟩ := ha
        exact minted_new (Or.inr ⟨s, rfl⟩)
      · rw [if_neg hx] at hf
        by_cases hs : x = s
        · rw [if_pos hs] at hf
          cases hf
        · rw [if_neg hs] at hf
          exact minted_mono (h x f r t d hf ha)
  | foreign fa =>
    cases fa with
    | del t0 =>
      simp only [stepP, applyForeignP, put] at hf
      by_cases hx : x = t0
      · rw [if_pos hx] at hf
        cases hf
      · rw [if_neg hx] at hf
        exact minted_mono (h x f r t d hf ha)
    | tamper t0 d' =>
      simp only [stepP, applyForeignP] at hf
      by_cases hx : x = t0
      · rw [if_pos hx] at hf
        cases h0 : w.files t0 with
        | none =>
          rw [h0] at hf
          cases hf
        | some f0 =>
          rw [h0] at hf
          simp at hf
          subst hf
          exact minted_mono (h t0 f0 r t d h0 ha)
      · rw [if_neg hx] at hf
        exact minted_mono (h x f r t d hf ha)
    | create t0 d0 =>
      simp only [stepP, applyForeignP, put] at hf
      by_cases hx : x = t0
      · rw [if_pos hx] at hf
        cases hf
        simp at ha
      · rw [if_neg hx] at hf
        exact minted_mono (h x f r t d hf ha)
    | move s0 t0 =>
      simp only [stepP, applyForeignP] at hf
      by_cases hx : x = t0
      · rw [if_pos hx] at hf
        exact minted_mono (h s0 f r t d hf ha)
      · rw [if_neg hx] at hf
        by_cases hs : x = s0
        · rw [if_pos hs] at hf
          cases hf
        · rw [if_neg hs] at hf
          exact minted_mono (h x f r t d hf ha)
    | copy s0 t0 =>
      simp only [stepP, applyForeignP, put] at hf
      by_cases hx : x = t0
      · rw [if_pos hx] at hf
        exact minted_mono (h s0 f r t d hf ha)
      · rw [if_neg hx] at hf
        exact minted_mono (h x f r t d hf ha)

/-- The invariant holds along any history. -/
theorem evolve_inv (es : List EventP) :
    ∀ (done : List EventP) (w : WorldP), AttInv done w → AttInv (done ++ es) (evolveP w es) := by
  induction es with
  | nil =>
    intro done w h
    simpa [evolveP] using h
  | cons e es ih =>
    intro done w h
    have := ih (done ++ [e]) (stepP w e) (step_inv done w e h)
    simpa [evolveP, List.append_assoc] using this

/-- Execution identity from the attestation alone: a file at t whose
    attestation names t was placed there by a broker write or rename under
    that request, in the history. No appeal to the log. -/
theorem attested_at_location_was_placed (h : List EventP) (t : String) (f : FileP)
    (r : Nat) (d : String)
    (hf : (evolveP emptyP h).files t = some f) (ha : f.att = some (r, t, d)) :
    Minted h r t d := by
  have hi := evolve_inv h [] emptyP (by
    intro x f r t d hf
    simp [emptyP] at hf)
  simpa using hi t f r t d hf ha

/-! ## The two mechanisms are complementary -/

/-- After a foreign move, the attestation names the old path: the path check
    rejects it without the log. -/
theorem moved_file_names_its_origin :
    (evolveP emptyP [.broker (.wr 7 "/a" "x"), .foreign (.move "/a" "/b")]).files "/b" =
      some ⟨"x", some (7, "/a", "x")⟩ := by
  simp [evolveP, stepP, applyP, writeP, applyForeignP, put, emptyP]

/-- A replay: written, copied away, deleted by the broker, copied back. The
    attestation names the location and was really minted, so it accepts the
    file; the log's latest entry for the path is the delete, so the log does not. -/
theorem replay_accepted_by_attestation_caught_by_log :
    let w := evolveP emptyP [.broker (.wr 1 "/t" "x"), .foreign (.copy "/t" "/bak"),
                             .broker (.dl 2 "/t"), .foreign (.copy "/bak" "/t")]
    w.files "/t" = some ⟨"x", some (1, "/t", "x")⟩ ∧
    latest w.log "/t" = some ⟨2, "/t", Op.del⟩ := by
  simp [evolveP, stepP, applyP, writeP, deleteP, applyForeignP, put, emptyP, latest]

/-! ## Refinement: B8 is this model with the path forgotten -/

def projF (f : FileP) : DARM.EffectIntegrity2.File :=
  ⟨f.digest, f.att.map (fun a => (a.1, a.2.2))⟩

def projW (w : WorldP) : World :=
  { log := w.log, files := fun x => (w.files x).map projF }

theorem proj_write (w : WorldP) (r : Nat) (t d : String) :
    projW (writeP w r t d) = brokerWrite (projW w) r t d := by
  unfold projW writeP brokerWrite put
  congr 1
  funext x
  by_cases hx : x = t <;> simp [hx, projF]

theorem proj_create (w : WorldP) (t d : String) :
    projW (applyForeignP w (.create t d)) = DARM.EffectIntegrity2.create (projW w) t d := by
  unfold projW applyForeignP DARM.EffectIntegrity2.create put
  congr 1
  funext x
  by_cases hx : x = t <;> simp [hx, projF]

end DARM.B8p

#print axioms DARM.B8p.evolve_inv
#print axioms DARM.B8p.attested_at_location_was_placed
#print axioms DARM.B8p.moved_file_names_its_origin
#print axioms DARM.B8p.replay_accepted_by_attestation_caught_by_log
#print axioms DARM.B8p.proj_write
#print axioms DARM.B8p.proj_create
