/-
  B6 — EFFECT INTEGRITY: COMPARE-AND-SWAP AND ATTESTATION (DARM Guard 0.8)

  Part 1, compare-and-swap (the broker's exchange-inspect-undo write): a
  write succeeds only from the recorded before-state; on conflict the
  foreign state is left intact; a retry cannot double an effect.

  Part 2, attestation (governed files attest the log): in any world built
  only by broker writes, verification finds nothing; a changed attested
  file is flagged; a dropped log entry whose file survives is flagged,
  which no hash chain alone can detect.

  Assumed: only broker writes create attestations. This is how the model
  represents MAC unforgeability; the implementation provides it with
  HMAC under a key the agent cannot read (assumption A2). Not modeled:
  the fallback path without renameat2; filesystems without xattrs; a
  foreign writer that restores the exact recorded state and attestation.
-/

namespace DARM.EffectIntegrity

/-! ## Part 1: compare-and-swap -/

/-- Target content (none = absent). Returns the new state and whether the write applied. -/
def cas (cur expected : Option String) (new : String) : Option String × Bool :=
  if cur = expected then (some new, true) else (cur, false)

/-- A write applies exactly when the target is in the recorded state. -/
theorem cas_applies_iff (cur expected : Option String) (new : String) :
    (cas cur expected new).2 = true ↔ cur = expected := by
  unfold cas
  split <;> simp_all

/-- On conflict, the foreign state is left exactly as it was. -/
theorem cas_conflict_preserves (cur expected : Option String) (new : String)
    (h : cur ≠ expected) : (cas cur expected new).1 = cur := by
  simp [cas, h]

/-- A retry cannot double an effect: applying the same write twice leaves
    the world as applying it once. -/
theorem cas_retry_idempotent (cur expected : Option String) (new : String) :
    (cas (cas cur expected new).1 expected new).1 = (cas cur expected new).1 := by
  by_cases h : cur = expected <;> by_cases h2 : some new = expected <;> simp_all [cas]

/-! ## Part 2: attestation -/

structure File where
  digest : String
  att : Option (Nat × String)   -- (request id, attested digest)

structure World where
  log : List (Nat × String × String)   -- successful writes: (request id, target, digest)
  files : String → Option File

def empty : World := { log := [], files := fun _ => none }

/-- A broker write: logged, and the file gets content and attestation together
    (the atomic exchange publishes both as one event). -/
def brokerWrite (w : World) (rid : Nat) (t d : String) : World :=
  { log := w.log ++ [(rid, t, d)],
    files := fun x => if x = t then some { digest := d, att := some (rid, d) } else w.files x }

/-- Every attested file's content matches its attestation, and its request is logged. -/
def Honest (w : World) : Prop :=
  ∀ t f, w.files t = some f → ∀ r d, f.att = some (r, d) → f.digest = d ∧ (r, t, d) ∈ w.log

theorem empty_honest : Honest empty := by
  intro t f hf
  simp [empty] at hf

theorem write_preserves (w : World) (rid : Nat) (t d : String) (h : Honest w) :
    Honest (brokerWrite w rid t d) := by
  intro x f hx r dd ha
  by_cases hxt : x = t
  · subst hxt
    simp [brokerWrite] at hx
    subst hx
    simp at ha
    obtain ⟨rfl, rfl⟩ := ha
    exact ⟨rfl, by simp [brokerWrite]⟩
  · simp [brokerWrite, hxt] at hx
    obtain ⟨h1, h2⟩ := h x f hx r dd ha
    exact ⟨h1, List.mem_append.mpr (Or.inl h2)⟩

/-- Any sequence of broker writes from an empty world is Honest. -/
def writes : World → List (Nat × String × String) → World
  | w, [] => w
  | w, (rid, t, d) :: rest => writes (brokerWrite w rid t d) rest

theorem writes_honest (w : World) (ops : List (Nat × String × String)) (h : Honest w) :
    Honest (writes w ops) := by
  induction ops generalizing w with
  | nil => exact h
  | cons op rest ih =>
    rcases op with ⟨rid, t, d⟩
    exact ih _ (write_preserves w rid t d h)

/-- Verification of one target: content must match its attestation, and the
    attested request must be in the log. Unattested files are not governed. -/
def flagged (w : World) (t : String) : Bool :=
  match w.files t with
  | none => false
  | some f =>
    match f.att with
    | none => false
    | some (r, d) => f.digest != d || !decide ((r, t, d) ∈ w.log)

/-- No false alarms: in an Honest world, nothing is flagged. -/
theorem honest_nothing_flagged (w : World) (h : Honest w) (t : String) : flagged w t = false := by
  cases hf : w.files t with
  | none => simp [flagged, hf]
  | some f =>
    cases ha : f.att with
    | none => simp [flagged, hf, ha]
    | some p =>
      obtain ⟨r, d⟩ := p
      obtain ⟨h1, h2⟩ := h t f hf r d ha
      simp [flagged, hf, ha, h1, h2]

/-- An adversary outside the broker changes a file's content; its attestation stays. -/
def tamper (w : World) (t d' : String) : World :=
  { w with files := fun x => if x = t then (w.files t).map (fun f => { f with digest := d' })
                             else w.files x }

/-- Tampering with an attested file is caught. -/
theorem tamper_detected (w : World) (t : String) (f : File) (r : Nat) (d d' : String)
    (hf : w.files t = some f) (ha : f.att = some (r, d)) (hne : d' ≠ d) :
    flagged (tamper w t d') t = true := by
  simp [flagged, tamper, hf, ha, hne]

/-- Dropping the log entry of a write whose attested file survives is caught,
    even though a hash chain over the remaining entries stays valid. -/
theorem truncation_detected (w : World) (log' : List (Nat × String × String)) (t : String)
    (f : File) (r : Nat) (d : String) (hw : Honest w)
    (hf : w.files t = some f) (ha : f.att = some (r, d)) (hgone : (r, t, d) ∉ log') :
    flagged { w with log := log' } t = true := by
  have hd := (hw t f hf r d ha).1
  simp [flagged, hf, ha, hd, hgone]

end DARM.EffectIntegrity

#print axioms DARM.EffectIntegrity.cas_retry_idempotent
#print axioms DARM.EffectIntegrity.cas_conflict_preserves
#print axioms DARM.EffectIntegrity.writes_honest
#print axioms DARM.EffectIntegrity.honest_nothing_flagged
#print axioms DARM.EffectIntegrity.tamper_detected
#print axioms DARM.EffectIntegrity.truncation_detected
