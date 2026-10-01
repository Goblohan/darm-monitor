/-
  E29 — FAITHFUL RENAMES, AND WHERE ATTESTED CONTENT COMES FROM

  E28a showed that B8's rename can mint content: it places d at the
  destination whatever the source holds. Two conditions on renames:

  content-faithful: the source holds d when it moves (what a compare-and-swap
  on the source's content checks).
  attestation-faithful: the source carries an attestation for d when it moves.

  Content-faithfulness is not enough: content created outside the broker,
  then renamed by it, is re-attested under the rename's request, giving a
  consistent world with an attested file that no write produced
  (rename_launders_foreign_content). Attestation-faithfulness is: in any
  attestation-faithful history from the empty world, every attestation present
  names content that some write in the history produced, through any chain of
  renames (attested_content_has_write_origin). Writes produce what they attest;
  a faithful rename re-attests content whose attestation already has an origin;
  foreign actions move, keep or remove attestations (tamper keeps one while
  changing the content), never create one.

  NOT claimed: which invocation a rename corresponds to (next); that the
  runtime refuses to rename an unattested source (a runtime question, probed
  separately).
-/
import E28aUnderAttack

namespace DARM.E29

open DARM.EffectIntegrity2 (World File Op BrokerOp Consistent expected latest empty
  brokerWrite brokerDelete brokerRename)
open DARM.E27b (Event Foreign evolve step applyForeign)

/-- A rename moves content the source holds. -/
def ContentFaithfulStep (w : World) : Event → Prop
  | .broker (.mv _ s _ d) => ∃ fs, w.files s = some fs ∧ fs.digest = d
  | _ => True

/-- A rename moves content the source carries an attestation for. -/
def AttFaithfulStep (w : World) : Event → Prop
  | .broker (.mv _ s _ d) => ∃ fs r', w.files s = some fs ∧ fs.att = some (r', d)
  | _ => True

/-- Every step of the history satisfies P, in the world where it occurs. -/
def Faithful (P : World → Event → Prop) : World → List Event → Prop
  | _, [] => True
  | w, e :: es => P w e ∧ Faithful P (step w e) es

/-- Every attestation present names content some write in h produced. -/
def Origin (h : List Event) (w : World) : Prop :=
  ∀ x f r d, w.files x = some f → f.att = some (r, d) →
    ∃ r0 t0, Event.broker (BrokerOp.wr r0 t0 d) ∈ h

theorem origin_mono {done : List Event} {e : Event} {d : String}
    (h : ∃ r0 t0, Event.broker (BrokerOp.wr r0 t0 d) ∈ done) :
    ∃ r0 t0, Event.broker (BrokerOp.wr r0 t0 d) ∈ done ++ [e] := by
  obtain ⟨r0, t0, hm⟩ := h
  exact ⟨r0, t0, List.mem_append_left _ hm⟩

/-- One attestation-faithful step preserves origin. -/
theorem step_origin (done : List Event) (w : World) (e : Event)
    (hf : AttFaithfulStep w e) (h : Origin done w) : Origin (done ++ [e]) (step w e) := by
  intro x f r d hx ha
  cases e with
  | broker op =>
    cases op with
    | wr r0 t0 d0 =>
      simp only [step, DARM.EffectIntegrity2.apply, brokerWrite] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        cases hx
        simp at ha
        obtain ⟨rfl, rfl⟩ := ha
        exact ⟨_, t0, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
      · rw [if_neg hxt] at hx
        exact origin_mono (h x f r d hx ha)
    | dl r0 t0 =>
      simp only [step, DARM.EffectIntegrity2.apply, brokerDelete] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        cases hx
      · rw [if_neg hxt] at hx
        exact origin_mono (h x f r d hx ha)
    | mv r0 s t0 d0 =>
      simp only [AttFaithfulStep] at hf
      simp only [step, DARM.EffectIntegrity2.apply, brokerRename] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        cases hx
        simp at ha
        obtain ⟨rfl, rfl⟩ := ha
        obtain ⟨fs, r', hs, hsa⟩ := hf
        exact origin_mono (h s fs r' _ hs hsa)
      · rw [if_neg hxt] at hx
        by_cases hxs : x = s
        · rw [if_pos hxs] at hx
          cases hx
        · rw [if_neg hxs] at hx
          exact origin_mono (h x f r d hx ha)
  | foreign fa =>
    cases fa with
    | del t0 =>
      simp only [step, applyForeign, DARM.EffectIntegrity2.foreignDelete] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        cases hx
      · rw [if_neg hxt] at hx
        exact origin_mono (h x f r d hx ha)
    | tamper t0 d' =>
      simp only [step, applyForeign, DARM.EffectIntegrity2.tamper] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        cases h0 : w.files t0 with
        | none =>
          rw [h0] at hx
          cases hx
        | some f0 =>
          rw [h0] at hx
          simp at hx
          subst hx
          exact origin_mono (h t0 f0 r d h0 ha)
      · rw [if_neg hxt] at hx
        exact origin_mono (h x f r d hx ha)
    | create t0 d0 =>
      simp only [step, applyForeign, DARM.EffectIntegrity2.create] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        cases hx
        simp at ha
      · rw [if_neg hxt] at hx
        exact origin_mono (h x f r d hx ha)
    | move s0 t0 =>
      simp only [step, applyForeign, DARM.EffectIntegrity2.foreignMove] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        exact origin_mono (h s0 f r d hx ha)
      · rw [if_neg hxt] at hx
        by_cases hxs : x = s0
        · rw [if_pos hxs] at hx
          cases hx
        · rw [if_neg hxs] at hx
          exact origin_mono (h x f r d hx ha)

/-- Origin holds along any attestation-faithful history. -/
theorem evolve_origin (es : List Event) :
    ∀ (done : List Event) (w : World), Faithful AttFaithfulStep w es → Origin done w →
      Origin (done ++ es) (evolve w es) := by
  induction es with
  | nil =>
    intro done w _ h
    simpa [evolve] using h
  | cons e es ih =>
    intro done w hfa h
    simp only [Faithful] at hfa
    have := ih (done ++ [e]) (step w e) hfa.2 (step_origin done w e hfa.1 h)
    simpa [evolve, List.append_assoc] using this

/-- Content origin: in an attestation-faithful history from the empty world,
    an attested file's content was produced by a write in the history, through
    any chain of renames. -/
theorem attested_content_has_write_origin (h : List Event)
    (hf : Faithful AttFaithfulStep empty h) (x : String) (f : File) (r : Nat) (d : String)
    (hx : (evolve empty h).files x = some f) (ha : f.att = some (r, d)) :
    ∃ r0 t0, Event.broker (BrokerOp.wr r0 t0 d) ∈ h := by
  have hi := evolve_origin h [] empty hf (by
    intro x f r d hx
    simp [empty] at hx)
  simpa using hi x f r d hx ha

/-- E28a's counterexample is excluded: its source is empty. -/
theorem rename_mints_content_is_unfaithful :
    ¬ Faithful ContentFaithfulStep empty DARM.E28a.renameOnly := by
  simp [Faithful, ContentFaithfulStep, DARM.E28a.renameOnly, empty]

/-- Foreign content, renamed by the broker. -/
def launder : List Event :=
  [Event.foreign (Foreign.create "/s" "evil"), Event.broker (BrokerOp.mv 5 "/s" "/x" "evil")]

/-- Content-faithfulness is not enough: the rename is content-faithful but not
    attestation-faithful, the world is consistent, the file is attested, and no
    write produced its content. -/
theorem rename_launders_foreign_content :
    Faithful ContentFaithfulStep empty launder ∧
    ¬ Faithful AttFaithfulStep empty launder ∧
    Consistent (evolve empty launder) ∧
    (evolve empty launder).files "/x" = some ⟨"evil", some (5, "evil")⟩ ∧
    ∀ r t, Event.broker (BrokerOp.wr r t "evil") ∉ launder := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Faithful, ContentFaithfulStep, launder, step, applyForeign,
      DARM.EffectIntegrity2.create, empty]
  · simp [Faithful, AttFaithfulStep, launder, step, applyForeign,
      DARM.EffectIntegrity2.create, empty]
  · unfold Consistent
    intro t
    by_cases h1 : t = "/x"
    · subst h1
      simp [launder, evolve, step, applyForeign, DARM.EffectIntegrity2.create,
        DARM.EffectIntegrity2.apply, brokerRename, expected, latest, empty]
    · by_cases h2 : t = "/s"
      · subst h2
        simp [launder, evolve, step, applyForeign, DARM.EffectIntegrity2.create,
          DARM.EffectIntegrity2.apply, brokerRename, expected, latest, empty]
      · simp [launder, evolve, step, applyForeign, DARM.EffectIntegrity2.create,
          DARM.EffectIntegrity2.apply, brokerRename, expected, latest, empty,
          h1, h2, Ne.symm h1, Ne.symm h2]
  · simp [launder, evolve, step, applyForeign, DARM.EffectIntegrity2.create,
      DARM.EffectIntegrity2.apply, brokerRename, empty]
  · intro r t h
    simp [launder] at h

end DARM.E29

#print axioms DARM.E29.evolve_origin
#print axioms DARM.E29.attested_content_has_write_origin
#print axioms DARM.E29.rename_mints_content_is_unfaithful
#print axioms DARM.E29.rename_launders_foreign_content
