/-
  E33b — PRINCIPAL VOUCHING: ATTRIBUTING EXTERNAL INPUTS

  E33's file channel attributes only content a broker write produced, so a
  gate that refuses unattributed reads also refuses every legitimate external
  input (an uploaded file, a fetched document). This file adds a second
  producer: the principal vouches for an exact (path, digest) pair in a
  manifest it holds. A read is attributed when the broker's attestation names
  the content read, or when the principal's manifest names the path and the
  digest of the content read, and the verdict says which.

  Proved
    two_source_faithful   in an attestation-faithful history, every attested
                          read of either kind is either written by the broker or
                          vouched for by the principal
    broker_tag_is_written / principal_tag_is_vouched
                          the tag says which producer: attribution keeps its
                          source
    vouch_is_content_exact
                          vouching names the digest, so a vouched file changed
                          afterwards is not an attested read of the new content
                          (the content-matching rule of E33, for vouching)
    agent_manifest_launders
                          if the agent can add manifest entries, foreign content
                          becomes an attested read that no broker write produced
                          and the principal never vouched for: the manifest must
                          be principal-held (as the intents file is)

  NOT claimed: that the manifest is principal-held in a deployment (an
  assumption, like the intents file's); that vouched content is true or safe
  (vouching attributes provenance, not quality).
-/
import E33AttestedChannels

namespace DARM.E33b

open DARM.E33 (Channel Gated FaithfulTo Written)
open DARM.EffectIntegrity2 (World File BrokerOp empty)
open DARM.E27b (Event Foreign evolve)

/-- Who attests a read. -/
inductive Source where
  | broker (rid : Nat)
  | principal
  deriving DecidableEq

/-- The principal's manifest: exact (path, digest) pairs it vouches for. -/
abbrev Manifest := List (String × String)

/-- The two-source file channel. A broker-tagged read is E33's content-matching
    read; a principal-tagged read requires the manifest to name this path and
    the digest of the content read. -/
def twoSource (m : Manifest) : Channel World String Source where
  reads := fun w d t => ∃ x f, w.files x = some f ∧ f.digest = d ∧
    match t with
    | some (.broker r) => f.att = some (r, d)
    | some .principal => (x, d) ∈ m
    | none => True

def Vouched (m : Manifest) (d : String) : Prop := ∃ x, (x, d) ∈ m

theorem two_source_faithful (m : Manifest) (h : List Event)
    (hf : DARM.E29.Faithful DARM.E29.AttFaithfulStep empty h) :
    FaithfulTo (twoSource m) (evolve empty h) (fun d => Written h d ∨ Vouched m d) := by
  rintro d t ⟨x, f, hx, hd, ht⟩
  cases t with
  | broker r =>
    exact Or.inl (DARM.E29.attested_content_has_write_origin h hf x f r d hx ht)
  | principal =>
    exact Or.inr ⟨x, ht⟩

theorem broker_tag_is_written (m : Manifest) (h : List Event)
    (hf : DARM.E29.Faithful DARM.E29.AttFaithfulStep empty h) (d : String) (r : Nat)
    (hr : (twoSource m).reads (evolve empty h) d (some (.broker r))) : Written h d := by
  obtain ⟨x, f, hx, _, ha⟩ := hr
  exact DARM.E29.attested_content_has_write_origin h hf x f r d hx ha

theorem principal_tag_is_vouched (m : Manifest) (w : World) (d : String)
    (hr : (twoSource m).reads w d (some .principal)) : Vouched m d := by
  obtain ⟨x, _, _, _, hm⟩ := hr
  exact ⟨x, hm⟩

/-- A file the principal vouched for, created outside the broker. -/
def uploadHist : List Event := [Event.foreign (Foreign.create "/in" "invoice")]

def principalManifest : Manifest := [("/in", "invoice")]

/-- Non-vacuity: the vouched external file is an attested read. -/
theorem vouched_upload_is_attested :
    Gated (twoSource principalManifest) (evolve empty uploadHist) "invoice" := by
  refine ⟨.principal, "/in", ⟨"invoice", none⟩, ?_, rfl, by simp [principalManifest]⟩
  simp [uploadHist, evolve, DARM.E27b.step, DARM.E27b.applyForeign,
    DARM.EffectIntegrity2.create, empty]

/-- The upload, then changed outside the broker. -/
def uploadTamperHist : List Event :=
  [Event.foreign (Foreign.create "/in" "invoice"), Event.foreign (Foreign.tamper "/in" "evil")]

/-- Vouching is content-exact: after the change, the new content is not an
    attested read (no broker write produced it, and the principal vouched for
    a different digest). -/
theorem vouch_is_content_exact :
    ¬ Gated (twoSource principalManifest) (evolve empty uploadTamperHist) "evil" := by
  rintro ⟨t, hr⟩
  have hf : DARM.E29.Faithful DARM.E29.AttFaithfulStep empty uploadTamperHist := by
    simp [DARM.E29.Faithful, DARM.E29.AttFaithfulStep, uploadTamperHist]
  rcases two_source_faithful principalManifest uploadTamperHist hf "evil" t hr with
    ⟨r0, t0, hm⟩ | ⟨x, hx⟩
  · simp [uploadTamperHist] at hm
  · simp [principalManifest] at hx

/-- Foreign content the agent was induced to fetch. -/
def foreignHist : List Event := [Event.foreign (Foreign.create "/in" "evil")]

/-- If the agent can add manifest entries, the manifest launders: foreign
    content becomes an attested read that no broker write produced and that
    the principal's own manifest does not name. -/
theorem agent_manifest_launders :
    let agentManifest : Manifest := ("/in", "evil") :: principalManifest
    Gated (twoSource agentManifest) (evolve empty foreignHist) "evil" ∧
    ¬ Written foreignHist "evil" ∧ ¬ Vouched principalManifest "evil" := by
  refine ⟨⟨.principal, "/in", ⟨"evil", none⟩, ?_, rfl, by simp⟩, ?_, ?_⟩
  · simp [foreignHist, evolve, DARM.E27b.step, DARM.E27b.applyForeign,
      DARM.EffectIntegrity2.create, empty]
  · rintro ⟨r0, t0, hm⟩; simp [foreignHist] at hm
  · rintro ⟨x, hx⟩; simp [principalManifest] at hx

end DARM.E33b

#print axioms DARM.E33b.two_source_faithful
#print axioms DARM.E33b.broker_tag_is_written
#print axioms DARM.E33b.principal_tag_is_vouched
#print axioms DARM.E33b.vouched_upload_is_attested
#print axioms DARM.E33b.vouch_is_content_exact
#print axioms DARM.E33b.agent_manifest_launders
