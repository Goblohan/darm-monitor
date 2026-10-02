/-
  E33 — ATTESTED CHANNELS: DISCHARGING CHANNEL INTEGRITY BEYOND FILES

  E32c composes attribution across a handoff when the downstream input lies in
  the set the downstream attribution relies on, which it split into a
  guarantee and channel integrity (nothing unmediated changes the value
  between the upstream effect and the downstream read). For a remote service
  that integrity cannot be assumed: E31 shows foreign clients act on the same
  state and the broker cannot observe it.

  The discharge proved here does not assume the channel is untouched. It
  gates the downstream read: the downstream boundary admits only inputs read
  with an attestation, and the channel is faithful when every attested value
  was produced by an attributed upstream effect. Then every input the
  downstream boundary admits lies in the rely set (gated_within), and the
  downstream stage is attributable on whatever the world holds, foreign
  activity included (gated_downstream_sound).

  Necessity: an ungated reader consumes a foreign value (gate_necessary); a
  gate on an unfaithful channel accepts a forged attestation
  (faithfulness_necessary).

  Instances
    Remote (E31): with an echoing service the record channel is faithful
      (from echoed_record_attributed); a foreign record is readable but not
      attested (e31_gate_necessary); and a service that never echoes offers no
      attested read at all (e31_no_echo_no_attested_read): the gate is then
      sound and empty. Attribution downstream of a non-echoing service cannot
      be discharged this way, matching E31's impossibility.
    Files (E29): in an attestation-faithful history, the content-matching
      channel (the attestation names the content read) is faithful (from
      attested_content_has_write_origin). A gate that checks only that an
      attestation is present is not: a foreign tamper keeps the attestation
      and changes the content (presence_gate_defeated_by_tamper). The gate must
      compare what is read with what is attested.

  NOT claimed: that a deployed consumer enforces the gate; that echoed
  identifiers are unforgeable (E31's assumption); channels other than these
  two.
-/
import E32cSequentialComposition
import E29FaithfulRename
import E31RemoteEffects

namespace DARM.E33

/-! ## Channels, attested reads, faithfulness -/

/-- What a reader can observe in state `S`: a value, with an attestation tag
    or without one. -/
structure Channel (S O Tag : Type) where
  reads : S → O → Option Tag → Prop

variable {S O Tag : Type}

/-- An attested read of `o`. -/
def Gated (ch : Channel S O Tag) (s : S) (o : O) : Prop :=
  ∃ t, ch.reads s o (some t)

/-- Faithful: every attested value was produced by an attributed upstream
    effect. -/
def FaithfulTo (ch : Channel S O Tag) (s : S) (Produced : O → Prop) : Prop :=
  ∀ o t, ch.reads s o (some t) → Produced o

theorem gated_within (ch : Channel S O Tag) (s : S) (Produced R : O → Prop)
    (hF : FaithfulTo ch s Produced) (hG : ∀ o, Produced o → R o) :
    ∀ o, Gated ch s o → R o := by
  rintro o ⟨t, ht⟩
  exact hG o (hF o t ht)

/-- The downstream boundary admits only attested inputs. -/
def GateRespected (ch : Channel S O Tag) (s : S) (B : DARM.E32c.Downstream O) : Prop :=
  ∀ o q, B.admits o q → Gated ch s o

/-- Downstream attribution on whatever the world holds: every admitted,
    fitting downstream action is acceptable, and its input traces to an
    attributed upstream effect. -/
theorem gated_downstream_sound (ch : Channel S O Tag) (s : S) (Produced R : O → Prop)
    (B : DARM.E32c.Downstream O) (j : B.I)
    (hF : FaithfulTo ch s Produced) (hG : ∀ o, Produced o → R o)
    (hB : DARM.E32c.RelySound B j R) (hGate : GateRespected ch s B) :
    ∀ o q, B.fits j o q = true → B.admits o q → B.acc j o q ∧ Produced o := by
  intro o q hfit hadm
  obtain ⟨t, ht⟩ := hGate o q hadm
  have hp := hF o t ht
  exact ⟨hB o (hG o hp) q hfit hadm, hp⟩

/-- The upstream link: if the broker executes only fitting, admitted upstream
    proposals, the upstream stage is attributable, and its acceptable effects
    leave outputs in the rely set, then everything produced lies in it. -/
theorem upstream_guarantee (A : DARM.E32b.Domain) (i : A.I) (out : A.P → O)
    (Executed : A.P → Prop) (R : O → Prop)
    (hExec : ∀ p, Executed p → A.fits i p = true ∧ A.admits p)
    (hA : DARM.E32b.Sound A i) (hGuar : ∀ p, A.acc i p → R (out p)) :
    ∀ o, (∃ p, Executed p ∧ out p = o) → R o := by
  rintro o ⟨p, hp, rfl⟩
  obtain ⟨hf, ha⟩ := hExec p hp
  exact hGuar p (hA p hf ha)

/-! ## Necessity -/

/-- `true` is produced and attested; `false` is foreign and unattested. -/
def honest : Channel Unit Bool Nat where
  reads := fun _ o t => (o = true ∧ t = some 0) ∨ (o = false ∧ t = none)

/-- The gate is necessary: the channel is faithful, yet a reader that does not
    require an attestation consumes the foreign value. -/
theorem gate_necessary :
    FaithfulTo honest () (fun o => o = true) ∧
    honest.reads () false none ∧ ¬ (false = true) ∧ ¬ Gated honest () false := by
  refine ⟨?_, Or.inr ⟨rfl, rfl⟩, Bool.noConfusion, ?_⟩
  · intro o t h
    rcases h with ⟨ho, _⟩ | ⟨_, ht⟩
    · exact ho
    · simp at ht
  · rintro ⟨t, h | h⟩
    · exact Bool.noConfusion h.1
    · simp at h

/-- A channel on which the foreign value carries a (forged) attestation. -/
def forged : Channel Unit Bool Nat where
  reads := fun _ _ t => t = some 0

/-- Faithfulness is necessary: the gate admits the forged attestation and the
    value read was never produced. -/
theorem faithfulness_necessary :
    ¬ FaithfulTo forged () (fun o => o = true) ∧ Gated forged () false := by
  refine ⟨?_, ⟨0, rfl⟩⟩
  intro h; exact Bool.noConfusion (h false 0 rfl)

/-! ## Instance: remote records (E31) -/

open DARM.E31 (W Ev Req run W0)

/-- The record channel: a reader sees a record's request content and its tag. -/
def recordChannel : Channel W Req Nat where
  reads := fun w r t => ∃ rec ∈ w.remote, (⟨rec.endpoint, rec.body⟩ : Req) = r ∧ rec.tag = t

/-- Produced remotely: the broker delivered this request, with echo. -/
def DeliveredEcho (h : List Ev) (r : Req) : Prop :=
  ∃ rid seen, Ev.brokerDelivered rid r true seen ∈ h

/-- With an echoing service, the record channel is faithful in any history,
    foreign clients included. -/
theorem e31_faithful (h : List Ev) : FaithfulTo recordChannel (run W0 h) (DeliveredEcho h) := by
  rintro r t ⟨rec, hrec, rfl, htag⟩
  obtain ⟨seen, hm⟩ := DARM.E31.echoed_record_attributed h rec hrec t htag
  exact ⟨t, seen, hm⟩

/-- A foreign record is readable, unattested, and was not produced by the
    broker: the gate is what keeps it out. -/
theorem e31_gate_necessary :
    recordChannel.reads (run W0 DARM.E31.droppedThenForeign) DARM.E31.order none ∧
    ¬ DeliveredEcho DARM.E31.droppedThenForeign DARM.E31.order := by
  constructor
  · refine ⟨⟨DARM.E31.order.endpoint, DARM.E31.order.body, none⟩, ?_, rfl, rfl⟩
    simp [run, DARM.E31.droppedThenForeign, DARM.E31.stepE, W0]
  · rintro ⟨rid, seen, hm⟩
    simp [DARM.E31.droppedThenForeign] at hm

/-- A service that never echoes offers no attested read: the gate stays sound
    but admits nothing. Downstream attribution cannot be discharged by
    attestation there, matching E31's impossibility without echo. -/
theorem e31_no_echo_no_attested_read (h : List Ev)
    (hno : ∀ rid r seen, Ev.brokerDelivered rid r true seen ∉ h) :
    ∀ r, ¬ Gated recordChannel (run W0 h) r := by
  rintro r ⟨t, ht⟩
  obtain ⟨rid, seen, hm⟩ := e31_faithful h r t ht
  exact hno rid r seen hm

/-! ## Instance: files (E29) -/

open DARM.EffectIntegrity2 (World File BrokerOp empty)
open DARM.E27b (Event Foreign evolve)

/-- The content-matching file channel: a read of content `d` is attested by
    request `r` only if the attestation names exactly `d`. -/
def fileChannel : Channel World String Nat where
  reads := fun w d t => ∃ x f, w.files x = some f ∧ f.digest = d ∧
    match t with
    | some r => f.att = some (r, d)
    | none => True

/-- Produced on the file channel: some broker write in the history wrote it. -/
def Written (h : List Event) (d : String) : Prop :=
  ∃ r0 t0, Event.broker (BrokerOp.wr r0 t0 d) ∈ h

theorem file_faithful (h : List Event)
    (hf : DARM.E29.Faithful DARM.E29.AttFaithfulStep empty h) :
    FaithfulTo fileChannel (evolve empty h) (Written h) := by
  rintro d r ⟨x, f, hx, _, ha⟩
  exact DARM.E29.attested_content_has_write_origin h hf x f r d hx ha

/-- A gate that only checks that some attestation is present. -/
def presenceChannel : Channel World String Nat where
  reads := fun w d t => ∃ x f, w.files x = some f ∧ f.digest = d ∧
    match t with
    | some r => ∃ d', f.att = some (r, d')
    | none => True

def tamperHist : List Event :=
  [Event.broker (BrokerOp.wr 1 "/x" "good"), Event.foreign (Foreign.tamper "/x" "evil")]

/-- The presence-only gate is defeated by tampering, in an attestation-faithful
    history: it admits "evil" as attested, and no write produced "evil". -/
theorem presence_gate_defeated_by_tamper :
    DARM.E29.Faithful DARM.E29.AttFaithfulStep empty tamperHist ∧
    Gated presenceChannel (evolve empty tamperHist) "evil" ∧
    ¬ Written tamperHist "evil" := by
  refine ⟨?_, ?_, ?_⟩
  · simp [DARM.E29.Faithful, DARM.E29.AttFaithfulStep, tamperHist]
  · refine ⟨1, "/x", ⟨"evil", some (1, "good")⟩, ?_, rfl, ⟨"good", rfl⟩⟩
    simp [tamperHist, evolve, DARM.E27b.step, DARM.E27b.applyForeign,
      DARM.EffectIntegrity2.apply, DARM.EffectIntegrity2.brokerWrite,
      DARM.EffectIntegrity2.tamper, empty]
  · rintro ⟨r0, t0, hm⟩
    simp [tamperHist] at hm

/-- The content-matching gate refuses the tampered file: "evil" is not an
    attested read, because it is not produced and the channel is faithful. -/
theorem matching_gate_refuses_tamper : ¬ Gated fileChannel (evolve empty tamperHist) "evil" := by
  rintro ⟨r, hr⟩
  have hf : DARM.E29.Faithful DARM.E29.AttFaithfulStep empty tamperHist :=
    presence_gate_defeated_by_tamper.1
  exact presence_gate_defeated_by_tamper.2.2 (file_faithful tamperHist hf "evil" r hr)

end DARM.E33

#print axioms DARM.E33.gated_within
#print axioms DARM.E33.gated_downstream_sound
#print axioms DARM.E33.upstream_guarantee
#print axioms DARM.E33.gate_necessary
#print axioms DARM.E33.faithfulness_necessary
#print axioms DARM.E33.e31_faithful
#print axioms DARM.E33.e31_gate_necessary
#print axioms DARM.E33.e31_no_echo_no_attested_read
#print axioms DARM.E33.file_faithful
#print axioms DARM.E33.presence_gate_defeated_by_tamper
#print axioms DARM.E33.matching_gate_refuses_tamper
