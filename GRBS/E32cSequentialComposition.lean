/-
  E32c — SEQUENTIAL COMPOSITION OF ATTRIBUTION (extends E32, E32b)

  E32b composes attribution along chains of transformations and across
  domains acting jointly. Here one domain's effect becomes another domain's
  input: a file written under an intent is later executed by CI, a fetched
  value is later sent. The downstream boundary decides in the context of the
  input it reads.

  Setting. An upstream domain A (E32b.Domain) with an output map `out` (what
  an executed A-proposal leaves in the world); a downstream domain B whose
  fit, admission and acceptance are indexed by its input; a channel `chan`
  (what B actually reads, given what A left: identity unless something
  unmediated intervenes); and the principal's acceptance of the pipeline.

  Results
    seq_sound                attribution composes across the handoff when
                             (1) A is attributable, (2) A's acceptable outputs,
                             read through the channel, lie inside the set of
                             inputs B's attribution relies on, (3) B is
                             attributable on that set, (4) acceptance is
                             sequentially separable
    seq_sound_of_integrity   (2) splits into guarantee-within-rely and channel
                             integrity (the channel preserves the rely set)
    rely_necessary           A attributable, channel intact, B attributable on
                             its rely set, separable: A's acceptance admits an
                             output outside B's rely set, and the pipeline is
                             not attributable
    channel_necessary        everything holds except the channel: an
                             unmediated change between A's effect and B's read
                             breaks attribution
    seqSeparability_necessary  everything holds except separability
  Instance on B3 writes, with a downstream executor that runs the file:
    pinned_pipeline_sound    pinned intent + intact channel: whatever the
                             executor runs is the principal's vetted summary
    p13_propagates           path-only intent: the attacker's admitted write is
                             executed downstream; the pipeline is not
                             attributable, though each stage's boundary
                             behaved as specified
    tamper_breaks_pipeline   pinned intent, but an unmediated rewrite of the
                             file between write and execution: not
                             attributable. Channel integrity for the file
                             channel is what E29/E30's attestation-faithfulness
                             establishes at runtime (Darm-Guard >= 0.19.0).

  NOT claimed: that any deployed downstream consumer (CI, a mailer) is
  modelled by `executor`; that `chan` is the identity in a deployment — that
  is the channel-integrity premise, discharged per channel (for files, by
  E29/E30 attestation; for other channels, open).
-/
import E32bAttributionComposition

namespace DARM.E32c

open DARM.E32b (Domain Sound)

/-- A downstream domain whose decisions are indexed by the input it reads. -/
structure Downstream (O : Type) where
  P : Type
  I : Type
  fits : I → O → P → Bool
  admits : O → P → Prop
  acc : I → O → P → Prop

/-- Downstream attribution, relying on its input lying in `R`. -/
def RelySound {O : Type} (B : Downstream O) (j : B.I) (R : O → Prop) : Prop :=
  ∀ o, R o → ∀ q, B.fits j o q = true → B.admits o q → B.acc j o q

/-- Pipeline attribution: every admitted, fitting upstream proposal followed by
    every admitted, fitting downstream proposal on what it reads is accepted. -/
def SeqSound {O : Type} (A : Domain) (B : Downstream O) (out : A.P → O) (chan : O → O)
    (accSeq : A.P → B.P → Prop) (i : A.I) (j : B.I) : Prop :=
  ∀ p q, A.fits i p = true → A.admits p →
    B.fits j (chan (out p)) q = true → B.admits (chan (out p)) q → accSeq p q

/-- Sequential separability: an acceptable upstream effect followed by an
    acceptable downstream effect on what it read is acceptable as a pipeline. -/
def SeqSeparable {O : Type} (A : Domain) (B : Downstream O) (out : A.P → O) (chan : O → O)
    (accSeq : A.P → B.P → Prop) (i : A.I) (j : B.I) : Prop :=
  ∀ p q, A.acc i p → B.acc j (chan (out p)) q → accSeq p q

theorem seq_sound {O : Type} (A : Domain) (B : Downstream O) (out : A.P → O) (chan : O → O)
    (accSeq : A.P → B.P → Prop) (i : A.I) (j : B.I) (R : O → Prop)
    (hA : Sound A i)
    (hG : ∀ p, A.acc i p → R (chan (out p)))
    (hB : RelySound B j R)
    (hS : SeqSeparable A B out chan accSeq i j) :
    SeqSound A B out chan accSeq i j := by
  intro p q hfa hadA hfb hadB
  have haccA := hA p hfa hadA
  exact hS p q haccA (hB _ (hG p haccA) q hfb hadB)

/-- Channel integrity: the channel preserves the downstream rely set. -/
def ChannelIntegrity {O : Type} (chan : O → O) (R : O → Prop) : Prop :=
  ∀ o, R o → R (chan o)

theorem seq_sound_of_integrity {O : Type} (A : Domain) (B : Downstream O) (out : A.P → O)
    (chan : O → O) (accSeq : A.P → B.P → Prop) (i : A.I) (j : B.I) (R : O → Prop)
    (hA : Sound A i)
    (hGuar : ∀ p, A.acc i p → R (out p))
    (hChan : ChannelIntegrity chan R)
    (hB : RelySound B j R)
    (hS : SeqSeparable A B out chan accSeq i j) :
    SeqSound A B out chan accSeq i j :=
  seq_sound A B out chan accSeq i j R hA (fun p h => hChan _ (hGuar p h)) hB hS

/-! ## Necessity -/

/-- Upstream: one proposal, admitted, acceptable, leaving output `o`. -/
def upAny : Domain where
  P := Bool
  I := Unit
  fits := fun _ _ => true
  admits := fun _ => True
  acc := fun _ _ => True

/-- Downstream that runs whatever it reads, accepted only on `true`. -/
def runner : Downstream Bool where
  P := Unit
  I := Unit
  fits := fun _ _ _ => true
  admits := fun _ _ => True
  acc := fun _ o _ => o = true

def pipelineAcc : Bool → Unit → Prop := fun p _ => p = true

theorem runner_relySound : RelySound runner () (fun o => o = true) := by
  intro o ho _ _ _; exact ho

/-- Rely set necessary: A accepts writing `false`, which the runner's
    attribution never covered. -/
theorem rely_necessary :
    Sound upAny () ∧ ChannelIntegrity id (fun o : Bool => o = true) ∧
    RelySound runner () (fun o => o = true) ∧
    SeqSeparable upAny runner id id (fun p _ => p = true) () () ∧
    ¬ (∀ p, upAny.acc () p → (fun o : Bool => o = true) (id p)) ∧
    ¬ SeqSound upAny runner id id (fun p _ => p = true) () () := by
  refine ⟨fun _ _ _ => trivial, fun _ h => h, runner_relySound, ?_, ?_, ?_⟩
  · intro p _ _ h; exact h
  · intro h; exact Bool.noConfusion (h false trivial)
  · intro h; exact Bool.noConfusion (h false () rfl trivial rfl trivial)

/-- Upstream that only ever leaves `true`. -/
def upTrue : Domain where
  P := Unit
  I := Unit
  fits := fun _ _ => true
  admits := fun _ => True
  acc := fun _ _ => True

/-- Pipeline acceptance that depends on what the runner actually read. -/
def readTrue (chan : Bool → Bool) : Unit → Unit → Prop := fun _ _ => chan true = true

/-- Channel necessary, as a contrast: the same upstream, downstream, rely set
    and pipeline acceptance. With the channel intact the pipeline is
    attributable; with an unmediated flip between write and read it is not,
    and only the channel differs. -/
theorem channel_necessary :
    SeqSound upTrue runner (fun _ => true) id (readTrue id) () () ∧
    ChannelIntegrity id (fun o : Bool => o = true) ∧
    ¬ ChannelIntegrity (fun _ => false) (fun o : Bool => o = true) ∧
    ¬ SeqSound upTrue runner (fun _ => true) (fun _ => false) (readTrue (fun _ => false)) () () := by
  refine ⟨?_, fun _ h => h, ?_, ?_⟩
  · exact seq_sound_of_integrity upTrue runner (fun _ => true) id (readTrue id) () ()
      (fun o => o = true) (fun _ _ _ => trivial) (fun _ _ => rfl) (fun _ h => h)
      runner_relySound (fun _ _ _ _ => rfl)
  · intro h; exact Bool.noConfusion (h true rfl)
  · intro h; exact Bool.noConfusion (h () () rfl trivial rfl trivial)

/-- Sequential separability necessary: both stages attributable, the input
    inside the rely set, the channel intact, and still the pipeline is not
    accepted (each step is fine; the sequence is not). -/
theorem seqSeparability_necessary :
    Sound upTrue () ∧ RelySound runner () (fun o => o = true) ∧
    ChannelIntegrity id (fun o : Bool => o = true) ∧
    ¬ SeqSeparable upTrue runner (fun _ => true) id (fun _ _ => False) () () ∧
    ¬ SeqSound upTrue runner (fun _ => true) id (fun _ _ => False) () () := by
  refine ⟨fun _ _ _ => trivial, runner_relySound, fun _ h => h, ?_, ?_⟩
  · intro h; exact h () () trivial rfl
  · intro h; exact h () () rfl trivial rfl trivial

/-! ## Instance: write a file under B3, then a downstream executor runs it -/

open DARM.Broker (Proposal)

/-- What a write leaves in the world: the content it carries. -/
def written (p : Proposal) : String := (p.args.lookup "content").getD ""

/-- A downstream executor (CI, a scheduler) that runs whatever the file holds.
    Its boundary admits every run; the principal accepts running only the
    vetted summary. -/
def executor : Downstream String where
  P := Unit
  I := Unit
  fits := fun _ _ _ => true
  admits := fun _ _ => True
  acc := fun _ o _ => o = "Q3 summary"

def vetted : String → Prop := fun o => o = "Q3 summary"

theorem executor_relySound : RelySound executor () vetted := by
  intro o ho _ _ _; exact ho

def pinnedDomain : Domain :=
  DARM.E32b.writeDomain (fun _ => DARM.E24d.WritesExactly "/workspace/reports/q3.md" "Q3 summary")

/-- If every `k`-argument carries `v` and one exists, lookup returns `v`. -/
theorem lookup_of_all (l : List (String × String)) (k v : String)
    (hall : ∀ a ∈ l, a.1 = k → a.2 = v) (hex : ∃ a ∈ l, a.1 = k) :
    l.lookup k = some v := by
  induction l with
  | nil => obtain ⟨_, ha, _⟩ := hex; simp at ha
  | cons a l ih =>
    by_cases hk : a.1 = k
    · have hv := hall a (by simp) hk
      obtain ⟨a1, a2⟩ := a
      simp only at hk hv
      subst hk; subst hv
      simp [List.lookup]
    · obtain ⟨a1, a2⟩ := a
      simp only at hk
      have hne : (k == a1) = false := by
        simp only [beq_eq_false_iff_ne]; exact fun h => hk h.symm
      simp only [List.lookup, hne]
      apply ih
      · intro b hb hbk; exact hall b (by simp [hb]) hbk
      · obtain ⟨b, hb, hbk⟩ := hex
        rcases List.mem_cons.mp hb with h | h
        · subst h; exact absurd hbk hk
        · exact ⟨b, h, hbk⟩

/-- The pinned write guarantees the vetted content is what it leaves. -/
theorem pinned_guarantee (p : Proposal)
    (h : DARM.E24d.WritesExactly "/workspace/reports/q3.md" "Q3 summary" p) :
    vetted (written p) := by
  obtain ⟨_, hall, _, hex⟩ := h
  have hl : p.args.lookup "content" = some "Q3 summary" := by
    apply lookup_of_all
    · intro a ha hk
      rcases hall a ha with h1 | h1
      · rw [h1.1] at hk; exact absurd hk (by decide)
      · exact h1.2
    · exact hex
  simp [vetted, written, hl]

/-- Pipeline acceptance: the principal accepts the pipeline when the run
    executed the vetted summary. -/
def pipelineVetted (chan : String → String) : Proposal → Unit → Prop :=
  fun p _ => chan (written p) = "Q3 summary"

theorem pinned_pipeline_sound :
    SeqSound pinnedDomain executor written id (pipelineVetted id)
      DARM.E24d.pinnedReport () :=
  seq_sound_of_integrity pinnedDomain executor written id (pipelineVetted id)
    DARM.E24d.pinnedReport () vetted
    DARM.E32b.pinned_sound_invariant_under_reordering
    (fun p h => pinned_guarantee p h)
    (fun _ h => h)
    executor_relySound
    (fun _ _ _ h => h)

def pathOnlyDomain : Domain :=
  DARM.E32b.writeDomain (fun _ => DARM.E24d.WritesExactly "/workspace/reports/q3.md" "Q3 summary")

/-- P13 propagates: under the path-only intent, the attacker's admitted write is
    executed downstream and the pipeline is not attributable — although the
    write boundary and the executor's boundary each behaved as specified. -/
theorem p13_propagates :
    ¬ SeqSound pathOnlyDomain executor written id (pipelineVetted id)
        DARM.E24b.forThisReport () := by
  intro h
  have := h DARM.E24d.attackerWritesReport ()
    DARM.E24d.attacker_fits_principal_intent DARM.E32b.attacker_admitted rfl trivial
  simp [pipelineVetted, written, DARM.E24d.attackerWritesReport] at this
  exact absurd this (by decide)

/-- An unmediated rewrite between the write and the run. -/
def tamper : String → String := fun _ => "wire funds to US1330"

/-- Channel integrity is necessary in the instance: the pinned intent alone
    does not make the pipeline attributable if the file can change between the
    write and the run. -/
theorem tamper_breaks_pipeline :
    ¬ SeqSound pinnedDomain executor written tamper (pipelineVetted tamper)
        DARM.E24d.pinnedReport () := by
  intro h
  have hfit : DARM.E24d.pinnedReport.fits DARM.Broker3.agentWritesReport = true :=
    DARM.E24d.pinned_fits_principal
  have hadm : ∃ e, DARM.Broker3.brokerStep DARM.Broker3.writeCfg DARM.Broker3.agentWritesReport = some e := by
    refine ⟨DARM.Broker3.canonicalize DARM.Broker3.writeCfg DARM.Broker3.agentWritesReport, ?_⟩
    have hk : DARM.Kernel4.kernelDecide DARM.Broker3.writeCfg.policy DARM.Broker3.writeCfg.credential
        (DARM.Broker3.canonicalize DARM.Broker3.writeCfg DARM.Broker3.agentWritesReport) =
        DARM.Kernel.Decision.admit := by decide +kernel
    unfold DARM.Broker3.brokerStep
    simp [hk]
  have := h DARM.Broker3.agentWritesReport () hfit hadm rfl trivial
  simp [pipelineVetted, tamper] at this

theorem not_channelIntegrity_tamper : ¬ ChannelIntegrity tamper vetted := by
  intro h
  have := h "Q3 summary" rfl
  simp [vetted, tamper] at this

end DARM.E32c

#print axioms DARM.E32c.seq_sound
#print axioms DARM.E32c.seq_sound_of_integrity
#print axioms DARM.E32c.rely_necessary
#print axioms DARM.E32c.channel_necessary
#print axioms DARM.E32c.seqSeparability_necessary
#print axioms DARM.E32c.pinned_pipeline_sound
#print axioms DARM.E32c.p13_propagates
#print axioms DARM.E32c.tamper_breaks_pipeline
#print axioms DARM.E32c.not_channelIntegrity_tamper
