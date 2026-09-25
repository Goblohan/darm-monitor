/-
  R23 — DARM GUARD CAUSAL COVERAGE

  Question: can a successful DARM Guard effect be represented as a causeable
  semantic transition with explicit causal coverage and boundary mediation?

  The semantic model is B6's World (governed files with attestations, plus
  the audit log). Transitions relate whole states, as in E13 and R20.

  R23-A  Representability. Every modelled broker write is a whole-state
         transition and an R20 BoundaryMediatedStep. The boundary here is
         CHOSEN to be the broker's transitions, so mediation holds by model
         construction. This is a representation result: within the R23
         model, the broker transition is boundary-mediated. It does NOT show
         that the real broker mediates all writes.

  R23-B  Coverage iff A1 and A2. The causeable relation is defined by
         adversary capability, independently of the governed relation:
         broker writes, plus direct writes to governed files when A1 fails,
         plus edits to the evidence (audit log) when A2 fails. E13's
         CausalCoverage holds iff A1 and A2, with an explicit witness
         transition for each failure branch. The assumptions are not hidden
         in the causeable relation; the theorem exposes them.

  R23-C  Detection bridge. When coverage fails, an uncovered causeable
         transition exists (formal fact); for the modelled classes, a
         direct write that changes an attested file's content, and an
         evidence edit that drops the entry of a surviving attested file,
         B6's verification flags the result (runtime evidence). This is
         not "coverage failure = detection": other failures (reads, writes
         to unattested files, edits that keep an entry) are not claimed.

  Not claimed: that the real broker realizes this model (a runtime
  correspondence is separate work); physical completeness of the model.
-/
import E13CausalSemanticCorrespondence
import B6EffectIntegrity

namespace DARM.R23

open GRBS.R20DARMToSemanticCorrespondence (SemanticSystem SemanticBoundary BoundaryMediatedStep)
open GRBS.E13CausalSemanticCorrespondence (CausalCoverage CauseableTransition GovernedTransition)
open DARM.EffectIntegrity (World File brokerWrite tamper flagged Honest
  tamper_detected truncation_detected)

/-! ## The governed relation: broker writes -/

def brokerStep (w w' : World) : Prop := ∃ rid t d, w' = brokerWrite w rid t d

def governed : GovernedTransition World := fun w w' => brokerStep w w'

/-- The invariant that distinguishes a broker step: it appends exactly one log entry. -/
theorem brokerStep_log_grows {w w' : World} (h : brokerStep w w') :
    w'.log.length = w.log.length + 1 := by
  obtain ⟨rid, t, d, rfl⟩ := h
  simp [brokerWrite]

/-! ## The causeable relation: adversary capability, gated by the deployment -/

structure Deployment where
  fileBypass : Bool       -- true: A1 fails (a route to governed files avoids the broker)
  evidenceBypass : Bool   -- true: A2 fails (the evidence can be edited)

def A1 (d : Deployment) : Prop := d.fileBypass = false
def A2 (d : Deployment) : Prop := d.evidenceBypass = false

/-- Creating a governed file outside the broker: content, no attestation. -/
def create (w : World) (t d : String) : World :=
  { w with files := fun x => if x = t then some { digest := d, att := none } else w.files x }

/-- A write to a governed file that does not go through the broker: modifying
    an existing file in place (keeping its attestation), or creating an absent
    one. Creation was added after tests/r23_conflict.py (Case B) showed that
    the first version of R23 under-approximated the real adversary. -/
def directWrite (w w' : World) : Prop :=
  (∃ t d', w' = tamper w t d') ∨ (∃ t d, w.files t = none ∧ w' = create w t d)

/-- An edit to the audit log that does not go through the broker. -/
def evidenceEdit (w w' : World) : Prop :=
  ∃ log', w' = { w with log := log' } ∧ log' ≠ w.log

def causeable (d : Deployment) : CauseableTransition World := fun w w' =>
  brokerStep w w' ∨
  (d.fileBypass = true ∧ directWrite w w') ∨
  (d.evidenceBypass = true ∧ evidenceEdit w w')

/-! ## R23-A: representability (mediation by model construction) -/

def sys : SemanticSystem := { State := World, Step := governed }
def bdy : SemanticBoundary sys := { mediated := governed }

/-- Within the R23 model, every broker write is a boundary-mediated step.
    True by construction of the boundary; a representation result only. -/
theorem broker_write_representable (w : World) (rid : Nat) (t d : String) :
    BoundaryMediatedStep sys bdy w (brokerWrite w rid t d) :=
  ⟨⟨rid, t, d, rfl⟩, ⟨rid, t, d, rfl⟩⟩

/-! ## R23-B: coverage iff the deployment assumptions -/

theorem direct_not_governed (w : World) (t d' : String) : ¬ governed w (tamper w t d') := by
  intro h
  have hl := brokerStep_log_grows h
  have hlog : (tamper w t d').log = w.log := rfl
  rw [hlog] at hl
  exact Nat.succ_ne_self _ hl.symm

/-- A witness world: one attested file "t" with content digest "d". -/
def w0 : World := brokerWrite DARM.EffectIntegrity.empty 1 "t" "d"

theorem truncation_not_governed : ¬ governed w0 { w0 with log := [] } := by
  intro h
  have hl := brokerStep_log_grows h
  simp [w0, brokerWrite, DARM.EffectIntegrity.empty] at hl

theorem truncation_is_evidence_edit : evidenceEdit w0 { w0 with log := [] } :=
  ⟨[], rfl, by simp [w0, brokerWrite, DARM.EffectIntegrity.empty]⟩

/-- A1 fails: a causeable transition that is not governed. -/
theorem a1_failure_witness (d : Deployment) (h : ¬ A1 d) :
    ∃ w w', causeable d w w' ∧ ¬ governed w w' := by
  have hf : d.fileBypass = true := by
    cases hb : d.fileBypass <;> simp_all [A1]
  exact ⟨w0, tamper w0 "t" "x", Or.inr (Or.inl ⟨hf, Or.inl ⟨"t", "x", rfl⟩⟩), direct_not_governed _ _ _⟩

/-- A2 fails: a causeable transition that is not governed. -/
theorem a2_failure_witness (d : Deployment) (h : ¬ A2 d) :
    ∃ w w', causeable d w w' ∧ ¬ governed w w' := by
  have he : d.evidenceBypass = true := by
    cases hb : d.evidenceBypass <;> simp_all [A2]
  exact ⟨w0, { w0 with log := [] }, Or.inr (Or.inr ⟨he, truncation_is_evidence_edit⟩),
    truncation_not_governed⟩

/-- R23-B: causal coverage holds exactly when A1 and A2 hold. -/
theorem coverage_iff_assumptions (d : Deployment) :
    CausalCoverage (causeable d) governed ↔ (A1 d ∧ A2 d) := by
  constructor
  · intro hcov
    constructor
    · show d.fileBypass = false
      cases hb : d.fileBypass with
      | false => rfl
      | true =>
        have h1 : ¬ A1 d := by simp [A1, hb]
        obtain ⟨w, w', hc, hng⟩ := a1_failure_witness d h1
        exact (hng (hcov w w' hc)).elim
    · show d.evidenceBypass = false
      cases hb : d.evidenceBypass with
      | false => rfl
      | true =>
        have h2 : ¬ A2 d := by simp [A2, hb]
        obtain ⟨w, w', hc, hng⟩ := a2_failure_witness d h2
        exact (hng (hcov w w' hc)).elim
  · rintro ⟨h1, h2⟩ w w' hc
    rcases hc with hb | ⟨hf, _⟩ | ⟨he, _⟩
    · exact hb
    · simp [A1] at h1; simp [h1] at hf
    · simp [A2] at h2; simp [h2] at he

/-- The failure direction, stated on its own. -/
theorem assumption_failure_breaks_coverage (d : Deployment) (h : ¬ A1 d ∨ ¬ A2 d) :
    ¬ CausalCoverage (causeable d) governed := by
  intro hc
  have hab := (coverage_iff_assumptions d).mp hc
  rcases h with h | h
  · exact h hab.1
  · exact h hab.2

/-! ## R23-C: coverage failure, and runtime evidence for modelled classes -/

/-- A1 fails, and a direct write changes an attested file's content: the
    transition is causeable, not governed, and B6's verification flags it. -/
theorem uncovered_direct_write_detected (w : World) (t : String) (f : File) (r : Nat)
    (dg d' : String) (hf : w.files t = some f) (ha : f.att = some (r, dg)) (hne : d' ≠ dg) :
    causeable ⟨true, false⟩ w (tamper w t d') ∧
    ¬ governed w (tamper w t d') ∧
    flagged (tamper w t d') t = true :=
  ⟨Or.inr (Or.inl ⟨rfl, Or.inl ⟨t, d', rfl⟩⟩), direct_not_governed w t d',
   tamper_detected w t f r dg d' hf ha hne⟩

/-- A2 fails, and an evidence edit drops the entry of a surviving attested
    file: the transition is causeable, not governed, and B6 flags it. -/
theorem uncovered_evidence_edit_detected (w : World) (log' : List (Nat × String × String))
    (t : String) (f : File) (r : Nat) (dg : String) (hw : Honest w)
    (hf : w.files t = some f) (ha : f.att = some (r, dg)) (hgone : (r, t, dg) ∉ log')
    (hlen : log'.length ≠ w.log.length + 1) :
    causeable ⟨false, true⟩ w { w with log := log' } ∧
    ¬ governed w { w with log := log' } ∧
    flagged { w with log := log' } t = true := by
  have hmem := (hw t f hf r dg ha).2
  have hne : log' ≠ w.log := by
    intro heq
    rw [heq] at hgone
    exact hgone hmem
  refine ⟨Or.inr (Or.inr ⟨rfl, log', rfl, hne⟩), ?_, truncation_detected w log' t f r dg hw hf ha hgone⟩
  intro h
  exact hlen (by simpa using brokerStep_log_grows h)

/-! ## R23-D: a coverage failure B6's verification cannot see -/

theorem create_not_governed (w : World) (t d : String) : ¬ governed w (create w t d) := by
  intro h
  have hl := brokerStep_log_grows h
  have hlog : (create w t d).log = w.log := rfl
  rw [hlog] at hl
  exact Nat.succ_ne_self _ hl.symm

/-- A1 fails and a governed file is created outside the broker: the transition
    is causeable and not governed, yet it preserves Honest and B6's
    verification does not flag it. Coverage fails undetectably. -/
theorem uncovered_creation_undetected (w : World) (t d : String)
    (hnone : w.files t = none) (hw : Honest w) :
    causeable ⟨true, false⟩ w (create w t d) ∧
    ¬ governed w (create w t d) ∧
    Honest (create w t d) ∧
    flagged (create w t d) t = false := by
  refine ⟨Or.inr (Or.inl ⟨rfl, Or.inr ⟨t, d, hnone, rfl⟩⟩), create_not_governed w t d, ?_, ?_⟩
  · intro x f hx r dd ha
    by_cases hxt : x = t
    · subst hxt
      simp [create] at hx
      subst hx
      simp at ha
    · simp [create, hxt] at hx
      exact hw x f hx r dd ha
  · simp [flagged, create]

end DARM.R23

#print axioms DARM.R23.broker_write_representable
#print axioms DARM.R23.coverage_iff_assumptions
#print axioms DARM.R23.assumption_failure_breaks_coverage
#print axioms DARM.R23.uncovered_direct_write_detected
#print axioms DARM.R23.uncovered_evidence_edit_detected
#print axioms DARM.R23.uncovered_creation_undetected
