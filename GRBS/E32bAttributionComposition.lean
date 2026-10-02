/-
  E32b — ATTRIBUTION INVARIANCE AND COMPOSITION (extends E32)

  E32 proves one-way transfer of completeness under FitCoverage,
  AdmissionReflects and AcceptsForward. This module adds:
    - admitted-only coverage: coverage need range only over proposals the
      target boundary admits (`admitted_coverage_strictly_weaker` shows this
      is strictly weaker than E32's FitCoverage);
    - independent necessity of each condition (four countermodels);
    - the dual conditions and invariance (iff);
    - composition along chains of domains, and across domains acting jointly
      (sound iff acceptance is separable; composed-harm countermodel);
    - instances on B3/E24b: argument reordering is an attribution
      automorphism; P13 is a coverage failure.

  When does "every admitted effect that fits the
  principal's intent is acceptable to the principal" survive a change of
  effect domain, and how does it compose?

  An effect domain packages what the boundary sees and what the principal
  accepts: proposals, intents, a fit test, an admission predicate (the
  boundary), and an acceptance judgment (the principal's specification, never
  evaluated by the boundary). Attribution in a domain (`Sound`) is E24d's
  completeness-under-admission, abstracted.

  A transformation (f on proposals, g on intents) transfers attribution
  A → B under four structural conditions:
    FitReflect      fitting in B, after translation, implies fitting in A
    AdmitReflect    admission in B implies admission in A
    AccPreserve     acceptable in A stays acceptable in B
    Coverage        every fitting, admitted B-proposal has an A-preimage
                    (the transformation introduces no new degree of freedom)

  Results
    transfer            the four conditions carry Sound A i to Sound B (g i)
    reflect_back        the dual three carry Sound B (g i) back to Sound A i
    invariant           both together: attribution is invariant (iff)
    *_necessary         each of the four is independently necessary:
                        a countermodel satisfies the other three, is sound
                        in A, and unsound in B
    compose_transfer    the conditions are closed under composition, so
                        attribution transfers along any chain of domains
    tensor_sound        across domains acting jointly, component soundness
                        gives joint soundness iff acceptance is separable
    separability_necessary   componentwise-attributable joint effect that the
                        principal does not accept (composed harm)
  Instances on the real definitions (B3 writeCfg, E24b Intent.fits, E24d)
    reverseArgs is an attribution automorphism of the B3 write domain, so the
      pinned intent's soundness is invariant under argument reordering
    the path-only embedding fails Coverage at exactly the attacker's write:
      P13 is a coverage failure, a transformation that adds a free content
      dimension the intent does not constrain

  NOT claimed: that any particular deployed translation (e.g. DARM ↔ FIDES)
  satisfies these conditions; that is a per-adapter obligation, checked by
  darm-verify on finite scenarios, not proved here. Sequential effects where
  one domain's effect becomes another's input are not modelled.
-/
import E24dRedemption
import E32AuthorizationTransformation

namespace DARM.E32b

/-! ## Domains and attribution -/

/-- An effect domain. `admits` is the boundary; `acc` is the principal's
    acceptance relative to an intent (a specification, not a check). -/
structure Domain where
  P : Type
  I : Type
  fits : I → P → Bool
  admits : P → Prop
  acc : I → P → Prop

/-- Attribution: every fitting, admitted proposal is acceptable. -/
def Sound (D : Domain) (i : D.I) : Prop :=
  ∀ p, D.fits i p = true → D.admits p → D.acc i p

/-- A transformation of effect domains. -/
structure Transform (A B : Domain) where
  f : A.P → B.P
  g : A.I → B.I

variable {A B C : Domain}

def FitReflect (t : Transform A B) : Prop :=
  ∀ i p, B.fits (t.g i) (t.f p) = true → A.fits i p = true
def AdmitReflect (t : Transform A B) : Prop :=
  ∀ p, B.admits (t.f p) → A.admits p
def AccPreserve (t : Transform A B) : Prop :=
  ∀ i p, A.acc i p → B.acc (t.g i) (t.f p)
def Coverage (t : Transform A B) : Prop :=
  ∀ i q, B.fits (t.g i) q = true → B.admits q → ∃ p, t.f p = q

/-- The dual conditions, for carrying attribution back from B to A. -/
def FitPreserve (t : Transform A B) : Prop :=
  ∀ i p, A.fits i p = true → B.fits (t.g i) (t.f p) = true
def AdmitPreserve (t : Transform A B) : Prop :=
  ∀ p, A.admits p → B.admits (t.f p)
def AccReflect (t : Transform A B) : Prop :=
  ∀ i p, B.acc (t.g i) (t.f p) → A.acc i p

/-- An attribution morphism: the four transfer conditions. -/
structure Morphism (t : Transform A B) : Prop where
  fit : FitReflect t
  admits : AdmitReflect t
  acc : AccPreserve t
  cover : Coverage t

/-! ## Transfer, reflection, invariance -/

theorem transfer (t : Transform A B) (m : Morphism t) (i : A.I) (h : Sound A i) :
    Sound B (t.g i) := by
  intro q hfit hadm
  obtain ⟨p, rfl⟩ := m.cover i q hfit hadm
  exact m.acc i p (h p (m.fit i p hfit) (m.admits p hadm))

theorem reflect_back (t : Transform A B) (hf : FitPreserve t) (ha : AdmitPreserve t)
    (hc : AccReflect t) (i : A.I) (h : Sound B (t.g i)) : Sound A i := by
  intro p hfit hadm
  exact hc i p (h (t.f p) (hf i p hfit) (ha p hadm))

/-- Invariance: under a morphism that also satisfies the dual conditions,
    attribution holds in A exactly when it holds in B. -/
theorem invariant (t : Transform A B) (m : Morphism t) (hf : FitPreserve t)
    (ha : AdmitPreserve t) (hc : AccReflect t) (i : A.I) :
    Sound A i ↔ Sound B (t.g i) :=
  ⟨transfer t m i, reflect_back t hf ha hc i⟩

/-! ## Necessity: each condition is independently required

Four countermodels over `Bool`. In each, three conditions hold, the source
intent is sound, and the target is not. -/

/-- Base source: one proposal (`true`) fits, is admitted, is acceptable. -/
def srcOK : Domain where
  P := Bool
  I := Unit
  fits := fun _ p => p
  admits := fun _ => True
  acc := fun _ p => p = true

theorem srcOK_sound : Sound srcOK () := by
  intro p hp _; exact hp

/-- Target in which `false` fits, is admitted, and is NOT acceptable. -/
def tgtBad : Domain where
  P := Bool
  I := Unit
  fits := fun _ _ => true
  admits := fun _ => True
  acc := fun _ p => p = true

theorem tgtBad_unsound : ¬ Sound tgtBad () := by
  intro h; exact Bool.noConfusion (h false rfl trivial)

/-- One-point source: its only proposal fits, is admitted, is acceptable. -/
def srcPoint : Domain where
  P := Unit
  I := Unit
  fits := fun _ _ => true
  admits := fun _ => True
  acc := fun _ _ => True

/-- Coverage necessary: f lands on the acceptable target point only; the
    unacceptable target point has no preimage. -/
def tCover : Transform srcPoint tgtBad := ⟨fun _ => true, id⟩

theorem coverage_necessary :
    FitReflect tCover ∧ AdmitReflect tCover ∧ AccPreserve tCover ∧ ¬ Coverage tCover ∧
    Sound srcPoint () ∧ ¬ Sound tgtBad (tCover.g ()) := by
  refine ⟨?_, ?_, ?_, ?_, fun _ _ _ => trivial, tgtBad_unsound⟩
  · intro _ _ _; rfl
  · intro _ _; trivial
  · intro _ _ _; rfl
  · intro h
    obtain ⟨p, hp⟩ := h () false rfl trivial
    exact Bool.noConfusion hp

/-- Source where both points fit and are admitted, but only `true` is
    acceptable: used with an unacceptable *source* point to break FitReflect. -/
def srcNarrow : Domain where
  P := Bool
  I := Unit
  fits := fun _ p => p
  admits := fun _ => True
  acc := fun _ p => p = true

/-- FitReflect necessary: identity on points, but the target intent fits
    `false` where the source intent did not. -/
def tFit : Transform srcNarrow tgtBad := ⟨id, id⟩

theorem fitReflect_necessary :
    ¬ FitReflect tFit ∧ AdmitReflect tFit ∧ AccPreserve tFit ∧ Coverage tFit ∧
    Sound srcNarrow () ∧ ¬ Sound tgtBad (tFit.g ()) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, tgtBad_unsound⟩
  · intro h; exact Bool.noConfusion (h () false rfl)
  · intro _ _; trivial
  · intro _ _ h; exact h
  · intro _ q _ _; exact ⟨q, rfl⟩
  · intro p hp _; exact hp

/-- Source where `false` fits but is NOT admitted (the boundary stops it). -/
def srcGuarded : Domain where
  P := Bool
  I := Unit
  fits := fun _ _ => true
  admits := fun p => p = true
  acc := fun _ p => p = true

/-- AdmitReflect necessary: the target boundary admits what the source
    boundary refused. -/
def tAdmit : Transform srcGuarded tgtBad := ⟨id, id⟩

theorem admitReflect_necessary :
    FitReflect tAdmit ∧ ¬ AdmitReflect tAdmit ∧ AccPreserve tAdmit ∧ Coverage tAdmit ∧
    Sound srcGuarded () ∧ ¬ Sound tgtBad (tAdmit.g ()) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, tgtBad_unsound⟩
  · intro _ _ _; rfl
  · intro h; exact Bool.noConfusion (h false trivial)
  · intro _ _ h; exact h
  · intro _ q _ _; exact ⟨q, rfl⟩
  · intro p _ hp; exact hp

/-- Source in which everything is acceptable. -/
def srcAll : Domain where
  P := Bool
  I := Unit
  fits := fun _ _ => true
  admits := fun _ => True
  acc := fun _ _ => True

/-- AccPreserve necessary: the target principal accepts less than the source. -/
def tAcc : Transform srcAll tgtBad := ⟨id, id⟩

theorem accPreserve_necessary :
    FitReflect tAcc ∧ AdmitReflect tAcc ∧ ¬ AccPreserve tAcc ∧ Coverage tAcc ∧
    Sound srcAll () ∧ ¬ Sound tgtBad (tAcc.g ()) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, tgtBad_unsound⟩
  · intro _ _ _; rfl
  · intro _ _; trivial
  · intro h; exact Bool.noConfusion (h () false trivial)
  · intro _ q _ _; exact ⟨q, rfl⟩
  · intro _ _ _; trivial

/-! ## Composition along chains of domains -/

def Transform.comp (t : Transform A B) (u : Transform B C) : Transform A C :=
  ⟨u.f ∘ t.f, u.g ∘ t.g⟩

theorem Morphism.comp (t : Transform A B) (u : Transform B C) (mt : Morphism t)
    (mu : Morphism u) : Morphism (t.comp u) where
  fit := fun i p h => mt.fit i p (mu.fit (t.g i) (t.f p) h)
  admits := fun p h => mt.admits p (mu.admits (t.f p) h)
  acc := fun i p h => mu.acc (t.g i) (t.f p) (mt.acc i p h)
  cover := by
    intro i r hfit hadm
    obtain ⟨q, rfl⟩ := mu.cover (t.g i) r hfit hadm
    have hfq : B.fits (t.g i) q = true := mu.fit (t.g i) q hfit
    have haq : B.admits q := mu.admits q hadm
    obtain ⟨p, rfl⟩ := mt.cover i q hfq haq
    exact ⟨p, rfl⟩

/-- Attribution transfers along any chain of attribution morphisms. -/
theorem compose_transfer (t : Transform A B) (u : Transform B C) (mt : Morphism t)
    (mu : Morphism u) (i : A.I) (h : Sound A i) : Sound C (u.g (t.g i)) :=
  transfer (t.comp u) (Morphism.comp t u mt mu) i h

/-! ## Composition across domains acting jointly -/

/-- Two domains acting together (one action with effects in both, e.g. write a
    file and send an email). The boundary admits the pair iff each component
    boundary admits its part; the joint acceptance is supplied separately,
    because the principal judges the combined effect. -/
def tensor (A B : Domain) (jointAcc : A.I × B.I → A.P × B.P → Prop) : Domain where
  P := A.P × B.P
  I := A.I × B.I
  fits := fun ij pq => A.fits ij.1 pq.1 && B.fits ij.2 pq.2
  admits := fun pq => A.admits pq.1 ∧ B.admits pq.2
  acc := jointAcc

/-- Separable acceptance: componentwise acceptable implies jointly acceptable. -/
def Separable (A B : Domain) (jointAcc : A.I × B.I → A.P × B.P → Prop) : Prop :=
  ∀ i j p q, A.acc i p → B.acc j q → jointAcc (i, j) (p, q)

theorem tensor_sound (jointAcc : A.I × B.I → A.P × B.P → Prop)
    (hs : Separable A B jointAcc) (i : A.I) (j : B.I)
    (hA : Sound A i) (hB : Sound B j) : Sound (tensor A B jointAcc) (i, j) := by
  intro pq hfit hadm
  simp only [tensor, Bool.and_eq_true] at hfit
  exact hs i j pq.1 pq.2 (hA pq.1 hfit.1 hadm.1) (hB pq.2 hfit.2 hadm.2)

/-- Separability is necessary: two domains each attributable (every admitted
    fitting effect acceptable on its own), and a joint effect that is
    componentwise acceptable but that the principal does not accept — the
    composed-harm pattern (e.g. reading a secret here, sending it there). -/
def unitOK : Domain where
  P := Unit
  I := Unit
  fits := fun _ _ => true
  admits := fun _ => True
  acc := fun _ _ => True

def rejectsTogether : unitOK.I × unitOK.I → unitOK.P × unitOK.P → Prop :=
  fun _ _ => False

theorem separability_necessary :
    Sound unitOK () ∧ Sound unitOK () ∧ ¬ Separable unitOK unitOK rejectsTogether ∧
    ¬ Sound (tensor unitOK unitOK rejectsTogether) ((), ()) := by
  refine ⟨fun _ _ _ => trivial, fun _ _ _ => trivial, ?_, ?_⟩
  · intro h; exact h () () () () trivial trivial
  · intro h; exact h ((), ()) rfl ⟨trivial, trivial⟩

/-! ## Instance 1: argument order is an attribution automorphism of B3 writes -/

open DARM.Broker (Proposal)
open DARM.E24b (Intent)

/-- The B3 write domain, with acceptance given per intent. -/
def writeDomain (acc : Intent → Proposal → Prop) : Domain where
  P := Proposal
  I := Intent
  fits := fun i p => i.fits p
  admits := fun p => ∃ e, DARM.Broker3.brokerStep DARM.Broker3.writeCfg p = some e
  acc := acc

def reverseArgs (p : Proposal) : Proposal := { tool := p.tool, args := p.args.reverse }

theorem reverseArgs_involutive (p : Proposal) : reverseArgs (reverseArgs p) = p := by
  cases p; simp [reverseArgs]

theorem fits_reverse (i : Intent) (p : Proposal) : i.fits (reverseArgs p) = i.fits p := by
  have h : DARM.E24b.constraintHolds p.args.reverse = DARM.E24b.constraintHolds p.args := by
    funext c; simp [DARM.E24b.constraintHolds]
  simp [Intent.fits, reverseArgs, h]

theorem admissible_reverse (p : Proposal) :
    DARM.Kernel4.admissible DARM.Broker3.writeCfg.policy DARM.Broker3.writeCfg.credential
      (DARM.Broker3.canonicalize DARM.Broker3.writeCfg (reverseArgs p)) =
    DARM.Kernel4.admissible DARM.Broker3.writeCfg.policy DARM.Broker3.writeCfg.credential
      (DARM.Broker3.canonicalize DARM.Broker3.writeCfg p) := by
  simp [DARM.Kernel4.admissible, DARM.Kernel4.argsAllowed, DARM.Kernel4.selectorsTrusted,
    DARM.Broker3.canonicalize, reverseArgs, List.map_reverse]

theorem admit_reverse (p : Proposal) :
    (∃ e, DARM.Broker3.brokerStep DARM.Broker3.writeCfg (reverseArgs p) = some e) ↔
    (∃ e, DARM.Broker3.brokerStep DARM.Broker3.writeCfg p = some e) := by
  have key : ∀ q : Proposal,
      (∃ e, DARM.Broker3.brokerStep DARM.Broker3.writeCfg q = some e) ↔
      DARM.Kernel4.admissible DARM.Broker3.writeCfg.policy DARM.Broker3.writeCfg.credential
        (DARM.Broker3.canonicalize DARM.Broker3.writeCfg q) = true := by
    intro q
    unfold DARM.Broker3.brokerStep
    rw [← DARM.Broker3.k4_admit_iff]
    constructor
    · rintro ⟨e, he⟩; split at he <;> simp_all
    · intro h; exact ⟨_, by rw [if_pos h]⟩
  rw [key, key, admissible_reverse]

/-- An acceptance judgment is order-blind if reordering arguments never
    changes it (true of any judgment about the denoted effect). -/
def OrderBlind (acc : Intent → Proposal → Prop) : Prop :=
  ∀ i p, acc i (reverseArgs p) ↔ acc i p

def reverseT (acc : Intent → Proposal → Prop) : Transform (writeDomain acc) (writeDomain acc) :=
  ⟨reverseArgs, id⟩

theorem reverse_morphism (acc : Intent → Proposal → Prop) (hb : OrderBlind acc) :
    Morphism (reverseT acc) where
  fit := fun (i : Intent) (p : Proposal) h => by
    have h' : Intent.fits i (reverseArgs p) = true := h
    rw [fits_reverse] at h'
    exact h'
  admits := fun p h => (admit_reverse p).mp h
  acc := fun i p h => (hb i p).mpr h
  cover := fun _ q _ _ => ⟨reverseArgs q, reverseArgs_involutive q⟩

/-- `WritesExactly` is about the denoted effect, so it is order-blind. -/
theorem writesExactly_orderBlind (path content : String) :
    OrderBlind (fun _ => DARM.E24d.WritesExactly path content) := by
  intro _ p
  simp [DARM.E24d.WritesExactly, reverseArgs]

/-- The pinned intent's attribution is invariant under argument reordering. -/
theorem pinned_sound_invariant_under_reordering :
    Sound (writeDomain (fun _ => DARM.E24d.WritesExactly "/workspace/reports/q3.md" "Q3 summary"))
      DARM.E24d.pinnedReport := by
  intro p hfit ⟨e, he⟩
  exact DARM.E24d.pinned_complete_under_b3 p e hfit he

theorem pinned_sound_after_reordering :
    Sound (writeDomain (fun _ => DARM.E24d.WritesExactly "/workspace/reports/q3.md" "Q3 summary"))
      ((reverseT _).g DARM.E24d.pinnedReport) :=
  transfer _ (reverse_morphism _ (writesExactly_orderBlind _ _)) _
    pinned_sound_invariant_under_reordering

/-! ## Instance 2: P13 is a coverage failure -/

/-- The path-only domain: a proposal is just a path; the principal accepts
    the report path. Here the path-only intent IS complete. -/
def pathDomain : Domain where
  P := String
  I := Unit
  fits := fun _ s => s == "/workspace/reports/q3.md"
  admits := fun _ => True
  acc := fun _ s => s = "/workspace/reports/q3.md"

theorem pathOnly_sound_in_path_domain : Sound pathDomain () := by
  intro (s : String) h _
  show s = "/workspace/reports/q3.md"
  have h' : (s == "/workspace/reports/q3.md") = true := h
  exact beq_iff_eq.mp h'

/-- Embedding into the write domain supplies the content the principal had in
    mind. The target judges the denoted effect. -/
def embedT : Transform pathDomain
    (writeDomain (fun _ => DARM.E24d.WritesExactly "/workspace/reports/q3.md" "Q3 summary")) :=
  ⟨fun s => { tool := "write_file", args := [("path", s), ("content", "Q3 summary")] },
   fun _ => DARM.E24b.forThisReport⟩

/-- The embedding has no preimage for the attacker's write: it adds a free
    content dimension the intent does not constrain. -/
theorem embed_misses_attacker : ¬ ∃ s, embedT.f s = DARM.E24d.attackerWritesReport := by
  rintro ⟨s, h⟩
  have h2 := congrArg (fun p : Proposal => p.args.getD 1 ("", "")) h
  simp [embedT, DARM.E24d.attackerWritesReport] at h2

theorem attacker_admitted :
    ∃ e, DARM.Broker3.brokerStep DARM.Broker3.writeCfg DARM.E24d.attackerWritesReport = some e := by
  refine ⟨DARM.Broker3.canonicalize DARM.Broker3.writeCfg DARM.E24d.attackerWritesReport, ?_⟩
  have hk : DARM.Kernel4.kernelDecide DARM.Broker3.writeCfg.policy DARM.Broker3.writeCfg.credential
      (DARM.Broker3.canonicalize DARM.Broker3.writeCfg DARM.E24d.attackerWritesReport) =
      DARM.Kernel.Decision.admit := by decide +kernel
  unfold DARM.Broker3.brokerStep
  simp [hk]

/-- Coverage fails exactly at the attacker's write. -/
theorem p13_is_coverage_failure : ¬ Coverage embedT := by
  intro h
  exact embed_misses_attacker
    (h () DARM.E24d.attackerWritesReport DARM.E24d.attacker_fits_principal_intent attacker_admitted)

/-- And attribution indeed fails in the target: path-only soundness in the
    path domain does not transfer (E24d.path_only_intent_incomplete, restated
    in this domain). -/
theorem p13_attribution_fails_in_target :
    Sound pathDomain () ∧
    ¬ Sound (writeDomain (fun _ => DARM.E24d.WritesExactly "/workspace/reports/q3.md" "Q3 summary"))
        (embedT.g ()) := by
  refine ⟨pathOnly_sound_in_path_domain, ?_⟩
  intro h
  obtain ⟨_, hall, _, _⟩ :=
    h DARM.E24d.attackerWritesReport DARM.E24d.attacker_fits_principal_intent attacker_admitted
  have h3 := hall ("content", "wire funds to US1330") (by simp [DARM.E24d.attackerWritesReport])
  exact absurd h3 (by decide)

/-! ## Relation to E32: coverage need only range over what the boundary admits -/

/-- Target where `false` fits but the boundary refuses it; `true` is fine. -/
def tgtGuarded : Domain where
  P := Bool
  I := Unit
  fits := fun _ _ => true
  admits := fun p => p = true
  acc := fun _ p => p = true

def tGuard : Transform srcPoint tgtGuarded := ⟨fun _ => true, id⟩

/-- E32's FitCoverage fails here: `false` fits the target intent and has no
    preimage. Admitted-only Coverage holds, the transform is a morphism, and
    attribution transfers. The boundary discharges the part of coverage that
    concerns proposals it refuses (as K4's deny-by-default does for the pinned
    intent). -/
theorem admitted_coverage_strictly_weaker :
    ¬ DARM.E32.FitCoverage srcPoint.fits tgtGuarded.fits tGuard.f tGuard.g () ∧
    Morphism tGuard ∧ Sound tgtGuarded (tGuard.g ()) := by
  have m : Morphism tGuard :=
    { fit := fun _ _ _ => rfl
      admits := fun _ _ => trivial
      acc := fun _ _ _ => rfl
      cover := by
        intro _ q _ hq
        exact ⟨(), hq.symm⟩ }
  refine ⟨?_, m, transfer tGuard m () (fun _ _ _ => trivial)⟩
  intro h
  obtain ⟨_, hp, _⟩ := h false rfl
  exact Bool.noConfusion hp

/-- Conversely, E32's hypotheses yield this module's Coverage and FitReflect
    on the points they cover, so E32's transfer is the special case where the
    boundary discharges nothing. -/
theorem e32_fitCoverage_gives_coverage {A B : Domain} (t : Transform A B) (i : A.I)
    (h : DARM.E32.FitCoverage A.fits B.fits t.f t.g i) :
    ∀ q, B.fits (t.g i) q = true → B.admits q → ∃ p, t.f p = q ∧ A.fits i p = true :=
  fun q hq _ => h q hq

end DARM.E32b

#print axioms DARM.E32b.transfer
#print axioms DARM.E32b.invariant
#print axioms DARM.E32b.coverage_necessary
#print axioms DARM.E32b.fitReflect_necessary
#print axioms DARM.E32b.admitReflect_necessary
#print axioms DARM.E32b.accPreserve_necessary
#print axioms DARM.E32b.compose_transfer
#print axioms DARM.E32b.tensor_sound
#print axioms DARM.E32b.separability_necessary
#print axioms DARM.E32b.reverse_morphism
#print axioms DARM.E32b.pinned_sound_after_reordering
#print axioms DARM.E32b.p13_is_coverage_failure
#print axioms DARM.E32b.p13_attribution_fails_in_target
#print axioms DARM.E32b.admitted_coverage_strictly_weaker
