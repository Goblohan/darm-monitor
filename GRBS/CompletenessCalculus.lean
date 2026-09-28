/-
  AUTHORIZATION COMPLETENESS, AS A CALCULUS

  One notion, stated once. An authorization is complete for an acceptance
  judgment, relative to a boundary, if every proposal that fits it AND is
  admitted by the boundary is acceptable. A mechanism is mediated if whatever
  it executes is fitted by some authorization in its registry and admitted by
  the boundary. Then: a mediated mechanism whose authorizations are all
  complete executes only acceptable proposals, whoever proposed them.

  Generic lemmas: completeness survives narrower fitting (pinning, premises),
  a stricter boundary, a looser acceptance judgment, and a smaller registry
  (revocation, consumption); authorizations fitting the same proposals are
  equally complete; pinning through an injective digest is pinning the value.

  Instances: E24b's step and E24d-R's premise registry are mediated at B3;
  E24d's CompleteUnder is this one at B3, so pinned_complete_under_b3 is an
  instance; completeness of a registry is preserved by revocation (E24c) and
  consumption.

  NOT claimed: that SHA-256 is injective (it is not, on all inputs; the digest
  case holds under collision resistance on the contents involved); anything
  about content that cannot be enumerated or pinned (E24e, lineage).
-/
import E24dRegistryPremises

namespace DARM.Completeness

open DARM.Broker (Proposal)

section Generic

variable {A P : Type}

def CompleteUnder (admit acc : P → Prop) (fits : A → P → Prop) (i : A) : Prop :=
  ∀ p, fits i p → admit p → acc p

/-- The one property a mechanism must have for the calculus to apply. -/
def Mediated (exec admit : P → Prop) (fits : A → P → Prop) (reg : List A) : Prop :=
  ∀ p, exec p → ∃ i ∈ reg, fits i p ∧ admit p

/-- A mediated mechanism whose authorizations are all complete executes only
    acceptable proposals, whoever proposed them, in any order. -/
theorem safety {exec admit acc : P → Prop} {fits : A → P → Prop} {reg : List A}
    (hm : Mediated exec admit fits reg) (hc : ∀ i ∈ reg, CompleteUnder admit acc fits i) :
    ∀ p, exec p → acc p := by
  intro p hp
  obtain ⟨i, hi, hf, ha⟩ := hm p hp
  exact hc i hi p hf ha

theorem complete_of_narrower_fit {admit acc : P → Prop} {fits : A → P → Prop} {i j : A}
    (hji : ∀ p, fits j p → fits i p) (h : CompleteUnder admit acc fits i) :
    CompleteUnder admit acc fits j :=
  fun p hf ha => h p (hji p hf) ha

theorem complete_of_narrower_admission {admit admit' acc : P → Prop} {fits : A → P → Prop} {i : A}
    (h' : ∀ p, admit' p → admit p) (h : CompleteUnder admit acc fits i) :
    CompleteUnder admit' acc fits i :=
  fun p hf ha => h p hf (h' p ha)

theorem complete_of_weaker_acceptance {admit acc acc' : P → Prop} {fits : A → P → Prop} {i : A}
    (h' : ∀ p, acc p → acc' p) (h : CompleteUnder admit acc fits i) :
    CompleteUnder admit acc' fits i :=
  fun p hf ha => h' p (h p hf ha)

/-- A smaller registry keeps completeness: revocation and consumption preserve it. -/
theorem complete_sublist {admit acc : P → Prop} {fits : A → P → Prop} {reg reg' : List A}
    (hsub : ∀ i ∈ reg', i ∈ reg) (h : ∀ i ∈ reg, CompleteUnder admit acc fits i) :
    ∀ i ∈ reg', CompleteUnder admit acc fits i :=
  fun i hi => h i (hsub i hi)

/-- Authorizations fitting the same proposals are equally complete. -/
theorem complete_transfer {A' : Type} {admit acc : P → Prop} {fits : A → P → Prop}
    {fits' : A' → P → Prop} {i : A} {j : A'} (heq : ∀ p, fits' j p ↔ fits i p) :
    CompleteUnder admit acc fits i ↔ CompleteUnder admit acc fits' j := by
  constructor
  · intro h p hf ha
    exact h p ((heq p).mp hf) ha
  · intro h p hf ha
    exact h p ((heq p).mpr hf) ha

/-- Pinning through an injective digest is the same constraint as pinning the
    value. Collision resistance is the assumption that makes a real digest
    behave injectively on the contents involved. -/
theorem pin_by_injective {V D : Type} (h : V → D) (hinj : ∀ x y, h x = h y → x = y) (x v : V) :
    h x = h v ↔ x = v :=
  ⟨hinj x v, fun e => by rw [e]⟩

end Generic

/-! ## Instances at B3 -/

def admitB3 (cfg : DARM.Broker3.Config) (p : Proposal) : Prop :=
  ∃ e, DARM.Broker3.brokerStep cfg p = some e

def fitsB (i : DARM.E24b.Intent) (p : Proposal) : Prop := i.fits p = true

theorem e24b_mediated (cfg : DARM.Broker3.Config) (reg : DARM.E24b.Registry) (c : DARM.E24.Premise) :
    Mediated (fun p => ∃ e, (DARM.E24b.step cfg reg p c).1 = some e) (admitB3 cfg) fitsB reg.intents := by
  intro p ⟨e, h⟩
  obtain ⟨i, _, hmem, hfit, hb⟩ := DARM.E24b.execution_requires_fitting_intent cfg reg p c e h
  exact ⟨i, hmem, hfit, e, hb⟩

theorem e24dR_mediated (cfg : DARM.Broker3.Config) (w : DARM.E24dR.World)
    (reg : DARM.E24dR.PRegistry) (c : DARM.E24.Premise) :
    Mediated (fun p => ∃ e, (DARM.E24dR.stepR cfg w reg p c).1 = some e) (admitB3 cfg)
      (fun (i : DARM.E24dR.PIntent) p => i.intent.fits p = true) reg.intents := by
  intro p ⟨e, h⟩
  obtain ⟨i, hmem, hfit, _, hb⟩ := DARM.E24dR.executed_implies_usable cfg w reg p c e h
  exact ⟨i, hmem, hfit, e, hb⟩

/-- E24d's CompleteUnder is this calculus's, instantiated at B3. -/
theorem e24d_complete_under_is_instance (cfg : DARM.Broker3.Config) (acc : DARM.E24d.Acceptable)
    (i : DARM.E24b.Intent) :
    DARM.E24d.CompleteUnder cfg acc i ↔ CompleteUnder (admitB3 cfg) acc fitsB i := by
  constructor
  · intro h p hf ha
    obtain ⟨e, he⟩ := ha
    exact h p e hf he
  · intro h p e hf he
    exact h p hf ⟨e, he⟩

/-- pinned_complete_under_b3, as an instance of the calculus. -/
theorem pinned_complete :
    CompleteUnder (admitB3 DARM.Broker3.writeCfg)
      (DARM.E24d.WritesExactly "/workspace/reports/q3.md" "Q3 summary") fitsB DARM.E24d.pinnedReport :=
  (e24d_complete_under_is_instance _ _ _).mp DARM.E24d.pinned_complete_under_b3

/-- Premises only narrow: if every intent's underlying E24b intent is complete
    under B3, whatever the premise registry executes is acceptable. -/
theorem premise_registry_safe (cfg : DARM.Broker3.Config) (acc : Proposal → Prop)
    (w : DARM.E24dR.World) (reg : DARM.E24dR.PRegistry) (c : DARM.E24.Premise)
    (hc : ∀ i ∈ reg.intents, CompleteUnder (admitB3 cfg) acc fitsB i.intent) :
    ∀ p, (∃ e, (DARM.E24dR.stepR cfg w reg p c).1 = some e) → acc p :=
  safety (e24dR_mediated cfg w reg c) (fun i hi p hf ha => hc i hi p hf ha)

/-- Completeness of a registry survives revocation (E24c). -/
theorem revocation_preserves_completeness (reg : DARM.E24b.Registry) (r : DARM.E24b.Intent)
    (admit acc : Proposal → Prop) (h : ∀ i ∈ reg.intents, CompleteUnder admit acc fitsB i) :
    ∀ i ∈ (DARM.E24c.revoke reg r).intents, CompleteUnder admit acc fitsB i :=
  complete_sublist (fun i hi => (List.mem_filter.mp hi).1) h

/-- ...and consumption: an invariant across every step, not a one-step property. -/
theorem consumption_preserves_completeness (reg : List DARM.E24b.Intent) (x : DARM.E24b.Intent)
    (admit acc : Proposal → Prop) (h : ∀ i ∈ reg, CompleteUnder admit acc fitsB i) :
    ∀ i ∈ reg.erase x, CompleteUnder admit acc fitsB i :=
  complete_sublist (fun i hi => List.mem_of_mem_erase hi) h

end DARM.Completeness

#print axioms DARM.Completeness.safety
#print axioms DARM.Completeness.complete_transfer
#print axioms DARM.Completeness.pin_by_injective
#print axioms DARM.Completeness.e24b_mediated
#print axioms DARM.Completeness.pinned_complete
#print axioms DARM.Completeness.premise_registry_safe
#print axioms DARM.Completeness.revocation_preserves_completeness
#print axioms DARM.Completeness.consumption_preserves_completeness
