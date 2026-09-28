/-
  E24e — LINEAGE, AND WHAT COMPLETENESS CAN REACH

  An intent constrains a proposal only through what the boundary observes.
  So completeness for a target proposal p0 is possible exactly when the
  acceptance judgment is determined by those observations on p0's admitted
  look-alikes (proposals the boundary cannot tell from p0).

  Proved, generically: necessity (a complete intent fitting p0 makes every
  admitted look-alike acceptable); sufficiency (an intent fitting exactly the
  look-alikes is complete when they are all acceptable); the characterization
  (a complete intent fitting p0 exists iff the admitted look-alikes are all
  acceptable, in a language that can express exact look-alike sets); and the
  impossibility (if two admitted look-alikes differ in acceptability, no intent
  fitting them is complete).

  At B3: pinning is complete for any path and content (generalizing E24d's
  witness); an intent whose content is a function the broker evaluates on a
  source it reads is complete: lineage with an observable derivation reduces to
  pinning, computed at the decision. Witness: acceptance that depends on how
  content was produced (invisible to the boundary) admits no complete intent.

  NOT claimed: that a source still holds its content after the decision; that
  any trusted component making a process observable is itself correct (that is
  an assumption to state, not a DARM guarantee).
-/
import CompletenessCalculus

namespace DARM.E24e

open DARM.Broker (Proposal)
open DARM.Completeness (CompleteUnder admitB3 fitsB)

section Observability

variable {A P O : Type}

/-- An intent language that sees proposals only through `obs`. -/
def ObsBound (fits : A → P → Prop) (obs : P → O) : Prop :=
  ∀ i p q, obs p = obs q → (fits i p ↔ fits i q)

/-- Necessity: a complete intent fitting p0 makes every admitted look-alike acceptable. -/
theorem complete_forces_fiber {fits : A → P → Prop} {obs : P → O} {admit acc : P → Prop}
    (hob : ObsBound fits obs) {i : A} {p0 : P} (hfit : fits i p0)
    (hc : CompleteUnder admit acc fits i) :
    ∀ p, obs p = obs p0 → admit p → acc p :=
  fun p hp ha => hc p ((hob i p p0 hp).mpr hfit) ha

/-- Sufficiency: an intent fitting exactly p0's look-alikes is complete when
    they are all acceptable. -/
theorem fiber_intent_complete {fits : A → P → Prop} {obs : P → O} {admit acc : P → Prop}
    {i : A} {p0 : P} (hex : ∀ p, fits i p ↔ obs p = obs p0)
    (hfib : ∀ p, obs p = obs p0 → admit p → acc p) :
    CompleteUnder admit acc fits i :=
  fun p hf ha => hfib p ((hex p).mp hf) ha

/-- Characterization: completeness is possible exactly when acceptance is
    determined by what the boundary observes. -/
theorem complete_intent_exists_iff {fits : A → P → Prop} {obs : P → O} {admit acc : P → Prop}
    (hob : ObsBound fits obs) (p0 : P) (i0 : A) (hex : ∀ p, fits i0 p ↔ obs p = obs p0) :
    (∃ i, fits i p0 ∧ CompleteUnder admit acc fits i) ↔
      (∀ p, obs p = obs p0 → admit p → acc p) := by
  constructor
  · intro ⟨i, hfit, hc⟩
    exact complete_forces_fiber hob hfit hc
  · intro hfib
    exact ⟨i0, (hex p0).mpr rfl, fiber_intent_complete hex hfib⟩

/-- Impossibility: two admitted look-alikes, one unacceptable, and no intent
    fitting the other is complete. -/
theorem no_complete_intent_for_hidden_acceptance {fits : A → P → Prop} {obs : P → O}
    {admit acc : P → Prop} (hob : ObsBound fits obs) {p q : P}
    (hsame : obs p = obs q) (hadm : admit q) (hbad : ¬ acc q) :
    ∀ i, fits i p → ¬ CompleteUnder admit acc fits i := by
  intro i hfit hc
  exact hbad (complete_forces_fiber hob hfit hc q hsame.symm hadm)

end Observability

/-! ## At B3: pinning in general, and lineage with an observable derivation -/

def pinned (x c : String) : DARM.E24b.Intent :=
  { tool := "write_file", constraints := [("path", x), ("content", c)] }

/-- Pinning is complete for any path and content (E24d proved one witness). -/
theorem pinned_complete_general (x c : String) :
    CompleteUnder (admitB3 DARM.Broker3.writeCfg) (DARM.E24d.WritesExactly x c) fitsB (pinned x c) := by
  intro p hfit hb
  obtain ⟨e, he⟩ := hb
  have hkeys := DARM.E24d.admitted_write_keys p e he
  unfold fitsB DARM.E24b.Intent.fits pinned at hfit
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_cons, List.all_nil, Bool.and_true] at hfit
  obtain ⟨htool, hpath, hcontent⟩ := hfit
  unfold DARM.E24b.constraintHolds at hpath hcontent
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, beq_iff_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at hpath hcontent
  obtain ⟨⟨ap, hap, hapk⟩, hpall⟩ := hpath
  obtain ⟨⟨ac, hac, hack⟩, hcall⟩ := hcontent
  refine ⟨htool.symm, ?_, ⟨ap, hap, hapk⟩, ⟨ac, hac, hack⟩⟩
  intro a ha
  rcases hkeys a ha with hk | hk
  · left; refine ⟨hk, ?_⟩
    rcases hpall a ha with h1 | h1
    · exact absurd hk h1
    · exact h1
  · right; refine ⟨hk, ?_⟩
    rcases hcall a ha with h1 | h1
    · exact absurd hk h1
    · exact h1

/-- Lineage with an observable derivation: the broker reads the source and
    evaluates the derivation at the decision, so the intent pins its result.
    Complete for "writes exactly f(source)", whatever the agent proposes. -/
def derived (x : String) (f : String → String) (source : String) : DARM.E24b.Intent :=
  pinned x (f source)

theorem derived_complete (x : String) (f : String → String) (source : String) :
    CompleteUnder (admitB3 DARM.Broker3.writeCfg) (DARM.E24d.WritesExactly x (f source))
      fitsB (derived x f source) :=
  pinned_complete_general x (f source)

/-! ## Witness: acceptance that depends on an unobserved process -/

/-- A proposal as (content, whether it was produced faithfully); the boundary
    observes only the content. -/
abbrev Produced := String × Bool

theorem hidden_process_admits_no_complete_intent (fits : List String → Produced → Prop)
    (hob : ObsBound fits Prod.fst) :
    ∀ i, fits i ("summary", true) →
      ¬ CompleteUnder (fun _ => True) (fun p : Produced => p.2 = true) fits i :=
  no_complete_intent_for_hidden_acceptance hob (q := ("summary", false)) rfl trivial (by simp)

end DARM.E24e

#print axioms DARM.E24e.complete_intent_exists_iff
#print axioms DARM.E24e.no_complete_intent_for_hidden_acceptance
#print axioms DARM.E24e.pinned_complete_general
#print axioms DARM.E24e.derived_complete
#print axioms DARM.E24e.hidden_process_admits_no_complete_intent
