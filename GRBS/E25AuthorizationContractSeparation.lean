/-
  E25 — AUTHORIZATION COMPLETENESS DOES NOT GIVE CONTRACT COVERAGE

  (Rewritten on review. The first version placed a complete authorization and
  an uncovered contract in unrelated models, which any two notions admit; it
  did not separate these two.)

  One model: a request has the content it writes and the inputs it read. An
  intent pins content. A contract declares the allowed inputs; coverage (R8's
  ContractCoverage) means every input read was declared.

  Proved: a content-pinning intent is complete for "writes exactly the pinned
  content" (content_pin_complete); in the same model it is fitted by a request
  whose inputs are not covered (complete_yet_inputs_uncovered): completeness
  constrains what an action produces, not what it drew on. And when the
  boundary observes only the content, as DARM's does (the agent's reads happen
  before the proposal and never appear in it), no intent is complete for
  "right content and covered inputs" (input_coverage_not_enforceable), an
  instance of E24e's no_complete_intent_for_hidden_acceptance.

  NOT claimed: that inputs cannot be governed at all; making them observable
  (for example, by mediating reads) changes what the boundary sees, and E24e's
  characterization then applies to the enlarged observation.
-/
import E24eLineage
import E15CausalCoverageContractEquivalence

namespace DARM.E25

open DARM.Completeness (CompleteUnder)
open DARM.E24e (ObsBound no_complete_intent_for_hidden_acceptance)

/-- A request: the content it writes, and the inputs it read. -/
structure Req where
  content : String
  reads : List String
  deriving DecidableEq, Repr

/-- An intent pins content. -/
def fitsContent (c : String) (p : Req) : Prop := p.content = c

/-- The contract's declared inputs. -/
def declared : List String := ["/workspace/q3.csv"]

/-- Contract coverage (R8): every input the request read was declared. -/
def inputsCovered (p : Req) : Prop :=
  GRBS.R8RichContractSeparation.R8e.ContractCoverage (fun s => s ∈ declared) (fun s => s ∈ p.reads)

/-- A content-pinning intent is complete for writing exactly that content. -/
theorem content_pin_complete (c : String) :
    CompleteUnder (fun _ : Req => True) (fun p => p.content = c) fitsContent c :=
  fun _ hf _ => hf

/-- The separation, in one model: the complete intent is fitted by a request
    whose inputs are not covered. -/
theorem complete_yet_inputs_uncovered :
    CompleteUnder (fun _ : Req => True) (fun p => p.content = "Q3 summary") fitsContent "Q3 summary" ∧
    ∃ p : Req, fitsContent "Q3 summary" p ∧ ¬ inputsCovered p := by
  refine ⟨content_pin_complete _, ⟨"Q3 summary", ["/workspace/secret.txt"]⟩, rfl, ?_⟩
  intro h
  have := h "/workspace/secret.txt" (by simp)
  simp [declared] at this

/-- When the boundary observes only the content, no intent is complete for
    "right content and covered inputs" (E24e's impossibility, applied to inputs). -/
theorem input_coverage_not_enforceable (fits : String → Req → Prop)
    (hob : ObsBound fits Req.content) :
    ∀ i, fits i ⟨"Q3 summary", ["/workspace/q3.csv"]⟩ →
      ¬ CompleteUnder (fun _ => True)
          (fun p => p.content = "Q3 summary" ∧ inputsCovered p) fits i :=
  no_complete_intent_for_hidden_acceptance hob (q := ⟨"Q3 summary", ["/workspace/secret.txt"]⟩)
    rfl trivial (by
      intro ⟨_, h⟩
      have := h "/workspace/secret.txt" (by simp)
      simp [declared] at this)

end DARM.E25

#print axioms DARM.E25.content_pin_complete
#print axioms DARM.E25.complete_yet_inputs_uncovered
#print axioms DARM.E25.input_coverage_not_enforceable
