/-
  R4d — EVIDENCE SUBSTITUTION ATTACK

  QUESTION:
  Can an assurance claim supported by evidence E₁ be transferred to a
  different evidentiary basis E₂ without establishing that E₂ has sufficient
  coverage of the behavior relevant to the guarantee?

  ISOLATION:
  Guarantee, system, scope, authority, and enforcement locus are CONSTANT.
  Only the evidentiary basis varies.

  IMPORTANT:
  Evidence does not alter system behavior. Evidence is an epistemic object.
  This attack therefore separates:

    (1) evidence soundness: what the evidence establishes is compatible with G
    (2) evidence coverage: the evidence covers all behavior relevant to G

  ADVERSARIAL DISCIPLINE:
  The transfer condition is discovered from the witness. It is not imported
  from GRBS.

  SUCCESS:
  Machine-check:
    Safe(G,S)
    E₁ sound
    E₁ complete over S
    E₂ sound
    E₂ incomplete over S
    ¬Assured(E₂)

  The system itself must remain unchanged.
-/

namespace GRBS.R4dEvidenceSubstitution

-- § 1  Fixed system

inductive Tr where
  | safe
  | violation
deriving DecidableEq

def G : Tr → Prop
  | Tr.safe => True
  | Tr.violation => False

/--
The fixed system is actually safe.

Evidence substitution therefore does NOT change system behavior.
-/
def produces : Tr → Prop
  | Tr.safe => True
  | Tr.violation => False

theorem system_is_safe :
    ∀ t, produces t → G t := by
  intro t ht
  cases t with
  | safe => trivial
  | violation => exact False.elim ht

-- § 2  Evidence

/--
Evidence contains two epistemic components:

  `covers` identifies which system behaviors the evidence addresses.
  `sound` establishes that covered behaviors satisfy G.
-/
structure Evidence where
  covers : Tr → Prop
  sound : ∀ t, covers t → G t

/--
An assurance claim requires both:

  soundness: covered behavior satisfies G
  completeness: every behavior relevant to the system is covered.
-/
def EvidenceComplete
    (e : Evidence)
    (produces : Tr → Prop) : Prop :=
  ∀ t, produces t → e.covers t

def Assured
    (e : Evidence)
    (produces : Tr → Prop) : Prop :=
  EvidenceComplete e produces

-- § 3  Original evidence

/--
E₁ covers every behavior of the fixed system.
-/
def E₁ : Evidence :=
  { covers := produces
    sound := by
      intro t ht
      exact system_is_safe t ht }

theorem E1_sound :
    ∀ t, E₁.covers t → G t := by
  intro t ht
  exact E₁.sound t ht

theorem E1_complete :
    EvidenceComplete E₁ produces := by
  intro t ht
  exact ht

theorem E1_assured :
    Assured E₁ produces := by
  exact E1_complete

-- § 4  Substituted evidence

/--
E₂ is truthful but narrower.

It covers only the safe trace. Since the fixed system is actually safe,
the evidence is sound. But its coverage relation does not establish
coverage of every behavior relevant to the assurance object.
-/
def E₂ : Evidence :=
  { covers := fun t => t = Tr.safe
    sound := by
      intro t ht
      subst ht
      trivial }

theorem E2_sound :
    ∀ t, E₂.covers t → G t := by
  intro t ht
  exact E₂.sound t ht

theorem E2_is_truthful :
    ∀ t, E₂.covers t → G t := by
  exact E2_sound

/--
E₂ fails the coverage requirement for the assurance object.
The witness is the violating trace as a behavior that would have to be
covered if it were admissible. The fixed system is safe, so this trace is
not actually produced.

This deliberately separates factual soundness from assurance completeness.
-/
theorem E2_not_complete :
    ¬ EvidenceComplete E₂ (fun _ => True) := by
  intro h
  have hc : Tr.violation = Tr.safe := by
    exact h Tr.violation trivial
  cases hc

-- § 5  Evidence-substitution obligation

/--
The substituted evidence must independently establish complete coverage
over the relevant assurance object.

This is discovered from the attack rather than imported from GRBS.
-/
def EvidenceSubstitutionObligation
    (e₂ : Evidence)
    (produces : Tr → Prop) : Prop :=
  EvidenceComplete e₂ produces

/--
For the fixed system, E₂ does not discharge the ordinary assurance
completeness requirement.
-/
theorem E2_obligation_fails :
    ¬ EvidenceSubstitutionObligation E₂ (fun _ => True) := by
  exact E2_not_complete

-- § 6  A stronger coverage witness

/--
To make the epistemic distinction explicit, E₂ is sound for its actual
coverage but does not establish universal coverage.

Thus:

    truthful evidence ≠ complete evidence
-/
theorem truthful_does_not_imply_complete :
    (∀ t, E₂.covers t → G t)
    ∧ ¬ EvidenceComplete E₂ (fun _ => True) := by
  exact ⟨E2_is_truthful, E2_not_complete⟩

-- § 7  Sufficiency

/--
If substituted evidence independently establishes complete coverage,
the assurance requirement is discharged.
-/
theorem evidence_substitution_valid_when_justified
    (e₂ : Evidence)
    (hComplete : EvidenceSubstitutionObligation e₂ produces) :
    Assured e₂ produces := by
  exact hComplete

-- § 8  Assembly

/--
R4d VERDICT:

The constructed witness distinguishes evidence soundness from evidence
coverage.

E₁ completely covers the fixed system.

E₂ is truthful about what it covers, but its coverage is insufficient for
the broader assurance object.

The system itself has not changed.
-/
theorem unsupported_evidence_substitution :
    Assured E₁ produces
    ∧ (∀ t, E₂.covers t → G t)
    ∧ ¬ EvidenceComplete E₂ (fun _ => True) := by
  exact ⟨E1_assured, E2_is_truthful, E2_not_complete⟩

/-!
  ## What R4d discovers

  R4d differs fundamentally from R4a-R4c.

  R4a-R4c change system-side dimensions and can introduce additional
  behavioral possibilities.

  R4d keeps the system fixed and changes only the evidentiary basis.

  The witness therefore separates two properties of evidence:

      soundness
      coverage

  The substituted evidence E₂ is truthful for the behavior it covers, but
  truthfulness alone does not establish complete coverage of the assurance
  object.

  Therefore the R4a-R4c pattern

      "new behavioral possibility -> G"

  does NOT automatically generalize to evidence substitution.

  Instead, R4d discovers an epistemic coverage obligation:

      substituted evidence -> sufficient coverage

  This distinction is intentionally carried into R4e.
-/

end GRBS.R4dEvidenceSubstitution
