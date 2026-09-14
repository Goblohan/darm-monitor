/-
  R4d — EVIDENCE COVERAGE ATTACK

  QUESTION:

  Can a truthful evidentiary basis be insufficient for assurance because its
  coverage does not span the execution domain quantified by the claim?

  ISOLATION:

    Guarantee       CONSTANT
    System          CONSTANT
    Scope           CONSTANT
    Authority       CONSTANT
    Enforcement     CONSTANT
    Evidence        CHANGES

  Unlike R4a-R4c, this attack does not substitute a system-side structural
  dimension. It attacks the epistemic basis of the assurance claim.

  The witness contains multiple distinct safe executions.

    safeA
    safeB

  The fixed system can produce both.

  E₁ covers both executions.

  E₂ covers only safeA.

  E₂ is truthful:
      every execution it covers satisfies G.

  E₂ is nevertheless incomplete:
      safeB is relevant to the assurance claim but is outside its coverage.

  Therefore:

      evidence soundness
          ≠
      evidence completeness

  This artifact does NOT claim that evidence coverage is novel in itself.
  It tests whether evidence substitution constitutes an independent
  assurance-transfer failure mode.
-/

namespace GRBS.R4dEvidenceCoverage

-- § 1  Execution space

inductive Tr where
  | safeA
  | safeB
  | violation
deriving DecidableEq

/--
The assurance guarantee.

Both relevant system executions are safe.
The violating trace is not.
-/
def G : Tr → Prop
  | Tr.safeA => True
  | Tr.safeB => True
  | Tr.violation => False

/--
Fixed system execution domain.

The system has two distinct relevant executions.
The violating execution is not produced by the fixed system.
-/
def produces : Tr → Prop
  | Tr.safeA => True
  | Tr.safeB => True
  | Tr.violation => False

/--
The fixed system satisfies the guarantee over its execution domain.
-/
theorem system_is_safe :
    ∀ t, produces t → G t := by
  intro t ht
  cases t with
  | safeA => trivial
  | safeB => trivial
  | violation => exact False.elim ht

-- § 2  Evidence

/--
Evidence consists of:

  `observes` — executions directly represented by the evidence
  `covers`   — executions for which the evidence is claimed to establish
               assurance

Soundness means the evidence never establishes G for a covered execution
that violates G.

Coverage is a separate property.
-/
structure Evidence where
  observes : Tr → Prop
  covers : Tr → Prop
  sound : ∀ t, covers t → G t

/--
Evidence is complete when every execution produced by the fixed system
lies inside its evidentiary coverage.
-/
def EvidenceComplete
    (e : Evidence)
    (produces : Tr → Prop) : Prop :=
  ∀ t, produces t → e.covers t

/--
Assurance requires complete coverage of the system execution domain.

Soundness remains part of the Evidence structure itself.
-/
def Assured
    (e : Evidence)
    (produces : Tr → Prop) : Prop :=
  EvidenceComplete e produces

-- § 3  Original evidence E₁

/--
E₁ covers every execution of the fixed system.
-/
def E₁ : Evidence :=
  { observes := produces
    covers := produces
    sound := by
      intro t ht
      exact system_is_safe t ht }

/--
E₁ is truthful about everything it covers.
-/
theorem E1_sound :
    ∀ t, E₁.covers t → G t := by
  intro t ht
  exact E₁.sound t ht

/--
E₁ covers the complete fixed-system execution domain.
-/
theorem E1_complete :
    EvidenceComplete E₁ produces := by
  intro t ht
  exact ht

/--
E₁ therefore supports the assurance claim.
-/
theorem E1_assured :
    Assured E₁ produces := by
  exact E1_complete

-- § 4  Substituted evidence E₂

/--
E₂ observes and covers only safeA.

It is completely truthful about what it covers.

It does not make any false statement about safeB or violation.
It simply lacks coverage of safeB.
-/
def E₂ : Evidence :=
  { observes := fun t => t = Tr.safeA
    covers := fun t => t = Tr.safeA
    sound := by
      intro t ht
      subst ht
      trivial }

/--
E₂ is sound for everything it covers.
-/
theorem E2_sound :
    ∀ t, E₂.covers t → G t := by
  intro t ht
  exact E₂.sound t ht

/--
E₂ is truthful about its observations.
-/
theorem E2_truthful :
    ∀ t, E₂.observes t → G t := by
  intro t ht
  exact E2_sound t ht

/--
E₂ fails completeness because safeB is genuinely produced by the fixed
system but is absent from E₂'s coverage relation.
-/
theorem E2_not_complete :
    ¬ EvidenceComplete E₂ produces := by
  intro h
  have hc : E₂.covers Tr.safeB := h Tr.safeB trivial
  have heq : Tr.safeB = Tr.safeA := by
    exact hc
  cases heq

/--
The substituted evidence remains sound even though it is incomplete.
-/
theorem E2_sound_but_incomplete :
    (∀ t, E₂.covers t → G t)
    ∧ ¬ EvidenceComplete E₂ produces := by
  exact ⟨E2_sound, E2_not_complete⟩

-- § 5  Evidence-substitution obligation

/--
A substituted evidentiary basis must establish complete coverage of the
execution domain quantified by the assurance claim.
-/
def EvidenceSubstitutionObligation
    (e₂ : Evidence)
    (produces : Tr → Prop) : Prop :=
  EvidenceComplete e₂ produces

/--
E₂ cannot discharge the evidence-substitution obligation.
-/
theorem E2_obligation_fails :
    ¬ EvidenceSubstitutionObligation E₂ produces := by
  exact E2_not_complete

/--
If substituted evidence independently establishes complete coverage,
the assurance requirement is discharged.
-/
theorem evidence_substitution_valid_when_justified
    (e₂ : Evidence)
    (hComplete : EvidenceSubstitutionObligation e₂ produces) :
    Assured e₂ produces := by
  exact hComplete

-- § 6  The actual substitution attack

/--
R4d witness:

  E₁ supports the fixed-system assurance claim.

  E₂ is truthful about every observation it makes.

  E₂ nevertheless cannot support the same system-level assurance claim
  because safeB is a produced execution outside its evidentiary coverage.

  No system-side dimension has changed.
-/
theorem unsupported_evidence_substitution :
    Assured E₁ produces
    ∧ (∀ t, E₂.observes t → G t)
    ∧ ¬ Assured E₂ produces := by
  exact ⟨E1_assured, E2_truthful, E2_not_complete⟩

/--
The failure is specifically a coverage failure, not a truthfulness failure.

E₂ does not contain a false observation.
Its failure is that it does not cover the entire execution domain.
-/
theorem evidence_failure_is_coverage_not_falsehood :
    (∀ t, E₂.observes t → G t)
    ∧ ¬ EvidenceComplete E₂ produces := by
  exact ⟨E2_truthful, E2_not_complete⟩

/-!
  ## R4d discovery

  R4a-R4c attack system-side substitutions:

      scope
      authority
      enforcement locus

  R4d holds those dimensions fixed and changes only the evidentiary basis.

  The witness demonstrates:

      truthful evidence
          does not imply
      complete evidentiary coverage.

  The relevant assurance-transfer obligation is therefore:

      substituted evidence
          -> sufficient coverage of the execution domain

  R4d does not establish that this obligation is novel in the literature.
  It establishes a machine-checked witness for treating evidentiary
  coverage as an explicit dimension of assurance transfer.
-/

end GRBS.R4dEvidenceCoverage
