/-
  R4c — LOCUS SUBSTITUTION ATTACK

  QUESTION: Can an assurance claim whose enforcement locus controls the
  relevant transition be transferred to a locus that merely observes it,
  without discharging a locus-substitution obligation?

  ISOLATION: Scope and authority are held CONSTANT. Only the enforcement
  locus varies. This structurally prevents conflation with R4a (scope)
  and R4b (authority).

  SUCCESS: Machine-check Safe(G,L₁) ∧ L₁ ≠ L₂ ∧ ¬Safe(G,L₂), identify
  the missing step, show it sufficient when discharged, show it
  undischargeable in the concrete witness.

  FAILURE: If locus substitution necessarily preserves safety, the
  obligation adds no value — a result against the conservation hypothesis.

  ADVERSARIAL DISCIPLINE: The attack tries to make transfer SUCCEED.
  Definitions are not rigged. The obligation is discovered, not imported.
-/

namespace GRBS.R4cLocusSubstitution

-- § 1  Minimal carriers

inductive Tr where
  | safe
  | violation
deriving DecidableEq

def G : Tr → Prop
  | Tr.safe => True
  | Tr.violation => False

/-- Enforcement locus: WHERE enforcement happens.
    `mediating` — the locus interposes on the transition and can block violations.
    `observing` — the locus can see the transition but cannot block it. -/
inductive Locus where
  | mediating  -- interposes: can prevent violating traces
  | observing  -- watches only: all traces pass through
deriving DecidableEq

/-- What traces are possible at each locus. At a mediating locus, only safe
    traces are producible (violations are blocked). At an observing locus,
    all traces pass through — including violations.
    Authority is the SAME in both: the difference is whether the locus can
    actually interpose on the transition. -/
def tracesAtLocus : Locus → Tr → Prop
  | Locus.mediating, t => t = Tr.safe
  | Locus.observing, _ => True

-- § 2  Safety at a locus

def SafeAtLocus
    (G : Tr → Prop) (l : Locus)
    (tracesAtLocus : Locus → Tr → Prop) : Prop :=
  ∀ t : Tr, tracesAtLocus l t → G t

-- § 3  The counterexample

theorem safe_at_mediating :
    SafeAtLocus G Locus.mediating tracesAtLocus := by
  intro t ht
  simp only [tracesAtLocus] at ht
  subst ht; trivial

theorem not_safe_at_observing :
    ¬ SafeAtLocus G Locus.observing tracesAtLocus := by
  intro h
  exact h Tr.violation trivial

theorem locus_differs : Locus.mediating ≠ Locus.observing := by
  intro h; exact Locus.noConfusion h

-- § 4  The locus-substitution obligation — discovered from the attack

/-- Every trace that becomes possible at L₂ but was NOT possible at L₁
    must independently satisfy G. This is the explicit transfer condition
    for locus substitution.

    Note: NOT a GRBS predicate. Discovered from the attack. -/
def LocusSubstitutionObligation
    (G : Tr → Prop) (l₁ l₂ : Locus)
    (tracesAtLocus : Locus → Tr → Prop) : Prop :=
  ∀ t : Tr, tracesAtLocus l₂ t → ¬ tracesAtLocus l₁ t → G t

-- § 5  Sufficiency

theorem locus_substitution_valid_when_justified
    (hL1 : SafeAtLocus G Locus.mediating tracesAtLocus)
    (hObl : LocusSubstitutionObligation G Locus.mediating Locus.observing tracesAtLocus) :
    SafeAtLocus G Locus.observing tracesAtLocus := by
  intro t ht
  cases t with
  | safe => exact hL1 Tr.safe rfl
  | violation => exact hObl Tr.violation trivial (fun h => Tr.noConfusion h)

-- § 6  Not dischargeable

theorem obligation_not_dischargeable :
    ¬ LocusSubstitutionObligation G Locus.mediating Locus.observing tracesAtLocus := by
  intro h
  exact h Tr.violation trivial (fun h => Tr.noConfusion h)

-- § 7  Assembly

/-- **R4c VERDICT: Unsupported locus substitution.**

    In the constructed witness, a valid assurance claim at a mediating locus
    cannot be transferred to an observing locus without discharging the
    locus-substitution obligation. Scope and authority are held constant —
    only the enforcement locus varies.

    (1) Safe(G, mediating) holds.
    (2) mediating ≠ observing.
    (3) ¬Safe(G, observing).
    (4) The obligation is sufficient when discharged.
    (5) The obligation is not dischargeable in this witness. -/
theorem unsupported_locus_substitution :
    SafeAtLocus G Locus.mediating tracesAtLocus
    ∧ Locus.mediating ≠ Locus.observing
    ∧ ¬ SafeAtLocus G Locus.observing tracesAtLocus
    ∧ ¬ LocusSubstitutionObligation G Locus.mediating Locus.observing tracesAtLocus :=
  ⟨safe_at_mediating, locus_differs,
   not_safe_at_observing, obligation_not_dischargeable⟩

/-!
  ## What R4c discovers

  In the constructed witness, locus substitution is not safety-preserving:
  a guarantee valid at a mediating locus can fail at an observing locus,
  even when scope and authority are constant.

  The `LocusSubstitutionObligation` has the form:
      ∀ t, tracesAtLocus(L₂, t) → ¬tracesAtLocus(L₁, t) → G t
  i.e., every NEW behavioral possibility must satisfy G.

  Three independently derived obligations now share the same pattern:

  | Attack | What changes | Obligation form                              |
  |--------|-------------|----------------------------------------------|
  | R4a    | Scope       | ∀ new component traces → G                   |
  | R4b    | Authority   | ∀ newly admitted traces → G                  |
  | R4c    | Locus       | ∀ newly passable traces → G                  |

  All three: every new behavioral possibility introduced by the transition
  must independently satisfy the guarantee. The common pattern is now
  three-for-three but NOT yet asserted as a theorem — R4d (evidence) and
  R4e (composition) determine whether it generalizes or breaks.
-/

end GRBS.R4cLocusSubstitution
