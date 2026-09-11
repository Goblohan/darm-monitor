/-
  R4b — AUTHORITY SUBSTITUTION ATTACK

  QUESTION: Can an assurance claim whose enforcement authority is A₁ be
  transferred to a system where the enforcement authority is A₂, without
  discharging an authority-substitution obligation?

  ISOLATION: Scope is held CONSTANT (one component, unchanged). Only the
  enforcement authority varies. This structurally prevents conflation with
  R4a (scope expansion).

  SUCCESS: Machine-check Safe(G,A₁) ∧ A₁ ≠ A₂ ∧ ¬Safe(G,A₂), identify
  the exact missing step, show it sufficient when discharged, show it
  undischargeable in the concrete witness.

  FAILURE: If authority substitution necessarily preserves safety, the
  obligation adds no value — a result against the conservation hypothesis.

  ADVERSARIAL DISCIPLINE: The attack tries to make transfer SUCCEED.
  Definitions are not rigged. The obligation is discovered, not imported.
-/

namespace GRBS.R4bAuthoritySubstitution

-- § 1  Minimal carriers

inductive Tr where
  | safe
  | violation
deriving DecidableEq

def G : Tr → Prop
  | Tr.safe => True
  | Tr.violation => False

/-- Enforcement authority: the mechanism that controls which traces the
    system can produce. `enforcing` mediates access and prevents violations.
    `permissive` does not mediate — all traces are possible. -/
inductive Auth where
  | enforcing   -- reference monitor / mediation active
  | permissive  -- enforcement removed or substituted with weaker mechanism
deriving DecidableEq

/-- What traces are possible under each authority. Under `enforcing`, only
    safe traces are producible. Under `permissive`, any trace is possible.
    This is not rigged: it represents the operational difference between
    an enforcing and a non-enforcing mechanism. -/
def tracesUnder : Auth → Tr → Prop
  | Auth.enforcing, t => t = Tr.safe
  | Auth.permissive, _ => True

-- § 2  Safety under an authority

def SafeUnderAuthority
    (G : Tr → Prop) (auth : Auth)
    (tracesUnder : Auth → Tr → Prop) : Prop :=
  ∀ t : Tr, tracesUnder auth t → G t

-- § 3  The counterexample

theorem safe_under_enforcing :
    SafeUnderAuthority G Auth.enforcing tracesUnder := by
  intro t ht
  simp only [tracesUnder] at ht
  subst ht; trivial

theorem not_safe_under_permissive :
    ¬ SafeUnderAuthority G Auth.permissive tracesUnder := by
  intro h
  exact h Tr.violation trivial

theorem authority_differs : Auth.enforcing ≠ Auth.permissive := by
  intro h; exact Auth.noConfusion h

-- § 4  The authority-substitution obligation — discovered from the attack

/-- Every trace that becomes possible under A₂ but was NOT possible under A₁
    must independently satisfy G. This is the explicit transfer condition
    for authority substitution.

    Note: NOT a GRBS predicate. Discovered from the attack. -/
def AuthSubstitutionObligation
    (G : Tr → Prop) (auth₁ auth₂ : Auth)
    (tracesUnder : Auth → Tr → Prop) : Prop :=
  ∀ t : Tr, tracesUnder auth₂ t → ¬ tracesUnder auth₁ t → G t

-- § 5  Sufficiency

theorem authority_substitution_valid_when_justified
    (hA1 : SafeUnderAuthority G Auth.enforcing tracesUnder)
    (hObl : AuthSubstitutionObligation G Auth.enforcing Auth.permissive tracesUnder) :
    SafeUnderAuthority G Auth.permissive tracesUnder := by
  intro t ht
  cases t with
  | safe => exact hA1 Tr.safe rfl
  | violation => exact hObl Tr.violation trivial (fun h => Tr.noConfusion h)

-- § 6  Not dischargeable

theorem obligation_not_dischargeable :
    ¬ AuthSubstitutionObligation G Auth.enforcing Auth.permissive tracesUnder := by
  intro h
  exact h Tr.violation trivial (fun h => Tr.noConfusion h)

-- § 7  Assembly

/-- **R4b VERDICT: Unsupported authority substitution.**

    In the constructed witness, a valid assurance claim under an enforcing authority cannot be transferred
    to a permissive authority without discharging the authority-substitution
    obligation. The scope is held constant — only the enforcement mechanism
    varies. The five conjuncts:

    (1) Safe(G, enforcing) holds — the original claim is valid.
    (2) enforcing ≠ permissive — authority genuinely changed.
    (3) ¬Safe(G, permissive) — the claim fails under the new authority.
    (4) The obligation is sufficient — when discharged, transfer is valid.
    (5) The obligation is not dischargeable — the new traces admitted by
        the permissive authority include violations. -/
theorem unsupported_authority_substitution :
    SafeUnderAuthority G Auth.enforcing tracesUnder
    ∧ Auth.enforcing ≠ Auth.permissive
    ∧ ¬ SafeUnderAuthority G Auth.permissive tracesUnder
    ∧ ¬ AuthSubstitutionObligation G Auth.enforcing Auth.permissive tracesUnder :=
  ⟨safe_under_enforcing, authority_differs,
   not_safe_under_permissive, obligation_not_dischargeable⟩

/-!
  ## What R4b discovers

  In the constructed witness, authority substitution is not safety-preserving: a guarantee valid under
  an enforcing authority can fail under a permissive authority, even when
  the scope is constant.

  The `AuthSubstitutionObligation` has the form:
      ∀ t, tracesUnder(A₂, t) → ¬tracesUnder(A₁, t) → G t
  i.e., every NEW behavioral possibility must satisfy G.

  Compare R4a's `ScopeExpansionObligation`:
      ∀ c ∈ S₂ \ S₁, ∀ t, produces(c, t) → G t
  i.e., every NEW component's traces must satisfy G.

  Both: every new element introduced by an expansion must independently
  satisfy the guarantee. The common pattern is emerging but NOT yet
  asserted as a theorem — R4c–R4e determine whether it generalizes.
-/

end GRBS.R4bAuthoritySubstitution
