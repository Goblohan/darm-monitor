/-
  R4a — SCOPE EXPANSION ATTACK

  QUESTION: Can a valid assurance claim over a narrower scope be transferred
  to a broader scope without establishing the additional conditions?

  SUCCESS: Machine-check Safe(G,S1) ∧ S1 ⊂ S2 ∧ ¬Safe(G,S2), identify the
  exact missing step, show it sufficient when discharged, undischargeable
  in the concrete witness.

  FAILURE: If scope expansion necessarily preserves safety, the obligation
  adds no value — a result AGAINST the conservation hypothesis.
-/

namespace GRBS.R4aScopeExpansion

inductive Component where
  | compLocal   -- the original, well-analyzed component
  | compRemote  -- the additional component in the expanded scope
deriving DecidableEq

inductive Tr where
  | safe
  | violation
deriving DecidableEq

def G : Tr → Prop
  | Tr.safe => True
  | Tr.violation => False

def produces : Component → Tr → Prop
  | Component.compLocal, t => t = Tr.safe
  | Component.compRemote, _ => True

def S₁ : Component → Prop := fun c => c = Component.compLocal
def S₂ : Component → Prop := fun _ => True

def SafeOverScope
    (G : Tr → Prop) (scope : Component → Prop)
    (produces : Component → Tr → Prop) : Prop :=
  ∀ c : Component, scope c → ∀ t : Tr, produces c t → G t

-- § 4  Scope inclusion

theorem scope_included : ∀ c, S₁ c → S₂ c := by
  intro _ _; trivial

theorem scope_strict : ∃ c, S₂ c ∧ ¬ S₁ c :=
  ⟨Component.compRemote, trivial, fun h => Component.noConfusion h⟩

-- § 5  The counterexample

theorem safe_over_S1 : SafeOverScope G S₁ produces := by
  intro c hc t ht
  subst hc
  simp only [produces] at ht
  subst ht
  trivial

theorem not_safe_over_S2 : ¬ SafeOverScope G S₂ produces := by
  intro h
  exact h Component.compRemote trivial Tr.violation trivial

-- § 6  The scope-expansion obligation

def ScopeExpansionObligation
    (G : Tr → Prop) (S₁ S₂ : Component → Prop)
    (produces : Component → Tr → Prop) : Prop :=
  ∀ c : Component, S₂ c → ¬ S₁ c → ∀ t : Tr, produces c t → G t

-- § 7  Sufficiency

theorem scope_expansion_valid_when_justified
    (hS1 : SafeOverScope G S₁ produces)
    (hObl : ScopeExpansionObligation G S₁ S₂ produces)
    (_hInc : ∀ c, S₁ c → S₂ c) :
    SafeOverScope G S₂ produces := by
  intro c hc t ht
  cases c with
  | compLocal => exact hS1 Component.compLocal rfl t ht
  | compRemote => exact hObl Component.compRemote trivial (fun h => Component.noConfusion h) t ht

-- § 8  Not dischargeable

theorem obligation_not_dischargeable :
    ¬ ScopeExpansionObligation G S₁ S₂ produces := by
  intro h
  -- compRemote is in S₂, not in S₁, produces violation
  exact h Component.compRemote trivial (fun h => Component.noConfusion h) Tr.violation trivial

-- § 9  Assembly

theorem unsupported_scope_expansion :
    SafeOverScope G S₁ produces
    ∧ (∀ c, S₁ c → S₂ c)
    ∧ (∃ c, S₂ c ∧ ¬ S₁ c)
    ∧ ¬ SafeOverScope G S₂ produces
    ∧ ¬ ScopeExpansionObligation G S₁ S₂ produces :=
  ⟨safe_over_S1, scope_included, scope_strict,
   not_safe_over_S2, obligation_not_dischargeable⟩

end GRBS.R4aScopeExpansion
