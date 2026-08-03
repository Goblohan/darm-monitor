import DarmMonitor.Basic
import DarmMonitor.BoundaryMargin
import DarmMonitor.StratumComposition

namespace DARM.SemanticQuotient

open DARM.Boundary
open DARM.Composition

/-- Semantic equivalence of discrete states.
    This deliberately identifies states by their observable policy,
    rather than by raw structural equality. -/
def SemanticallyEquivalent
    {CapId : Type} [DecidableEq CapId]
    (s₁ s₂ : State CapId (Fin n)) : Prop :=
  s₁.policy = s₂.policy

theorem semanticallyEquivalent_refl
    {CapId : Type} [DecidableEq CapId]
    (s : State CapId (Fin n)) :
    SemanticallyEquivalent s s := by
  rfl

theorem semanticallyEquivalent_symm
    {CapId : Type} [DecidableEq CapId]
    {s₁ s₂ : State CapId (Fin n)}
    (h : SemanticallyEquivalent s₁ s₂) :
    SemanticallyEquivalent s₂ s₁ := by
  exact h.symm

theorem semanticallyEquivalent_trans
    {CapId : Type} [DecidableEq CapId]
    {s₁ s₂ s₃ : State CapId (Fin n)}
    (h₁ : SemanticallyEquivalent s₁ s₂)
    (h₂ : SemanticallyEquivalent s₂ s₃) :
    SemanticallyEquivalent s₁ s₃ := by
  exact h₁.trans h₂

end DARM.SemanticQuotient

#print axioms DARM.SemanticQuotient.semanticallyEquivalent_refl
#print axioms DARM.SemanticQuotient.semanticallyEquivalent_symm
#print axioms DARM.SemanticQuotient.semanticallyEquivalent_trans
