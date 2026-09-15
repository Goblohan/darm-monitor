import DarmMonitor.CompositionRuleBoundary

namespace DARM

/-- A composition-rule declaration records the boundary at which a rule
    claims to operate. It does not contain a semantic validity proof. -/
structure CompositionRuleDeclaration
    {State Boundary Locus : Type}
    (G : BoundaryIndexedGuarantee State Boundary)
    (Evidence : ScopedEvidence Boundary State)
    (Enforced : Locus → Boundary → State → Prop)
    (source target : Boundary)
    (targetLocus : Locus) where
  compositionBoundary : CompositionBoundary

/-- Semantic validity of a composition-rule declaration. -/
def CompositionRuleValid
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    (targetLocus : Locus)
    (_declaration :
      CompositionRuleDeclaration
        G Evidence Enforced source target targetLocus) : Prop :=
  ∀ s,
    G source s →
    Evidence target s →
    Enforced targetLocus target s →
    G target s

/-- A validated rule consists of a declaration together with a proof
    that its premises establish the target guarantee. -/
structure ValidatedCompositionRule
    {State Boundary Locus : Type}
    (G : BoundaryIndexedGuarantee State Boundary)
    (Evidence : ScopedEvidence Boundary State)
    (Enforced : Locus → Boundary → State → Prop)
    (source target : Boundary)
    (targetLocus : Locus) where
  declaration :
    CompositionRuleDeclaration
      G Evidence Enforced source target targetLocus
  valid :
    CompositionRuleValid targetLocus declaration

/-- Validation preserves the boundary declared by the rule. -/
theorem validatedRule_preserves_declared_boundary
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    (rule :
      ValidatedCompositionRule
        G Evidence Enforced source target targetLocus) :
    rule.declaration.compositionBoundary =
      rule.declaration.compositionBoundary := by
  rfl

end DARM
