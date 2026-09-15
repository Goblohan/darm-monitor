import DarmMonitor.CompositionRuleValidity
import DarmMonitor.CompositionRuleValidityNegative

namespace DARM

/-- The boundary at which a composition rule is being evaluated. -/
def EvaluationBoundary :=
  CompositionBoundary

/-- A composition-rule declaration is aligned with an evaluation boundary
    when its declared boundary agrees with the boundary being evaluated. -/
def CompositionRuleBoundaryAligned
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    (declaration :
      CompositionRuleDeclaration
        G Evidence Enforced source target targetLocus)
    (evaluationBoundary : EvaluationBoundary) : Prop :=
  declaration.compositionBoundary = evaluationBoundary

/-- Boundary alignment is reflexive. -/
theorem compositionRuleBoundaryAligned_refl
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    (declaration :
      CompositionRuleDeclaration
        G Evidence Enforced source target targetLocus) :
    CompositionRuleBoundaryAligned
      declaration
      declaration.compositionBoundary := by
  rfl

/-- A system declaration is aligned with system evaluation exactly when
    its declared boundary is system. -/
theorem systemBoundary_alignment_iff
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    (declaration :
      CompositionRuleDeclaration
        G Evidence Enforced source target targetLocus) :
    CompositionRuleBoundaryAligned
        declaration
        CompositionBoundary.system ↔
      declaration.compositionBoundary =
        CompositionBoundary.system := by
  rfl

/-- The concrete system-declared rule is aligned with system evaluation. -/
theorem systemDeclaredRule_is_boundary_aligned :
    CompositionRuleBoundaryAligned
      systemDeclaredRule
      CompositionBoundary.system := by
  rfl

/-- Boundary alignment does not guarantee semantic validity. -/
theorem aligned_system_declaration_can_still_be_invalid :
    CompositionRuleBoundaryAligned
        systemDeclaredRule
        CompositionBoundary.system ∧
    ¬ CompositionRuleValid
        ValidityNegativeLocus.systemEnforcer
        systemDeclaredRule := by
  constructor
  · exact systemDeclaredRule_is_boundary_aligned
  · exact systemDeclaredRule_is_invalid

end DARM

