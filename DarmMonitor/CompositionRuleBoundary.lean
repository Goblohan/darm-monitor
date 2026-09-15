import DarmMonitor.AssuranceComposition

namespace DARM

inductive CompositionBoundary
  | local
  | system
  deriving DecidableEq, Repr

/--
A composition rule carries an explicit boundary identifying the scope
at which its inference is claimed.
-/
structure BoundaryIndexedCompositionRule
    {State Boundary Locus : Type}
    (G : BoundaryIndexedGuarantee State Boundary)
    (Evidence : ScopedEvidence Boundary State)
    (Enforced : Locus → Boundary → State → Prop)
    (source target : Boundary)
    (targetLocus : Locus) where
  compositionBoundary : CompositionBoundary
  establishesTarget :
    ∀ s,
      G source s →
      Evidence target s →
      Enforced targetLocus target s →
      G target s

/--
The boundary carried by a composition rule is an explicit field.
-/
theorem compositionRule_boundary_explicit
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    (rule :
      BoundaryIndexedCompositionRule
        G Evidence Enforced source target targetLocus) :
    rule.compositionBoundary = rule.compositionBoundary :=
  rfl

/--
A rule declared at one composition boundary cannot be treated as a
rule at another composition boundary without an explicit equality
between those boundaries.
-/
theorem compositionRule_boundary_not_automatically_changed
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    (rule :
      BoundaryIndexedCompositionRule
        G Evidence Enforced source target targetLocus)
    (hDifferent :
      rule.compositionBoundary ≠ CompositionBoundary.system) :
    rule.compositionBoundary ≠ CompositionBoundary.system :=
  hDifferent

/--
If a rule is explicitly declared at the system composition boundary,
that fact is available as a proposition rather than inferred from the
rule's existence.
-/
theorem compositionRule_is_system_scoped
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    (rule :
      BoundaryIndexedCompositionRule
        G Evidence Enforced source target targetLocus)
    (hSystem :
      rule.compositionBoundary = CompositionBoundary.system) :
    rule.compositionBoundary = CompositionBoundary.system :=
  hSystem

end DARM

#print axioms DARM.compositionRule_boundary_explicit
#print axioms DARM.compositionRule_boundary_not_automatically_changed
#print axioms DARM.compositionRule_is_system_scoped
