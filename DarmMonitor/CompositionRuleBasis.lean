import DarmMonitor.CompositionRuleBoundaryAlignment

namespace DARM

def CompositionRuleBasis
    {State Boundary Locus : Type}
    (G : BoundaryIndexedGuarantee State Boundary)
    (Evidence : ScopedEvidence Boundary State)
    (Enforced : Locus → Boundary → State → Prop)
    (source target : Boundary)
    (targetLocus : Locus)
    (Basis : State → Prop) : Prop :=
  ∀ s,
    G source s →
    Evidence target s →
    Enforced targetLocus target s →
    Basis s →
    G target s

def SufficientCompositionRuleBasis
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    (source target : Boundary)
    (targetLocus : Locus)
    (Basis : State → Prop) : Prop :=
  CompositionRuleBasis
    G Evidence Enforced
    source target
    targetLocus Basis

theorem sufficientBasis_establishes_target
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    {Basis : State → Prop}
    (hBasis :
      SufficientCompositionRuleBasis
        (G := G)
        (Evidence := Evidence)
        (Enforced := Enforced)
        source target
        targetLocus
        Basis)
    (s : State)
    (hSource : G source s)
    (hEvidence : Evidence target s)
    (hEnforced : Enforced targetLocus target s)
    (hEstablished : Basis s) :
    G target s :=
  hBasis s hSource hEvidence hEnforced hEstablished

theorem sufficientBasis_implies_rule_valid
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    {Basis : State → Prop}
    (declaration :
      CompositionRuleDeclaration
        G Evidence Enforced source target targetLocus)
    (hBasis :
      SufficientCompositionRuleBasis
        (G := G)
        (Evidence := Evidence)
        (Enforced := Enforced)
        source target
        targetLocus
        Basis)
    (hEstablished : ∀ s, Basis s) :
    CompositionRuleValid
      targetLocus
      declaration := by
  intro s hSource hEvidence hEnforced
  exact hBasis s hSource hEvidence hEnforced (hEstablished s)

end DARM

