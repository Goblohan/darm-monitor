import DarmMonitor.CompositionRuleBasis

namespace DARM

def BasisEstablishment
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    (Basis : State → Prop) : Prop :=
  ∀ s,
    G source s →
    Evidence target s →
    Enforced targetLocus target s →
    Basis s

def BasisTargetAdequacy
    {State Boundary : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    (target : Boundary)
    (Basis : State → Prop) : Prop :=
  ∀ s,
    Basis s →
    G target s

def FactorizedCompositionBasis
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    (Basis : State → Prop) : Prop :=
  BasisEstablishment
    (G := G)
    (Evidence := Evidence)
    (Enforced := Enforced)
    (source := source)
    (target := target)
    (targetLocus := targetLocus)
    Basis ∧
  BasisTargetAdequacy
    (G := G)
    target
    Basis

theorem factorizedBasis_implies_compositionBasis
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    {Basis : State → Prop}
    (hFactorized :
      FactorizedCompositionBasis
        (G := G)
        (Evidence := Evidence)
        (Enforced := Enforced)
        (source := source)
        (target := target)
        (targetLocus := targetLocus)
        Basis) :
    CompositionRuleBasis
      G Evidence Enforced
      source target
      targetLocus Basis := by
  intro s hSource hEvidence hEnforced hBasis
  exact hFactorized.2 s hBasis

theorem factorizedBasis_establishes_target
    {State Boundary Locus : Type}
    {G : BoundaryIndexedGuarantee State Boundary}
    {Evidence : ScopedEvidence Boundary State}
    {Enforced : Locus → Boundary → State → Prop}
    {source target : Boundary}
    {targetLocus : Locus}
    {Basis : State → Prop}
    (hFactorized :
      FactorizedCompositionBasis
        (G := G)
        (Evidence := Evidence)
        (Enforced := Enforced)
        (source := source)
        (target := target)
        (targetLocus := targetLocus)
        Basis)
    (s : State)
    (hSource : G source s)
    (hEvidence : Evidence target s)
    (hEnforced : Enforced targetLocus target s) :
    G target s := by
  have hBasis :=
    hFactorized.1 s hSource hEvidence hEnforced
  exact hFactorized.2 s hBasis

end DARM

#print axioms DARM.factorizedBasis_implies_compositionBasis
#print axioms DARM.factorizedBasis_establishes_target
