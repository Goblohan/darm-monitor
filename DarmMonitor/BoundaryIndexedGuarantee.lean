import DarmMonitor.GuaranteeAdequacy

namespace DARM

def BoundaryIndexedGuarantee
    (State Boundary : Type) :=
  Boundary → State → Prop

def BoundaryRepresentationEq
    {State Representation : Type}
    (ρ : State → Representation)
    (s₁ s₂ : State) : Prop :=
  ρ s₁ = ρ s₂

def BoundaryGuaranteeAdequate
    {State Representation Boundary : Type}
    (ρ : State → Representation)
    (G : BoundaryIndexedGuarantee State Boundary) : Prop :=
  ∀ b s₁ s₂,
    BoundaryRepresentationEq ρ s₁ s₂ →
    (G b s₁ ↔ G b s₂)

theorem boundaryGuaranteeAdequate_iff
    {State Representation Boundary : Type}
    {ρ : State → Representation}
    {G : BoundaryIndexedGuarantee State Boundary} :
    BoundaryGuaranteeAdequate ρ G ↔
      ∀ b s₁ s₂,
        ρ s₁ = ρ s₂ →
        (G b s₁ ↔ G b s₂) := by
  rfl

theorem boundaryGuaranteeAdequate_at
    {State Representation Boundary : Type}
    {ρ : State → Representation}
    {G : BoundaryIndexedGuarantee State Boundary}
    (hAdequate : BoundaryGuaranteeAdequate ρ G)
    (b : Boundary) :
    GuaranteeAdequate ρ (G b) := by
  intro s₁ s₂ hRep
  exact hAdequate b s₁ s₂ hRep

theorem not_boundaryGuaranteeAdequate_of_witness
    {State Representation Boundary : Type}
    {ρ : State → Representation}
    {G : BoundaryIndexedGuarantee State Boundary}
    (b : Boundary)
    (s₁ s₂ : State)
    (hRep : BoundaryRepresentationEq ρ s₁ s₂)
    (hDisagree : ¬ (G b s₁ ↔ G b s₂)) :
    ¬ BoundaryGuaranteeAdequate ρ G := by
  intro hAdequate
  exact hDisagree (hAdequate b s₁ s₂ hRep)

end DARM

#print axioms DARM.boundaryGuaranteeAdequate_iff
#print axioms DARM.boundaryGuaranteeAdequate_at
#print axioms DARM.not_boundaryGuaranteeAdequate_of_witness
