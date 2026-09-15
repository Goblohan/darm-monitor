import DarmMonitor.BoundaryIndexedGuarantee

namespace DARM

inductive Boundary
  | localScope
  | systemScope
  deriving DecidableEq, Repr

structure State where
  localValue : Bool
  externalSafe : Bool
  deriving DecidableEq, Repr

def localRepresentation : State → Bool :=
  fun s => s.localValue

def localGuarantee : State → Prop :=
  fun s => s.localValue = true

def systemGuarantee : State → Prop :=
  fun s => s.localValue = true ∧ s.externalSafe = true

def scopedGuarantee :
    BoundaryIndexedGuarantee State Boundary :=
  fun b s =>
    match b with
    | Boundary.localScope => localGuarantee s
    | Boundary.systemScope => systemGuarantee s

theorem localRepresentation_adequate_localGuarantee :
    GuaranteeAdequate
      localRepresentation
      localGuarantee := by
  intro s₁ s₂ hRep
  unfold RepresentationEq localRepresentation at hRep
  simp [localGuarantee, hRep]

theorem localRepresentation_inadequate_systemGuarantee :
    ¬ GuaranteeAdequate
      localRepresentation
      systemGuarantee := by
  apply not_guaranteeAdequate_of_witness
    (s₁ := { localValue := true, externalSafe := true })
    (s₂ := { localValue := true, externalSafe := false })
  · rfl
  · simp [systemGuarantee]

theorem scopedGuarantee_local :
    scopedGuarantee Boundary.localScope = localGuarantee := by
  rfl

theorem scopedGuarantee_system :
    scopedGuarantee Boundary.systemScope = systemGuarantee := by
  rfl

theorem local_adequacy_does_not_imply_system_adequacy :
    GuaranteeAdequate
      localRepresentation
      localGuarantee ∧
    ¬ GuaranteeAdequate
      localRepresentation
      systemGuarantee := by
  constructor
  · exact localRepresentation_adequate_localGuarantee
  · exact localRepresentation_inadequate_systemGuarantee

end DARM

#print axioms DARM.localRepresentation_adequate_localGuarantee
#print axioms DARM.localRepresentation_inadequate_systemGuarantee
#print axioms DARM.scopedGuarantee_local
#print axioms DARM.scopedGuarantee_system
#print axioms DARM.local_adequacy_does_not_imply_system_adequacy
