import DarmMonitor.CompositionRuleBasisFactorization

namespace DARM

structure FactorNegativeState where
  localSafe : Bool
  systemSafe : Bool

inductive FactorNegativeBoundary
  | source
  | systemTarget

inductive FactorNegativeLocus
  | systemEnforcer

def factorNegativeGuarantee :
    BoundaryIndexedGuarantee
      FactorNegativeState
      FactorNegativeBoundary :=
  fun boundary state =>
    match boundary with
    | FactorNegativeBoundary.source =>
        state.localSafe = true
    | FactorNegativeBoundary.systemTarget =>
        state.systemSafe = true

def factorNegativeEvidence :
    ScopedEvidence
      FactorNegativeBoundary
      FactorNegativeState :=
  fun boundary state =>
    match boundary with
    | FactorNegativeBoundary.source =>
        state.localSafe = true
    | FactorNegativeBoundary.systemTarget =>
        state.localSafe = true

def factorNegativeEnforced :
    FactorNegativeLocus →
      FactorNegativeBoundary →
      FactorNegativeState →
      Prop :=
  fun locus boundary state =>
    match locus, boundary with
    | FactorNegativeLocus.systemEnforcer,
      FactorNegativeBoundary.systemTarget =>
        state.localSafe = true
    | _, _ =>
        False

def factorNegativeBasis :
    FactorNegativeState → Prop :=
  fun state =>
    state.localSafe = true

def factorNegativeState : FactorNegativeState :=
  { localSafe := true
    systemSafe := false }

theorem factorNegative_basisEstablishment :
    BasisEstablishment
      (G := factorNegativeGuarantee)
      (Evidence := factorNegativeEvidence)
      (Enforced := factorNegativeEnforced)
      (source := FactorNegativeBoundary.source)
      (target := FactorNegativeBoundary.systemTarget)
      (targetLocus := FactorNegativeLocus.systemEnforcer)
      factorNegativeBasis := by
  intro s hSource hEvidence hEnforced
  exact hSource

theorem factorNegative_basis_holds :
    factorNegativeBasis factorNegativeState := by
  rfl

theorem factorNegative_target_fails :
    ¬ factorNegativeGuarantee
      FactorNegativeBoundary.systemTarget
      factorNegativeState := by
  intro h
  cases h

theorem factorNegative_basisTargetAdequacy_fails :
    ¬ BasisTargetAdequacy
      (G := factorNegativeGuarantee)
      FactorNegativeBoundary.systemTarget
      factorNegativeBasis := by
  intro hAdequacy
  exact factorNegative_target_fails
    (hAdequacy factorNegativeState
      factorNegative_basis_holds)

end DARM

#print axioms DARM.factorNegative_basisEstablishment
#print axioms DARM.factorNegative_basis_holds
#print axioms DARM.factorNegative_target_fails
#print axioms DARM.factorNegative_basisTargetAdequacy_fails
