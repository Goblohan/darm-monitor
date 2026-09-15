import DarmMonitor.CompositionRuleBasis

namespace DARM

structure BasisNegativeState where
  localSafe : Bool
  systemSafe : Bool

inductive BasisNegativeBoundary
  | source
  | systemTarget
  deriving DecidableEq, Repr

inductive BasisNegativeLocus
  | systemEnforcer
  deriving DecidableEq, Repr

def basisNegativeGuarantee :
    BoundaryIndexedGuarantee
      BasisNegativeState
      BasisNegativeBoundary :=
  fun boundary state =>
    match boundary with
    | BasisNegativeBoundary.source =>
        state.localSafe = true
    | BasisNegativeBoundary.systemTarget =>
        state.systemSafe = true

def basisNegativeEvidence :
    ScopedEvidence
      BasisNegativeBoundary
      BasisNegativeState :=
  fun boundary state =>
    match boundary with
    | BasisNegativeBoundary.source =>
        state.localSafe = true
    | BasisNegativeBoundary.systemTarget =>
        state.localSafe = true

def basisNegativeEnforced :
    BasisNegativeLocus →
    BasisNegativeBoundary →
    BasisNegativeState →
    Prop :=
  fun locus boundary state =>
    match locus, boundary with
    | BasisNegativeLocus.systemEnforcer,
      BasisNegativeBoundary.systemTarget =>
        state.localSafe = true
    | _, _ =>
        False

def weakBasis :
    BasisNegativeState → Prop :=
  fun state =>
    state.localSafe = true

def systemDeclaredBasisRule :
    CompositionRuleDeclaration
      basisNegativeGuarantee
      basisNegativeEvidence
      basisNegativeEnforced
      BasisNegativeBoundary.source
      BasisNegativeBoundary.systemTarget
      BasisNegativeLocus.systemEnforcer :=
  { compositionBoundary := CompositionBoundary.system }

def basisNegativeState : BasisNegativeState :=
  { localSafe := true
    systemSafe := false }

theorem systemDeclaredBasisRule_is_system_scoped :
    systemDeclaredBasisRule.compositionBoundary =
      CompositionBoundary.system := by
  rfl

theorem basisNegative_source_guarantee :
    basisNegativeGuarantee
      BasisNegativeBoundary.source
      basisNegativeState := by
  rfl

theorem basisNegative_target_evidence :
    basisNegativeEvidence
      BasisNegativeBoundary.systemTarget
      basisNegativeState := by
  rfl

theorem basisNegative_target_enforcement :
    basisNegativeEnforced
      BasisNegativeLocus.systemEnforcer
      BasisNegativeBoundary.systemTarget
      basisNegativeState := by
  rfl

theorem basisNegative_weak_basis_holds :
    weakBasis basisNegativeState := by
  rfl

theorem basisNegative_target_guarantee_fails :
    ¬ basisNegativeGuarantee
      BasisNegativeBoundary.systemTarget
      basisNegativeState := by
  intro h
  exact Bool.noConfusion h

theorem weakBasis_does_not_establish_system_target :
    weakBasis basisNegativeState ∧
    ¬ basisNegativeGuarantee
      BasisNegativeBoundary.systemTarget
      basisNegativeState := by
  constructor
  · exact basisNegative_weak_basis_holds
  · exact basisNegative_target_guarantee_fails

end DARM


