import DarmMonitor.CompositionRuleValidity

namespace DARM

structure ValidityNegativeState where
  localSafe : Bool
  systemSafe : Bool

inductive ValidityNegativeBoundary
  | source
  | systemTarget
  deriving DecidableEq, Repr

inductive ValidityNegativeLocus
  | systemEnforcer
  deriving DecidableEq, Repr

def validityNegativeGuarantee :
    BoundaryIndexedGuarantee
      ValidityNegativeState
      ValidityNegativeBoundary :=
  fun boundary state =>
    match boundary with
    | ValidityNegativeBoundary.source =>
        state.localSafe = true
    | ValidityNegativeBoundary.systemTarget =>
        state.systemSafe = true

def validityNegativeEvidence :
    ScopedEvidence
      ValidityNegativeBoundary
      ValidityNegativeState :=
  fun boundary state =>
    match boundary with
    | ValidityNegativeBoundary.source =>
        state.localSafe = true
    | ValidityNegativeBoundary.systemTarget =>
        state.localSafe = true

def validityNegativeEnforced :
    ValidityNegativeLocus →
    ValidityNegativeBoundary →
    ValidityNegativeState →
    Prop :=
  fun locus boundary state =>
    match locus, boundary with
    | ValidityNegativeLocus.systemEnforcer,
      ValidityNegativeBoundary.systemTarget =>
        state.localSafe = true
    | _, _ =>
        False

def systemDeclaredRule :
    CompositionRuleDeclaration
      validityNegativeGuarantee
      validityNegativeEvidence
      validityNegativeEnforced
      ValidityNegativeBoundary.source
      ValidityNegativeBoundary.systemTarget
      ValidityNegativeLocus.systemEnforcer :=
  { compositionBoundary := CompositionBoundary.system }

def negativeState : ValidityNegativeState :=
  { localSafe := true
    systemSafe := false }

theorem systemDeclaredRule_is_system_scoped :
    systemDeclaredRule.compositionBoundary =
      CompositionBoundary.system := by
  rfl

theorem systemDeclaredRule_premises_hold :
    validityNegativeGuarantee
        ValidityNegativeBoundary.source
        negativeState ∧
    validityNegativeEvidence
        ValidityNegativeBoundary.systemTarget
        negativeState ∧
    validityNegativeEnforced
        ValidityNegativeLocus.systemEnforcer
        ValidityNegativeBoundary.systemTarget
        negativeState := by
  constructor
  · rfl
  constructor <;> rfl

theorem systemTarget_fails :
    ¬ validityNegativeGuarantee
        ValidityNegativeBoundary.systemTarget
        negativeState := by
  intro h
  exact Bool.noConfusion h

theorem systemDeclaredRule_is_invalid :
    ¬ CompositionRuleValid
        ValidityNegativeLocus.systemEnforcer
        systemDeclaredRule := by
  intro hValid
  have hTarget :=
    hValid
      negativeState
      (by rfl)
      (by rfl)
      (by rfl)
  exact Bool.noConfusion hTarget

end DARM

