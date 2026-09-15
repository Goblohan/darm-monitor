import DarmMonitor.CompositionRuleBoundary

namespace DARM

structure RuleNegativeState where
  localSafe : Bool
  systemSafe : Bool
  deriving DecidableEq, Repr

inductive RuleNegativeBoundary
  | localSource
  | localTarget
  | systemTarget
  deriving DecidableEq, Repr

inductive RuleNegativeLocus
  | localEnforcer
  | systemEnforcer
  deriving DecidableEq, Repr

def ruleNegativeGuarantee :
    BoundaryIndexedGuarantee
      RuleNegativeState RuleNegativeBoundary :=
  fun boundary state =>
    match boundary with
    | RuleNegativeBoundary.localSource =>
        state.localSafe = true
    | RuleNegativeBoundary.localTarget =>
        state.localSafe = true
    | RuleNegativeBoundary.systemTarget =>
        state.systemSafe = true

def ruleNegativeEvidence :
    ScopedEvidence
      RuleNegativeBoundary RuleNegativeState :=
  fun boundary state =>
    match boundary with
    | RuleNegativeBoundary.localSource =>
        state.localSafe = true
    | RuleNegativeBoundary.localTarget =>
        state.localSafe = true
    | RuleNegativeBoundary.systemTarget =>
        state.localSafe = true

def ruleNegativeEnforced :
    RuleNegativeLocus →
    RuleNegativeBoundary →
    RuleNegativeState →
    Prop :=
  fun locus boundary state =>
    match locus, boundary with
    | RuleNegativeLocus.localEnforcer,
      RuleNegativeBoundary.localTarget =>
        state.localSafe = true
    | RuleNegativeLocus.systemEnforcer,
      RuleNegativeBoundary.systemTarget =>
        state.localSafe = true
    | _, _ =>
        False

/--
A valid local composition rule:
local source evidence and local enforcement establish the
local target guarantee.
-/
def localRule :
    BoundaryIndexedCompositionRule
      ruleNegativeGuarantee
      ruleNegativeEvidence
      ruleNegativeEnforced
      RuleNegativeBoundary.localSource
      RuleNegativeBoundary.localTarget
      RuleNegativeLocus.localEnforcer :=
  { compositionBoundary := CompositionBoundary.local
    establishesTarget := by
      intro s hSource hEvidence hEnforced
      exact hEvidence }

/--
The concrete state satisfies the local condition but not the broader
system condition.
-/
def negativeState : RuleNegativeState :=
  { localSafe := true
    systemSafe := false }

theorem localRule_is_locally_scoped :
    localRule.compositionBoundary =
      CompositionBoundary.local := by
  rfl

/--
The local composition rule is valid for the local target.
-/
theorem localRule_establishes_localTarget :
    ruleNegativeGuarantee
      RuleNegativeBoundary.localTarget
      negativeState := by
  exact localRule.establishesTarget
    negativeState
    (by rfl)
    (by rfl)
    (by rfl)

/--
The broader system guarantee is false.
-/
theorem systemTarget_fails :
    ¬ ruleNegativeGuarantee
        RuleNegativeBoundary.systemTarget
        negativeState := by
  intro h
  exact Bool.noConfusion h

/--
The local rule does not establish the broader system guarantee.
-/
theorem localRule_does_not_imply_systemTarget :
    ¬ ruleNegativeGuarantee
        RuleNegativeBoundary.systemTarget
        negativeState := by
  exact systemTarget_fails

/--
The local rule's declared composition boundary is not the system
composition boundary.
-/
theorem localRule_not_system_scoped :
    localRule.compositionBoundary ≠
      CompositionBoundary.system := by
  intro h
  cases h

end DARM

#print axioms DARM.localRule_is_locally_scoped
#print axioms DARM.localRule_establishes_localTarget
#print axioms DARM.systemTarget_fails
#print axioms DARM.localRule_does_not_imply_systemTarget
#print axioms DARM.localRule_not_system_scoped
