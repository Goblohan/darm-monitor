import DarmMonitor.Basic

namespace DARM

/-
E0/E1: Semantic → Executable Preservation

Goal:
  Test whether a semantic meaning can be related to an
  executable state transition without assuming the relation.

The experiment deliberately distinguishes:

  Meaning
      ↓
  Action
      ↓
  Executable transition
      ↓
  Meaning satisfied

The key question is whether "Preserves" can be derived
from executable semantics rather than stipulated.
-/

inductive Meaning
  | OpenDoor
  | CloseDoor
  deriving DecidableEq, Repr

inductive Action
  | Open
  | Close
  deriving DecidableEq, Repr

inductive DoorState
  | Open
  | Closed
  deriving DecidableEq, Repr

/-- Concrete executable semantics. -/
def execute : DoorState → Action → DoorState
  | .Closed, .Open  => .Open
  | .Open,   .Close => .Closed
  | s, _ => s

/-- What it means for a final state to satisfy a meaning. -/
def MeaningSatisfied : Meaning → DoorState → Prop
  | .OpenDoor,  .Open   => True
  | .CloseDoor, .Closed => True
  | _, _ => False

/--
Semantic preservation is NOT stipulated directly.

It is derived from:
  1. execution actually producing the claimed state
  2. that state satisfying the meaning
-/
def Preserves
    (m : Meaning)
    (a : Action)
    (s s' : DoorState) : Prop :=
  execute s a = s' ∧
  MeaningSatisfied m s'

/-- Positive case: opening a closed door realizes OpenDoor. -/
theorem open_preserves :
    Preserves .OpenDoor .Open .Closed .Open := by
  simp [Preserves, execute, MeaningSatisfied]

/-- Positive case: closing an open door realizes CloseDoor. -/
theorem close_preserves :
    Preserves .CloseDoor .Close .Open .Closed := by
  simp [Preserves, execute, MeaningSatisfied]

/-- Wrong action does not preserve the meaning. -/
theorem wrong_action_fails :
    ¬ Preserves .OpenDoor .Close .Closed .Closed := by
  simp [Preserves, execute, MeaningSatisfied]

/--
A semantic meaning by itself does not establish preservation.
The executable transition must actually realize it.
-/
theorem preservation_requires_execution :
    ¬ Preserves .OpenDoor .Open .Closed .Closed := by
  simp [Preserves, execute, MeaningSatisfied]

/--
Opening a closed door yields an open door: one evaluation of execute
(every Lean function is deterministic; this states one input-output pair).
-/
theorem open_from_closed_yields_open :
    execute .Closed .Open = .Open := by
  rfl

/--
Now combine semantic preservation with authorization and coverage.
This is the first minimal entitlement relation.
-/
def Authorized : Meaning → Action → Prop
  | .OpenDoor, .Open => True
  | .CloseDoor, .Close => True
  | _, _ => False

/-- In this model every action is covered, so coverage never decides entitlement. -/
def Covered : Action → Prop
  | .Open => True
  | .Close => True

def Entitled
    (m : Meaning)
    (a : Action)
    (s s' : DoorState) : Prop :=
  Preserves m a s s' ∧
  Authorized m a ∧
  Covered a

/-- The complete positive path. -/
theorem open_entitled :
    Entitled .OpenDoor .Open .Closed .Open := by
  simp [Entitled, Preserves, execute,
        MeaningSatisfied, Authorized, Covered]

/-- A wrong action is not entitled: closing, for the meaning OpenDoor, is
    both unauthorized and non-preserving. -/
theorem wrong_action_not_entitled :
    ¬ Entitled .OpenDoor .Close .Closed .Closed := by
  simp [Entitled, Preserves, execute,
        MeaningSatisfied, Authorized, Covered]

/-- Authorization alone cannot establish entitlement: opening is authorized
    for OpenDoor, and covered, yet not entitled when the claimed outcome
    (still closed) is not what execution produces. -/
theorem authorized_but_unrealized_not_entitled :
    ¬ Entitled .OpenDoor .Open .Closed .Closed := by
  simp [Entitled, Preserves, execute,
        MeaningSatisfied, Authorized, Covered]

end DARM
