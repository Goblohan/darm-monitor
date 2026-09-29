import E0SemanticExecutable

namespace DARM

/-
E2: Software → Physical Boundary

Question:
Can semantic preservation hold at the software layer
while failing at the physical layer?

If yes, what additional assumption is required to
transfer the guarantee across that boundary?

Answer (rewritten on review). Yes: with an actuator that does not implement
the software transition, a meaning preserved in software fails physically
(software_preserves_physical_does_not, the counterexample). The assumption
that transfers the guarantee is actuator correctness, a commuting square:
running the actuator on the realized state gives the realization of what the
software computed. Under it, software preservation implies physical
preservation of the realized states, for every meaning, action and state
(preservation_transfers); the broken actuator violates it
(broken_actuator_not_correct). For DARM, the broker's model is the software
layer, and the correspondence of the real filesystem to that model is the
actuator-correctness assumption, which the B8 trace checker tests.

NOT claimed: that any real actuator is correct; that realize is the only
sensible realization.
-/

inductive PhysicalDoorState
  | Open
  | Closed
  deriving DecidableEq, Repr

/-- A broken physical actuator: it never changes the door's state. -/
def physicalExecute :
    PhysicalDoorState → Action → PhysicalDoorState
  | .Closed, .Open  => .Closed
  | .Open,   .Close => .Open
  | s, _ => s

/-- Physical realization of a meaning. -/
def PhysicalMeaningSatisfied :
    Meaning → PhysicalDoorState → Prop
  | .OpenDoor,  .Open   => True
  | .CloseDoor, .Closed => True
  | _, _ => False

def PhysicalPreserves
    (m : Meaning)
    (a : Action)
    (s s' : PhysicalDoorState) : Prop :=
  physicalExecute s a = s' ∧
  PhysicalMeaningSatisfied m s'

/--
The counterexample. Software says the door opened; the broken actuator
fails to open it.
-/
theorem software_preserves_physical_does_not :
    Preserves .OpenDoor .Open .Closed .Open ∧
    ¬ PhysicalPreserves .OpenDoor .Open .Closed .Closed := by
  constructor
  · exact open_preserves
  · simp [PhysicalPreserves, physicalExecute,
          PhysicalMeaningSatisfied]

/-! ## The transfer assumption, and the transfer theorem -/

/-- How a software state is realized physically. -/
def realize : DoorState → PhysicalDoorState
  | .Open => .Open
  | .Closed => .Closed

/-- Physical preservation for an arbitrary actuator. -/
def PhysicalPreservesWith (px : PhysicalDoorState → Action → PhysicalDoorState)
    (m : Meaning) (a : Action) (s s' : PhysicalDoorState) : Prop :=
  px s a = s' ∧ PhysicalMeaningSatisfied m s'

/-- The transfer assumption: the actuator implements the software transition
    (a commuting square through realize). -/
def ActuatorCorrect (px : PhysicalDoorState → Action → PhysicalDoorState) : Prop :=
  ∀ s a, px (realize s) a = realize (execute s a)

/-- Satisfying a meaning in software implies satisfying it physically. -/
theorem satisfied_transfers (m : Meaning) (s : DoorState)
    (h : MeaningSatisfied m s) : PhysicalMeaningSatisfied m (realize s) := by
  cases m <;> cases s <;> simp_all [MeaningSatisfied, PhysicalMeaningSatisfied, realize]

/-- Transfer: under a correct actuator, software preservation implies
    physical preservation of the realized states. -/
theorem preservation_transfers (px : PhysicalDoorState → Action → PhysicalDoorState)
    (hpx : ActuatorCorrect px) (m : Meaning) (a : Action) (s s' : DoorState)
    (h : Preserves m a s s') : PhysicalPreservesWith px m a (realize s) (realize s') := by
  obtain ⟨hexec, hsat⟩ := h
  exact ⟨by rw [hpx s a, hexec], satisfied_transfers m s' hsat⟩

/-- The file's actuator violates the assumption, which is why the
    counterexample exists. -/
theorem broken_actuator_not_correct : ¬ ActuatorCorrect physicalExecute := by
  intro h
  have := h .Closed .Open
  simp [physicalExecute, realize, execute] at this

/-- PhysicalPreserves is PhysicalPreservesWith at the broken actuator. -/
theorem physicalPreserves_is_broken_instance (m : Meaning) (a : Action)
    (s s' : PhysicalDoorState) :
    PhysicalPreserves m a s s' ↔ PhysicalPreservesWith physicalExecute m a s s' :=
  Iff.rfl

end DARM

#print axioms DARM.software_preserves_physical_does_not
#print axioms DARM.satisfied_transfers
#print axioms DARM.preservation_transfers
#print axioms DARM.broken_actuator_not_correct
#print axioms DARM.physicalPreserves_is_broken_instance
