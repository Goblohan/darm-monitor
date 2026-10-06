/-
  E36: COMPOSITIONAL REPRESENTATION ADEQUACY

  E35 establishes adequacy for one observed representation. E36 asks whether
  adequacy can survive a finite chain of representation transitions, and whether
  the first lossy transition can be represented by a witness.

  This is property-specific. It does not claim semantic equivalence or provide
  an executable search over arbitrary propositions.
-/
import E35RepresentationAdequacy

namespace DARM.E36

/-- Apply one representation transition to an observation. -/
def advance {V O : Type} (observe : V → O) (step : O → O) : V → O :=
  fun v => step (observe v)

/-- The observation after a finite sequence of transitions. -/
def chainObservation {V O : Type} (observe : V → O) :
    List (O → O) → V → O
  | [] => observe
  | step :: rest => chainObservation (advance observe step) rest

/-- The local obligation discharged by one representation transition. -/
def TransitionPreserves {V O : Type} (P : V → Prop)
    (observe : V → O) (step : O → O) : Prop :=
  DARM.E35.AdequateFor observe P →
    DARM.E35.AdequateFor (advance observe step) P

/-- Every transition in a finite chain discharges its local obligation. -/
def ChainObligations {V O : Type} (P : V → Prop)
    (observe : V → O) : List (O → O) → Prop
  | [] => True
  | step :: rest =>
      TransitionPreserves P observe step ∧
        ChainObligations P (advance observe step) rest

/-- Local adequacy obligations compose through the whole chain. -/
theorem chain_preserves {V O : Type} (P : V → Prop)
    (observe : V → O) :
    ∀ steps, DARM.E35.AdequateFor observe P →
      ChainObligations P observe steps →
      DARM.E35.AdequateFor (chainObservation observe steps) P := by
  intro steps
  induction steps generalizing observe with
  | nil =>
      intro hInitial _
      simpa [chainObservation] using hInitial
  | cons step rest ih =>
      intro hInitial hObligations
      rcases hObligations with ⟨hStep, hRest⟩
      simpa [chainObservation] using
        (ih (observe := advance observe step) (hStep hInitial) hRest)

/-- A pair in one observed class with different property values. -/
def LossWitness {V O : Type} (observe : V → O) (P : V → Prop) : Prop :=
  ∃ r v, DARM.E35.ObservedGate observe r v ∧
    ((P r ∧ ¬ P v) ∨ (¬ P r ∧ P v))

/-- A loss witness proves that the representation is not adequate for P. -/
theorem lossWitness_not_adequate {V O : Type}
    {observe : V → O} {P : V → Prop}
    (hLoss : LossWitness observe P) :
    ¬ DARM.E35.AdequateFor observe P := by
  rcases hLoss with ⟨r, v, hSame, hDifferent⟩
  rcases hDifferent with ⟨hR, hNotV⟩ | ⟨hNotR, hV⟩
  · exact DARM.E35.alias_defeats_adequacy hSame hR hNotV
  · intro hA
    exact hNotR (DARM.E35.observed_preserved hA hV hSame.symm)

/-- The first transition with a loss witness, indexed from zero.

    For a later index, adequacy of the immediately preceding representation
    is included, so the witness is the first one in the chain.
-/
def FirstLossAt {V O : Type} (P : V → Prop) (observe : V → O) :
    List (O → O) → Nat → Prop
  | [], _ => False
  | step :: _rest, 0 => LossWitness (advance observe step) P
  | step :: rest, Nat.succ n =>
      DARM.E35.AdequateFor (advance observe step) P ∧
        FirstLossAt P (advance observe step) rest n

/-- A first-loss certificate exposes an actual lossy representation. -/
theorem firstLoss_has_witness {V O : Type}
    {P : V → Prop} {observe : V → O}
    {steps : List (O → O)} {n : Nat}
    (h : FirstLossAt P observe steps n) :
    ∃ obs : V → O, LossWitness obs P := by
  induction steps generalizing observe n with
  | nil =>
      cases h
  | cons step rest ih =>
      cases n with
      | zero =>
          exact ⟨advance observe step, h⟩
      | succ n =>
          exact ih (observe := advance observe step) (n := n) h.2

/-- An initially adequate chain whose first loss occurs at a transition
    falsifies that transition's local preservation obligation. -/
theorem firstLoss_exposes_transition_gap {V O : Type}
    {P : V → Prop} {observe : V → O}
    {steps : List (O → O)} {n : Nat}
    (hInitial : DARM.E35.AdequateFor observe P)
    (h : FirstLossAt P observe steps n) :
    ∃ before : V → O, ∃ step : O → O,
      DARM.E35.AdequateFor before P ∧
      ¬ TransitionPreserves P before step := by
  revert observe n hInitial h
  induction steps with
  | nil =>
      intro observe n hInitial h
      cases h
  | cons step rest ih =>
      intro observe n hInitial h
      cases n with
      | zero =>
          refine ⟨observe, step, hInitial, ?_⟩
          intro hPreserves
          exact (lossWitness_not_adequate h) (hPreserves hInitial)
      | succ n =>
          exact ih (observe := advance observe step) (n := n) h.1 h.2

/-- The first-loss certificate identifies an inadequate representation.
    The stronger theorem above locates a failed local obligation. -/
theorem firstLoss_exposes_undischarged {V O : Type}
    {P : V → Prop} {observe : V → O}
    {steps : List (O → O)} {n : Nat}
    (h : FirstLossAt P observe steps n) :
    ∃ obs : V → O, ¬ DARM.E35.AdequateFor obs P := by
  rcases firstLoss_has_witness h with ⟨obs, hLoss⟩
  exact ⟨obs, lossWitness_not_adequate hLoss⟩

/-! A finite witness using E35's guarded and unconditional programs. -/

def collapse : Bool → Bool := fun _ => false

theorem collapse_is_lossy :
    LossWitness
      (advance DARM.E35.structural collapse)
      DARM.E35.Authorized := by
  refine ⟨.guarded, .unconditional, ?_, ?_⟩
  · rfl
  · exact Or.inl ⟨
      DARM.E35.erased_admits_unauthorized_change.2.1,
      DARM.E35.erased_admits_unauthorized_change.2.2⟩

theorem collapse_is_first_loss :
    FirstLossAt DARM.E35.Authorized DARM.E35.structural [collapse] 0 := by
  simpa [FirstLossAt] using collapse_is_lossy

theorem collapse_exposes_undischarged :
    ∃ obs : DARM.E35.Program → Bool, ¬ DARM.E35.AdequateFor obs DARM.E35.Authorized :=
  ⟨advance DARM.E35.structural collapse,
    lossWitness_not_adequate collapse_is_lossy⟩

end DARM.E36

#print axioms DARM.E36.chain_preserves
#print axioms DARM.E36.lossWitness_not_adequate
#print axioms DARM.E36.firstLoss_exposes_transition_gap
#print axioms DARM.E36.firstLoss_exposes_undischarged
#print axioms DARM.E36.collapse_is_first_loss
