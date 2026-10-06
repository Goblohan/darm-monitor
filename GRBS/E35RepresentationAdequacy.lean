/-
  E35: REPRESENTATION ADEQUACY FOR ASSURANCE PRESERVATION

  E34's gate compares code in reviewed cones. A concrete checker instead sees
  a representation (for example an inventory of fingerprints). Equality of that
  representation may stand in for E34's Gate only with a bridge obligation.

  Statements: property-specific adequacy is exactly preservation from every reviewed
  member of an observation class; a representation that reflects E34's code gate
  transfers its preservation theorem; a representation that erases guardedness
  admits an unsafe change, while one retaining guardedness preserves the toy
  authorization property.

  The witness models the indentation regression in DARM Guard's gate_attacks.py.
  It does not formalize Python, its tokenizer, hashing, the dependency inventory,
  or its environment. Those implementation bridges remain tested or assumed.
  Retaining suite markers repairs that witness, not arbitrary semantic gaps.
  E24e already characterizes observation-bound authorization; this module applies
  the same distinction to reviewed-program preservation, with an E34 bridge.
-/
import E34AssuranceUnderChange

namespace DARM.E35

/-- The concrete gate observes representations rather than programs directly. -/
def ObservedGate {V O : Type} (observe : V → O) (reviewed candidate : V) : Prop :=
  observe reviewed = observe candidate

/-- The representation retains the distinctions needed by this property. -/
def AdequateFor {V O : Type} (observe : V → O) (P : V → Prop) : Prop :=
  ∀ r v, ObservedGate observe r v → (P r ↔ P v)

theorem observed_preserved {V O : Type} {observe : V → O} {P : V → Prop}
    (hA : AdequateFor observe P) {r v : V} (hR : P r)
    (hG : ObservedGate observe r v) : P v :=
  (hA r v hG).mp hR

/-- Characterization over all reviewed members, not completeness of every gate. -/
theorem adequate_iff_preserves_all_reviews {V O : Type} (observe : V → O) (P : V → Prop) :
    AdequateFor observe P ↔
      ∀ r v, ObservedGate observe r v → P r → P v := by
  constructor
  · intro h r v hG hR
    exact observed_preserved h hR hG
  · intro h r v hG
    exact ⟨h r v hG, h v r hG.symm⟩

/-- Stronger, property-independent obligation for reusing E34's code gate. -/
def ReflectsCodeGate {N C O : Type} (A : E34.Analysis N C)
    (observe : E34.Prog N C → O) : Prop :=
  ∀ r v, ObservedGate observe r v → E34.Gate A r v

theorem e34_preserved_through_representation {N C O : Type}
    (A : E34.Analysis N C) (P : E34.Prog N C → Prop)
    (observe : E34.Prog N C → O) (hL : E34.Local A P)
    (hBridge : ReflectsCodeGate A observe) (r v : E34.Prog N C)
    (hR : P r) (hObserved : ObservedGate observe r v) : P v :=
  E34.preserved A P hL r v hR (hBridge r v hObserved)

/-- One observed class containing a good and bad program defeats adequacy. -/
theorem alias_defeats_adequacy {V O : Type} {observe : V → O} {P : V → Prop}
    {r v : V} (hSame : ObservedGate observe r v) (hGood : P r) (hBad : ¬ P v) :
    ¬ AdequateFor observe P := by
  intro hA
  exact hBad (observed_preserved hA hGood hSame)

/-! A finite witness: the same effect under a guard, or outside it. -/

inductive Program where
  | guarded
  | unconditional
  deriving DecidableEq, Repr

def effect : Program → Bool → Bool
  | .guarded, allowed => allowed
  | .unconditional, _ => true

def Authorized (p : Program) : Prop :=
  ∀ allowed, effect p allowed = true → allowed = true

/-- Abstracts a representation that drops the only distinguishing structure. -/
def erased : Program → Unit := fun _ => ()

def structural : Program → Bool
  | .guarded => true
  | .unconditional => false

theorem erased_admits_unauthorized_change :
    ObservedGate erased .guarded .unconditional ∧
    Authorized .guarded ∧ ¬ Authorized .unconditional := by
  refine ⟨rfl, ?_, ?_⟩
  · intro allowed h
    exact h
  · intro h
    have impossible := h false rfl
    cases impossible

theorem erased_not_adequate : ¬ AdequateFor erased Authorized :=
  alias_defeats_adequacy erased_admits_unauthorized_change.1
    erased_admits_unauthorized_change.2.1 erased_admits_unauthorized_change.2.2

theorem structural_adequate : AdequateFor structural Authorized := by
  intro r v h
  cases r <;> cases v <;> simp_all [ObservedGate, structural]

theorem structural_rejects_witness :
    ¬ ObservedGate structural .guarded .unconditional := by
  simp [ObservedGate, structural]

end DARM.E35

#print axioms DARM.E35.observed_preserved
#print axioms DARM.E35.adequate_iff_preserves_all_reviews
#print axioms DARM.E35.e34_preserved_through_representation
#print axioms DARM.E35.alias_defeats_adequacy
#print axioms DARM.E35.erased_admits_unauthorized_change
#print axioms DARM.E35.erased_not_adequate
#print axioms DARM.E35.structural_adequate
#print axioms DARM.E35.structural_rejects_witness
