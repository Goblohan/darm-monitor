/-
Executable obligation core. Labels denote authenticated assertions, not facts
about the physical world. The Python implementation is tested against this
definition. Parsing, cryptography and complete mediation are outside this file.
-/
import Lean

namespace DARM.E38.Operational

def rowOK (facts row : List String) : Bool :=
  decide (row ≠ []) && row.all (fun atom => decide (atom ∈ facts))

def admitRel (facts : List String) (obligations : List (List String))
    (checks : List Bool) : Bool :=
  decide (obligations ≠ []) && checks.all (fun c => c) &&
    obligations.all (rowOK facts)

/-- Operational support, with no external-world interpretation. -/
def Supported (facts : List String) (obligations : List (List String)) : Prop :=
  obligations ≠ [] ∧ ∀ row ∈ obligations, row ≠ [] ∧ ∀ atom ∈ row, atom ∈ facts

theorem rowOK_iff (facts row : List String) :
    rowOK facts row = true ↔ row ≠ [] ∧ ∀ atom ∈ row, atom ∈ facts := by
  simp [rowOK, List.all_eq_true]

theorem admit_iff (facts : List String) (obligations : List (List String))
    (checks : List Bool) :
    admitRel facts obligations checks = true ↔
      Supported facts obligations ∧ (∀ c ∈ checks, c = true) := by
  simp only [admitRel, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    rowOK_iff, Supported]
  constructor
  · rintro ⟨⟨hne, hc⟩, hr⟩
    exact ⟨⟨hne, hr⟩, hc⟩
  · rintro ⟨⟨hne, hr⟩, hc⟩
    exact ⟨⟨hne, hc⟩, hr⟩

theorem admitted_implies_supported (facts : List String)
    (obligations : List (List String)) (checks : List Bool)
    (h : admitRel facts obligations checks = true) : Supported facts obligations :=
  ((admit_iff facts obligations checks).mp h).1

theorem missing_required_atom_refuses (facts : List String)
    (obligations : List (List String)) (checks : List Bool)
    (row : List String) (atom : String)
    (hr : row ∈ obligations) (ha : atom ∈ row) (hm : atom ∉ facts) :
    admitRel facts obligations checks ≠ true := by
  intro h
  exact hm (((admitted_implies_supported facts obligations checks h).2 row hr).2 atom ha)

theorem failed_check_refuses (facts : List String)
    (obligations : List (List String)) (checks : List Bool)
    (h : false ∈ checks) : admitRel facts obligations checks ≠ true := by
  intro hAdmit
  have hf := ((admit_iff facts obligations checks).mp hAdmit).2 false h
  cases hf

theorem empty_contract_refuses (facts : List String) (checks : List Bool) :
    admitRel facts [] checks = false := by simp [admitRel]

#print axioms admitted_implies_supported
#print axioms missing_required_atom_refuses
#print axioms failed_check_refuses

end DARM.E38.Operational
