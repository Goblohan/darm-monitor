import DarmMonitor.Basic
import DarmMonitor.BoundaryMargin
import DarmMonitor.StratumComposition

namespace DARM.SemanticQuotient

abbrev Action := Fin 2

def meaning : Action → Nat
  | 0 => 0
  | 1 => 1

theorem action_zero_ne_one : (0 : Action) ≠ 1 := by
  decide

theorem meaning_zero_ne_one :
    meaning (0 : Action) ≠ meaning (1 : Action) := by
  decide

def semanticImage (s : Finset Action) : Finset Nat :=
  s.image meaning

theorem semanticImage_singleton :
    semanticImage ({0} : Finset Action) = {0} := by
  simp [semanticImage, meaning]

theorem semanticImage_pair :
    semanticImage ({0, 1} : Finset Action) = {0, 1} := by
  simp [semanticImage, meaning]

theorem semanticImage_strict_expansion :
    semanticImage ({0} : Finset Action) ⊂
      semanticImage ({0, 1} : Finset Action) := by
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro x hx
    rw [semanticImage_singleton] at hx
    rw [semanticImage_pair]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    exact Or.inl hx
  · intro h
    rw [semanticImage_singleton, semanticImage_pair] at h
    have h1 := Finset.ext_iff.mp h 1
    simp at h1

end DARM.SemanticQuotient

#print axioms DARM.SemanticQuotient.action_zero_ne_one
#print axioms DARM.SemanticQuotient.meaning_zero_ne_one
#print axioms DARM.SemanticQuotient.semanticImage_strict_expansion