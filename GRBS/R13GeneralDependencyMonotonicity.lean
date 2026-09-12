import GRBS

namespace GRBS.R13GeneralDependencyMonotonicity

/-
R13 abstracts the R11/R12 witness pair.

The central observation is purely relational:

  If D1 is a subset of D2, then coverage of D2 implies
  coverage of D1.

Thus dependency expansion is safe only when the expanded
dependency relation remains covered.

The result is stated independently of any particular
implementation of dependencies or boundaries.
-/

/--
Dependency inclusion.
-/
def DependencySubset
    {D : Type}
    (D1 D2 : D → Prop) : Prop :=
  ∀ d, D1 d → D2 d

/--
Coverage of a dependency relation.
-/
def Covers
    {D : Type}
    (Deps : D → Prop)
    (Cov : D → Prop) : Prop :=
  ∀ d, Deps d → Cov d

/--
Coverage of the expanded dependency set implies coverage
of the original dependency set whenever the original set
is included in the expanded set.
-/
theorem coverage_preserved_under_dependency_restriction
    {D : Type}
    (D1 D2 Cov : D → Prop)
    (hSubset : DependencySubset D1 D2)
    (hExpanded : Covers D2 Cov) :
    Covers D1 Cov := by
  intro d hd
  exact hExpanded d (hSubset d hd)

/--
GRBS is preserved when the dependency relation used by the
guarantee is restricted to a subset whose members are still
covered by the same boundary.
-/
theorem grbs_preserved_under_dependency_restriction
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (D1 : F.Dependency → Prop)
    (hSubset :
      ∀ d, D1 d → F.dep g s d)
    (hGRBS :
      GRBS F g s b l) :
    Covers D1 (fun d => F.cov b l s d) := by
  intro d hd
  exact hGRBS d (hSubset d hd)

/--
If an expanded dependency relation is fully covered, then
the original GRBS dependency relation remains covered.
-/
theorem expanded_coverage_implies_restricted_coverage
    {D : Type}
    (D1 D2 Cov : D → Prop)
    (hSubset : DependencySubset D1 D2)
    (hExpanded : Covers D2 Cov) :
    Covers D1 Cov :=
  coverage_preserved_under_dependency_restriction
    D1 D2 Cov hSubset hExpanded

/--
A newly introduced uncovered dependency is sufficient to
demonstrate that coverage cannot be inferred merely from
coverage of the original dependency relation.
-/
theorem uncovered_new_dependency_blocks_expanded_coverage
    {D : Type}
    (D2 Cov : D → Prop)
    (d : D)
    (hNew : D2 d)
    (hUncovered : ¬ Cov d) :
    ¬ Covers D2 Cov := by
  intro hCovered
  exact hUncovered (hCovered d hNew)

/--
Exact decomposition of coverage under dependency expansion.

When D1 is a subset of D2, coverage of the expanded
dependency relation is equivalent to coverage of the
original dependency relation together with coverage of
the newly introduced dependencies.
-/
theorem coverage_expansion_iff_new_dependencies_covered
    {D : Type}
    (D1 D2 Cov : D → Prop)
    (hSubset : DependencySubset D1 D2) :
    Covers D2 Cov ↔
      Covers D1 Cov ∧
      Covers (fun d => D2 d ∧ ¬ D1 d) Cov := by
  constructor
  · intro hExpanded
    constructor
    · exact coverage_preserved_under_dependency_restriction
        D1 D2 Cov hSubset hExpanded
    · intro d hd
      exact hExpanded d hd.1
  · intro hParts
    intro d hd2
    by_cases hd1 : D1 d
    · exact hParts.1 d hd1
    · exact hParts.2 d ⟨hd2, hd1⟩

end GRBS.R13GeneralDependencyMonotonicity
