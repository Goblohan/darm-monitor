import GRBS
import R5AssuranceConservation
import R6GRBSDeltaBridge

open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge

namespace GRBS.R14DeltaBasedAssuranceTransfer

/--
Dependency inclusion used by the delta-transfer formulation.
-/
def DependencySubset
    {D : Type}
    (D1 D2 : D → Prop) : Prop :=
  ∀ d, D1 d → D2 d

/--
A delta-based assurance transfer requires:

1. assurance of the source domain,
2. explicit representation of every newly introduced target item
   as a structural dependency,
3. boundary coverage of those dependencies, and
4. semantic discharge of the covered dependencies.

The source-to-target dependency inclusion is recorded explicitly
to make dependency expansion visible at the transfer boundary.
-/
def DeltaBasedTransfer
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop) : Prop :=
  SourceAssured F.Dependency source property ∧
  DependencySubset source target ∧
  DeltaSubsetDependency F g s source target ∧
  GRBS F g s b l ∧
  CoveredDischargesProperty F g s b l property

/--
Delta-based transfer establishes the R5 delta obligation.

The proof explicitly composes the structural dependency
representation, GRBS coverage, and semantic discharge.
-/
theorem delta_transfer_discharges_obligation
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop)
    (hTransfer :
      DeltaBasedTransfer F g s b l source target property) :
    DeltaObligation F.Dependency source target property := by
  rcases hTransfer with
    ⟨_hSource, _hSubset, hDeltaDep, hGRBS, hCovered⟩
  exact grbs_implies_delta_obligation
    F g s b l source target property
    hGRBS hDeltaDep hCovered

/--
A valid delta-based transfer preserves source assurance at the target.
-/
theorem delta_based_transfer_preserves_assurance
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop)
    (hTransfer :
      DeltaBasedTransfer F g s b l source target property) :
    TargetAssured F.Dependency target property := by
  rcases hTransfer with
    ⟨hSource, _hSubset, hDeltaDep, hGRBS, hCovered⟩
  have hDelta :
      DeltaObligation F.Dependency source target property :=
    grbs_implies_delta_obligation
      F g s b l source target property
      hGRBS hDeltaDep hCovered
  exact target_assured_of_source_and_delta
    F.Dependency source target property hSource hDelta

/--
The explicit dependency-inclusion component is sufficient to recover
the R13 coverage decomposition at the domain level.
-/
theorem target_dependency_expansion
    {D : Type}
    (source target : D → Prop) :
    ∀ d, target d → source d ∨ (target d ∧ ¬ source d) := by
  intro d hd
  by_cases hs : source d
  · exact Or.inl hs
  · exact Or.inr ⟨hd, hs⟩

end GRBS.R14DeltaBasedAssuranceTransfer
