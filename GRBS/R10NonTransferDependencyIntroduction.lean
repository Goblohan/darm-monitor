import GRBS
import R5AssuranceConservation
import R6GRBSDeltaBridge

namespace GRBS.R10NonTransferDependencyIntroduction

open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge

/-
R10 formalizes a central DARM distinction:

  source assurance may remain valid
  while assurance transfer fails because the target
  introduces a dependency that is not covered by the
  target boundary.

The theorem is intentionally independent of the semantic
truth of the guarantee itself. It concerns admissibility
of assurance transfer.
-/

def DARMTransfer
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop) : Prop :=
  SourceAssured F.Dependency source property ∧
  GRBS F g s b l ∧
  DeltaSubsetDependency F g s source target ∧
  CoveredDischargesProperty F g s b l property

/--
A dependency is newly introduced when it is required by the
target but was not required by the source.
-/
def NewlyIntroduced
    {D : Type}
    (source target : D → Prop)
    (d : D) : Prop :=
  target d ∧ ¬ source d

/--
If a newly introduced dependency is required by the target,
but is not covered by the boundary, then GRBS fails.
-/
theorem newly_introduced_uncovered_implies_not_grbs
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (d : F.Dependency)
    (hTarget : F.dep g s d)
    (hUncovered : ¬ F.cov b l s d) :
    ¬ GRBS F g s b l := by
  intro hGRBS
  exact hUncovered (hGRBS d hTarget)

/--
Main R10 theorem.

A newly introduced dependency that is relevant to the target
and uncovered by the boundary prevents DARM transfer, even
when the source assurance is available.
-/
theorem source_assurance_does_not_survive_uncovered_dependency_introduction
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop)
    (d : F.Dependency)
    (_hSource : SourceAssured F.Dependency source property)
    (_hNew : NewlyIntroduced source target d)
    (hTargetDep : F.dep g s d)
    (hUncovered : ¬ F.cov b l s d) :
    ¬ DARMTransfer F g s b l source target property := by
  intro hTransfer
  exact hUncovered (hTransfer.2.1 d hTargetDep)

/--
The failure is specifically attributable to the introduced
dependency. The source assurance hypothesis is retained in
the theorem rather than being allowed to discharge the result
vacuously.
-/
theorem transfer_failure_is_independent_of_source_assurance
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop)
    (d : F.Dependency)
    (_hSource : SourceAssured F.Dependency source property)
    (_hNew : NewlyIntroduced source target d)
    (hTargetDep : F.dep g s d)
    (hUncovered : ¬ F.cov b l s d) :
    GRBS F g s b l → False := by
  intro hGRBS
  exact hUncovered (hGRBS d hTargetDep)

end GRBS.R10NonTransferDependencyIntroduction
