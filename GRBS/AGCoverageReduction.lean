import GRBS
import SeL4GRBS

namespace GRBS
namespace AGCoverageReduction

/--
The AG assumption obtained by explicitly encoding DARM's
guarantee-relative coverage obligation.
-/
def CoverageAGAssumption
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus) : Prop :=
  ∀ d, F.dep g s d → F.cov b l s d

/--
GRBS is definitionally identical to the coverage-encoded AG assumption.
-/
theorem coverageAG_iff_grbs
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus) :
    CoverageAGAssumption F g s b l ↔
      GRBS F g s b l := by
  rfl

open GRBS.SeL4GRBS

/--
The concrete SysB system fails the coverage-encoded AG assumption
because its guarantee-relevant DMA dependency is uncovered.
-/
theorem coverageAG_rejects_SysB :
    ¬ CoverageAGAssumption
        GRBS.SeL4GRBS.F
        GRBS.SeL4GRBS.g
        GRBS.SeL4GRBS.SysB
        GRBS.SeL4GRBS.b
        GRBS.SeL4GRBS.l := by
  intro h
  exact GRBS.SeL4GRBS.dma_uncovered_B
    (h GRBS.SeL4GRBS.Dependency.dma
      GRBS.SeL4GRBS.SysB_dma_dependency)

/--
The concrete SysC system satisfies the coverage-encoded AG assumption.
Its two possible dependency constructors are both covered.
-/
theorem coverageAG_accepts_SysC :
    CoverageAGAssumption
        GRBS.SeL4GRBS.F
        GRBS.SeL4GRBS.g
        GRBS.SeL4GRBS.SysC
        GRBS.SeL4GRBS.b
        GRBS.SeL4GRBS.l := by
  intro d hDep
  cases d with
  | cap =>
      exact GRBS.SeL4GRBS.cap_covered_C
  | dma =>
      exact GRBS.SeL4GRBS.dma_covered_C

end AGCoverageReduction
end GRBS

#print axioms GRBS.AGCoverageReduction.coverageAG_iff_grbs
#print axioms GRBS.AGCoverageReduction.coverageAG_rejects_SysB
#print axioms GRBS.AGCoverageReduction.coverageAG_accepts_SysC
