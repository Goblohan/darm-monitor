import DarmMonitor.Basic
import GRBS
import SeL4GRBS

namespace GRBS.BasicGRBSBridge

open GRBS.SeL4GRBS

theorem capability_confinement
    {CapId ActionId : Type}
    [DecidableEq CapId]
    [DecidableEq ActionId]
    {reqs : ActionId → CapId}
    {allowedCapLimit : Finset CapId}
    {s : State CapId ActionId}
    {a : ActionId}
    (hCap : capInvariant allowedCapLimit s)
    (hExec : canExecute reqs s a) :
    reqs a ∈ allowedCapLimit :=
  execution_confined_by_cap_bound
    (s := s)
    (a := a)
    hCap
    hExec

theorem represented_dependency_is_bounded
    {CapId ActionId : Type}
    [DecidableEq CapId]
    [DecidableEq ActionId]
    {reqs : ActionId → CapId}
    {allowedCapLimit : Finset CapId}
    {s : State CapId ActionId}
    {d : CapId}
    (hCap : capInvariant allowedCapLimit s)
    (hRep :
      ∃ a, reqs a = d ∧ canExecute reqs s a) :
    d ∈ allowedCapLimit := by
  obtain ⟨a, ha, hExec⟩ := hRep
  have hBound := capability_confinement hCap hExec
  simpa [ha] using hBound


/--
The capability dependency is covered in SysB.
-/
theorem cspace_bridge_B :
    F.cov b l SysB Dependency.cap := by
  exact cap_covered_B

/--
The DMA dependency is not established by the capability bridge.
SysB contains a guarantee-relevant DMA dependency, but that dependency
is uncovered.
-/
theorem dma_remains_uncovered_B :
    F.dep g SysB Dependency.dma ∧
    ¬ F.cov b l SysB Dependency.dma := by
  exact ⟨SysB_dma_dependency, dma_uncovered_B⟩

/--
Capability coverage of the CSpace dependency does not imply GRBS for SysB.

SysB has an additional guarantee-relevant DMA dependency that remains
uncovered.
-/
theorem capability_coverage_not_grbs_B :
    F.cov b l SysB Dependency.cap ∧
    F.dep g SysB Dependency.dma ∧
    ¬ F.cov b l SysB Dependency.dma := by
  exact ⟨cap_covered_B, SysB_dma_dependency, dma_uncovered_B⟩

/--
The existing seL4 GRBS model therefore rejects transfer for SysB even
though its capability dependency is covered.
-/
theorem capability_covered_but_grbs_fails_B :
    F.cov b l SysB Dependency.cap ∧
    ¬ GRBS F g SysB b l := by
  exact ⟨cap_covered_B, not_GRBS_SysB⟩

/--
The repaired system SysC covers both the CSpace and DMA dependencies.
The capability-side result is therefore compatible with full GRBS once
the additional physical authority is explicitly covered.
-/
theorem capability_and_dma_covered_C :
    F.cov b l SysC Dependency.cap ∧
    F.cov b l SysC Dependency.dma ∧
    GRBS F g SysC b l := by
  exact ⟨cap_covered_C, dma_covered_C, GRBS_SysC⟩

end GRBS.BasicGRBSBridge

#print axioms GRBS.BasicGRBSBridge.capability_confinement
#print axioms GRBS.BasicGRBSBridge.represented_dependency_is_bounded
#print axioms GRBS.BasicGRBSBridge.cspace_bridge_B
#print axioms GRBS.BasicGRBSBridge.dma_remains_uncovered_B
#print axioms GRBS.BasicGRBSBridge.capability_coverage_not_grbs_B
#print axioms GRBS.BasicGRBSBridge.capability_covered_but_grbs_fails_B
#print axioms GRBS.BasicGRBSBridge.capability_and_dma_covered_C
