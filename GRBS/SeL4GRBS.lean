import GRBS

namespace GRBS.SeL4GRBS

/-!
  Stage II-A: Guarantee-relative seL4 authority model.

  This is a Lean model structured around the R1 GRBS kernel.
  It is NOT a formal correspondence to seL4's Isabelle/HOL model.

  The purpose is narrower:

    1. instantiate the actual R1 `Frame`;
    2. make dependency guarantee-relative;
    3. distinguish CSpace authority from physical DMA authority;
    4. hold CSpace/software behavior constant;
    5. show that an uncovered DMA dependency makes GRBS fail;
    6. show that adding IOMMU coverage restores GRBS.

  No claim is made here about verified correspondence to actual seL4.
-/

inductive Channel where
  | cap
  | dma
  deriving DecidableEq

inductive Env where
  | benign
  | dmaAttack
  deriving DecidableEq

inductive Trace where
  | nominal
  | dmaWrite
  deriving DecidableEq

inductive Guarantee where
  | integrity
  deriving DecidableEq

structure System where
  hasDMA : Prop
  iommu   : Prop

inductive Boundary where
  | systemBoundary
  deriving DecidableEq

inductive Locus where
  | monitor
  deriving DecidableEq

inductive Dependency where
  | cap
  | dma
  deriving DecidableEq

def F : Frame where
  Trace := Trace
  Guarantee := Guarantee
  System := System
  Boundary := Boundary
  Locus := Locus
  Dependency := Dependency
  Environment := Env

  Safe := fun _ t =>
    match t with
    | Trace.nominal => True
    | Trace.dmaWrite => False

  dep := fun _g s d =>
    match d with
    | Dependency.cap => True
    | Dependency.dma => s.hasDMA

  cov := fun _b _l s d =>
    match d with
    | Dependency.cap => True
    | Dependency.dma => s.iommu

  Envs := fun _b e =>
    match e with
    | Env.benign => True
    | Env.dmaAttack => True

  Traces := fun _s _e _b t =>
    match t with
    | Trace.nominal => True
    | Trace.dmaWrite => False

  Perturbs := fun t d =>
    match t, d with
    | Trace.dmaWrite, Dependency.dma => True
    | _, _ => False

abbrev g : F.Guarantee := Guarantee.integrity

def b : F.Boundary :=
  Boundary.systemBoundary

def l : F.Locus :=
  Locus.monitor

def SysA : F.System :=
  { hasDMA := False
    iommu   := False }

def SysB : F.System :=
  { hasDMA := True
    iommu   := False }

def SysC : F.System :=
  { hasDMA := True
    iommu   := True }

theorem SysA_dma_not_dependency :
    ¬ F.dep g SysA Dependency.dma := by
  simp [F, SysA]

theorem SysB_dma_dependency :
    F.dep g SysB Dependency.dma := by
  simp [F, SysB]

theorem SysC_dma_dependency :
    F.dep g SysC Dependency.dma := by
  simp [F, SysC]

theorem cap_covered_A :
    F.cov b l SysA Dependency.cap := by
  simp [F, b, l, SysA]

theorem cap_covered_B :
    F.cov b l SysB Dependency.cap := by
  simp [F, b, l, SysB]

theorem cap_covered_C :
    F.cov b l SysC Dependency.cap := by
  simp [F, b, l, SysC]

theorem dma_uncovered_B :
    ¬ F.cov b l SysB Dependency.dma := by
  simp [F, b, l, SysB]

theorem dma_covered_C :
    F.cov b l SysC Dependency.dma := by
  simp [F, b, l, SysC]

theorem GRBS_SysA :
    GRBS F g SysA b l := by
  intro d hdep
  cases d with
  | cap =>
      simp [F, b, l, SysA]
  | dma =>
      exact False.elim (SysA_dma_not_dependency hdep)

theorem not_GRBS_SysB :
    ¬ GRBS F g SysB b l := by
  intro h
  have hdep : F.dep g SysB Dependency.dma :=
    SysB_dma_dependency
  have hcov : F.cov b l SysB Dependency.dma :=
    h Dependency.dma hdep
  exact dma_uncovered_B hcov

theorem GRBS_SysC :
    GRBS F g SysC b l := by
  intro d hdep
  cases d with
  | cap =>
      simp [F, b, l, SysC]
  | dma =>
      exact dma_covered_C

theorem cspace_dependency_identical :
    F.dep g SysA Dependency.cap ∧
    F.dep g SysB Dependency.cap ∧
    F.dep g SysC Dependency.cap := by
  simp [F, SysA, SysB, SysC]

theorem cspace_coverage_identical :
    F.cov b l SysA Dependency.cap ∧
    F.cov b l SysB Dependency.cap ∧
    F.cov b l SysC Dependency.cap := by
  simp [F, b, l, SysA, SysB, SysC]

theorem authority_topology_BC_identical :
    ∀ d, F.dep g SysB d ↔ F.dep g SysC d := by
  intro d
  cases d <;> simp [F, SysB, SysC]

theorem dma_dependency_BC_identical :
    F.dep g SysB Dependency.dma ∧
    F.dep g SysC Dependency.dma := by
  exact ⟨SysB_dma_dependency, SysC_dma_dependency⟩

theorem dma_coverage_BC_differs :
    ¬ F.cov b l SysB Dependency.dma ∧
    F.cov b l SysC Dependency.dma := by
  exact ⟨dma_uncovered_B, dma_covered_C⟩

theorem guarantee_relative_separation :
    GRBS F g SysA b l ∧
    ¬ GRBS F g SysB b l ∧
    GRBS F g SysC b l := by
  exact ⟨GRBS_SysA, not_GRBS_SysB, GRBS_SysC⟩

theorem iommu_does_not_remove_dependency :
    F.dep g SysB Dependency.dma ∧
    F.dep g SysC Dependency.dma := by
  exact ⟨SysB_dma_dependency, SysC_dma_dependency⟩

theorem iommu_repairs_GRBS :
    ¬ GRBS F g SysB b l ∧
    GRBS F g SysC b l := by
  exact ⟨not_GRBS_SysB, GRBS_SysC⟩

end GRBS.SeL4GRBS
