import GRBS
import R6GRBSDeltaBridge

namespace GRBS.R9ContractGRBSCorrespondence

/-
R9 studies the relationship between GRBS and an explicitly
coverage-aware contract condition.

The purpose is not to claim that GRBS is inexpressible in
contract formalisms. Instead, we characterize the conditions
under which the two become equivalent.

This separates:
  (1) representation of dependencies,
  (2) representation of boundary coverage,
  (3) the logical GRBS condition itself.
-/

def ContractCoverage
    {D : Type}
    (covered : D → Prop)
    (dep : D → Prop) : Prop :=
  ∀ d, dep d → covered d

/--
A dependency representation is faithful when its contract-level
dependency predicate agrees with the dependency predicate used
by the GRBS frame.
-/
def DependencyFaithful
    {D : Type}
    (frameDep contractDep : D → Prop) : Prop :=
  ∀ d, frameDep d ↔ contractDep d

/--
A coverage representation is faithful when its contract-level
coverage predicate agrees with the frame's boundary coverage.
-/
def CoverageFaithful
    {D : Type}
    (frameCov contractCov : D → Prop) : Prop :=
  ∀ d, frameCov d ↔ contractCov d

/--
If the contract dependency and coverage predicates faithfully
represent the frame predicates, contract coverage implies GRBS.
-/
theorem contract_coverage_implies_grbs
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (contractDep contractCov : F.Dependency → Prop)
    (hDep :
      DependencyFaithful
        (fun d => F.dep g s d)
        contractDep)
    (hCov :
      CoverageFaithful
        (fun d => F.cov b l s d)
        contractCov)
    (hContract :
      ContractCoverage contractCov contractDep) :
    GRBS F g s b l := by
  intro d hd
  have hdc : contractDep d := (hDep d).mp hd
  have hcc : contractCov d := hContract d hdc
  exact (hCov d).mpr hcc

/--
If the contract dependency and coverage predicates faithfully
represent the frame predicates, GRBS implies contract coverage.
-/
theorem grbs_implies_contract_coverage
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (contractDep contractCov : F.Dependency → Prop)
    (hDep :
      DependencyFaithful
        (fun d => F.dep g s d)
        contractDep)
    (hCov :
      CoverageFaithful
        (fun d => F.cov b l s d)
        contractCov)
    (hGRBS :
      GRBS F g s b l) :
    ContractCoverage contractCov contractDep := by
  intro d hdc
  have hd : F.dep g s d := (hDep d).mpr hdc
  have hc : F.cov b l s d := hGRBS d hd
  exact (hCov d).mp hc

/--
Main correspondence theorem.

Under faithful dependency and coverage representations,
GRBS is logically equivalent to the corresponding
coverage-aware contract condition.
-/
theorem grbs_iff_contract_coverage
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (contractDep contractCov : F.Dependency → Prop)
    (hDep :
      DependencyFaithful
        (fun d => F.dep g s d)
        contractDep)
    (hCov :
      CoverageFaithful
        (fun d => F.cov b l s d)
        contractCov) :
    GRBS F g s b l ↔ ContractCoverage contractCov contractDep := by
  constructor
  · exact grbs_implies_contract_coverage
      F g s b l contractDep contractCov hDep hCov
  · exact contract_coverage_implies_grbs
      F g s b l contractDep contractCov hDep hCov


end GRBS.R9ContractGRBSCorrespondence
