import DARMCoreCalculus

namespace GRBS.DCEE6AConcreteContractNormalization

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge
open GRBS.DARMCoreCalculus

/-!
DCEE-6A: Concrete Contract Normalization

Purpose:
  Test whether a concrete assume-guarantee contract representation can
  normalize into the backend-neutral SourceAssured interface used by DARM.

The experiment does NOT claim that DARM is more expressive than contracts.
It tests whether contract-specific validity can be separated from the
subsequent assurance-transfer judgment.
-/

structure Contract (D : Type) where
  assumption : D → Prop
  guarantee : D → Prop

def ContractValid {D : Type} (c : Contract D) : Prop :=
  ∀ d, c.assumption d → c.guarantee d

def ContractRefines {D : Type} (c' c : Contract D) : Prop :=
  (∀ d, c'.assumption d → c.assumption d) ∧
  (∀ d, c'.guarantee d → c.guarantee d)

def ContractSourceAssured
    {D : Type}
    (c : Contract D) : Prop :=
  SourceAssured D c.assumption c.guarantee

def NormalizeContract
    {D : Type}
    (c : Contract D) :
    D → Prop :=
  c.assumption

theorem contract_valid_normalizes_to_source_assurance
    {D : Type}
    (c : Contract D)
    (hValid : ContractValid c) :
    ContractSourceAssured c := by
  intro d hd
  exact hValid d hd

theorem normalized_contract_is_definitionally_source_assurance
    {D : Type}
    (c : Contract D) :
    ContractSourceAssured c ↔
    SourceAssured D c.assumption c.guarantee := by
  rfl

inductive D
  | d1
  | d2

def sourceContract : Contract D where
  assumption := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  guarantee := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False

def targetDependency : D → Prop
  | D.d1 => True
  | D.d2 => True

def targetCoverage : D → Prop
  | D.d1 => True
  | D.d2 => True

def targetDischarge : D → Prop
  | D.d1 => True
  | D.d2 => True

theorem source_contract_valid :
    ContractValid sourceContract := by
  intro d hd
  cases d <;> simp [sourceContract] at *

theorem source_contract_assured :
    ContractSourceAssured sourceContract := by
  exact contract_valid_normalizes_to_source_assurance
    sourceContract
    source_contract_valid

theorem normalized_contract_preserves_source_assurance :
    ContractSourceAssured sourceContract ↔
    SourceAssured D
      sourceContract.assumption
      sourceContract.guarantee := by
  exact normalized_contract_is_definitionally_source_assurance
    sourceContract

structure TransferContext where
  source : D → Prop
  target : D → Prop
  dependency : D → Prop
  covered : D → Prop
  discharged : D → Prop

def TransferContextValid
    (t : TransferContext) : Prop :=
  (∀ d, t.target d → t.dependency d) ∧
  (∀ d, t.target d → t.covered d) ∧
  (∀ d, t.target d → t.discharged d)

def transferContext : TransferContext where
  source := sourceContract.assumption
  target := targetDependency
  dependency := targetDependency
  covered := targetCoverage
  discharged := targetDischarge

theorem transfer_context_valid :
    TransferContextValid transferContext := by
  constructor
  · intro d hd
    exact hd
  · constructor
    · intro d hd
      exact hd
    · intro d hd
      exact hd

theorem contract_assurance_and_transfer_are_separate :
    ContractSourceAssured sourceContract ∧
    TransferContextValid transferContext := by
  constructor
  · exact source_contract_assured
  · exact transfer_context_valid

end GRBS.DCEE6AConcreteContractNormalization

namespace GRBS
namespace GeneralTransferTheorems

open R5AssuranceConservation
open R6GRBSDeltaBridge
open DARMCoreCalculus

theorem admissible_transfer_implies_grbs
    {F : Frame}
    {g : F.Guarantee}
    {s : F.System}
    {b : F.Boundary}
    {l : F.Locus}
    {candidate : DARMCoreCalculus.TransferCandidate F.Dependency} :
    DARMCoreCalculus.DARMTransferAdmissible
        F g s b l candidate →
    GRBS F g s b l := by
  intro h
  exact h.2.1

theorem uncovered_target_dependency_blocks_grbs
    {F : Frame}
    {g : F.Guarantee}
    {s : F.System}
    {b : F.Boundary}
    {l : F.Locus}
    {target : F.Dependency → Prop}
    (d : F.Dependency)
    (hTarget : target d)
    (hRepresents : target d → F.dep g s d)
    (hUncovered : ¬ F.cov b l s d) :
    ¬ GRBS F g s b l := by
  intro hGRBS
  have hCovered : F.cov b l s d :=
    hGRBS d (hRepresents hTarget)
  exact hUncovered hCovered

theorem uncovered_target_dependency_blocks_transfer
    {F : Frame}
    {g : F.Guarantee}
    {s : F.System}
    {b : F.Boundary}
    {l : F.Locus}
    {candidate : DARMCoreCalculus.TransferCandidate F.Dependency}
    (d : F.Dependency)
    (hTarget : candidate.target d)
    (hRepresents : candidate.target d → F.dep g s d)
    (hUncovered : ¬ F.cov b l s d) :
    ¬ DARMCoreCalculus.DARMTransferAdmissible
        F g s b l candidate := by
  intro hTransfer
  have hGRBS : GRBS F g s b l :=
    admissible_transfer_implies_grbs hTransfer
  have hBlocked : ¬ GRBS F g s b l :=
    uncovered_target_dependency_blocks_grbs
      (g := g)
      d hTarget hRepresents hUncovered
  exact hBlocked hGRBS

end GeneralTransferTheorems
end GRBS
