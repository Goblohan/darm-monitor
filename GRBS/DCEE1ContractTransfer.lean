/-
DCEE-1A: Contract Refinement vs DARM Transfer

This is an experimental comparison module.

Research question:
  Can ordinary contract refinement hold while DARM transfer
  is inadmissible because the target introduces an uncovered
  assurance-relevant dependency?

The experiment does not claim that richer contract formalisms
cannot represent the same information.
-/

import DARMCoreCalculus

namespace GRBS.DCEE1ContractTransfer

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.DARMCoreCalculus

/-- Level 1: ordinary assumption/guarantee contract. -/
structure Contract (D : Type) where
  assumption : D → Prop
  guarantee : D → Prop

/-- Ordinary contract refinement. -/
def ContractRefines
    {D : Type}
    (cPrime c : Contract D) : Prop :=
  (∀ d, cPrime.assumption d → c.assumption d) ∧
  (∀ d, cPrime.guarantee d → c.guarantee d)


namespace GRBS.DCEE1ContractTransfer

/-- A candidate assurance transfer: source and target dependency sets,
    together with the property that must be discharged. -/
structure TransferCandidate (D : Type) where
  source : D → Prop
  target : D → Prop
  property : D → Prop

/-- The three structural obligations used by the DARM transfer analysis. -/
def DeltaRepresented
    (F : Frame) (g : F.Guarantee) (s : F.System)
    (candidate : TransferCandidate F.Dependency) : Prop :=
  GRBS.R6GRBSDeltaBridge.DeltaSubsetDependency
    F g s candidate.source candidate.target

/-- Boundary coverage of the dependencies required by the guarantee. -/
def DeltaCovered
    (F : Frame) (g : F.Guarantee) (s : F.System) (b : F.Boundary)
    (l : F.Locus) : Prop :=
  GRBS F g s b l

/-- Semantic discharge of the dependencies covered by the boundary. -/
def DeltaDischarged
    (F : Frame) (g : F.Guarantee) (s : F.System) (b : F.Boundary)
    (l : F.Locus) (candidate : TransferCandidate F.Dependency) : Prop :=
  GRBS.R6GRBSDeltaBridge.CoveredDischargesProperty
    F g s b l candidate.property

/-- DARM transfer admissibility at Level 1. -/
def DARMTransferAdmissible
    (F : Frame) (g : F.Guarantee) (s : F.System) (b : F.Boundary)
    (l : F.Locus) (candidate : TransferCandidate F.Dependency) : Prop :=
  DeltaRepresented F g s candidate ∧
  DeltaCovered F g s b l ∧
  DeltaDischarged F g s b l candidate

end GRBS.DCEE1ContractTransfer


namespace Level1Counterexample

inductive D
  | d1
  | d2

inductive G
  | g

inductive S
  | s

inductive B
  | b

inductive L
  | l

def F : Frame where
  Trace := Unit
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := Unit
  Safe := fun _ _ => True
  dep := fun _ _ d =>
    match d with
    | D.d1 => True
    | D.d2 => True
  cov := fun _ _ _ d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def candidate : GRBS.DCEE1ContractTransfer.TransferCandidate F.Dependency where
  source := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  target := fun _ => True
  property := fun _ => True

def contract_old : Contract F.Dependency where
  assumption := fun _ => True
  guarantee := fun _ => True

def contract_new : Contract F.Dependency where
  assumption := fun _ => True
  guarantee := fun _ => True

theorem contract_refinement_holds :
    ContractRefines contract_new contract_old := by
  constructor <;> intro d hd <;> trivial

theorem source_assurance_holds :
    SourceAssured F.Dependency candidate.source candidate.property := by
  intro d hd
  trivial

theorem target_dependency_is_introduced :
    GRBS.R5AssuranceConservation.Delta
      F.Dependency candidate.source candidate.target D.d2 := by
  constructor
  · trivial
  · intro h
    cases h

theorem target_dependency_is_uncovered :
    ¬ F.cov B.b L.l S.s D.d2 := by
  simp [F]

theorem darm_transfer_fails :
    ¬ GRBS.DCEE1ContractTransfer.DARMTransferAdmissible
      F G.g S.s B.b L.l candidate := by
  intro h
  rcases h with ⟨hRepresented, hCovered, hDischarged⟩
  exact target_dependency_is_uncovered
    (hCovered D.d2 (by simp [F]))

theorem contract_refinement_survives_but_darm_transfer_fails :
    ContractRefines contract_new contract_old ∧
    SourceAssured F.Dependency candidate.source candidate.property ∧
    ¬ GRBS.DCEE1ContractTransfer.DARMTransferAdmissible
      F G.g S.s B.b L.l candidate := by
  exact ⟨
    contract_refinement_holds,
    source_assurance_holds,
    darm_transfer_fails
  ⟩

end Level1Counterexample

namespace Level1CCoverageAwareContract

/-- A contract representation that explicitly records which
    dependencies are covered and which dependency obligations
    are discharged. This is intentionally defined independently
    of DARMTransferAdmissible. -/
structure CoverageAwareContract (D : Type) where
  assumption : D → Prop
  guarantee : D → Prop
  dependency : D → Prop
  covered : D → Prop
  discharged : D → Prop

/-- A target contract is transfer-valid relative to a source
    contract when:
    1. assumptions are preserved,
    2. guarantees are preserved,
    3. every target dependency is covered,
    4. every target dependency is discharged. -/
def TransferValid
    {D : Type}
    (source target : CoverageAwareContract D) : Prop :=
  (∀ d, target.assumption d → source.assumption d) ∧
  (∀ d, target.guarantee d → source.guarantee d) ∧
  (∀ d, target.dependency d → target.covered d) ∧
  (∀ d, target.dependency d → target.discharged d)

/-- Source contract corresponding to the Level-1 source context. -/
def contract_old :
    CoverageAwareContract Level1Counterexample.F.Dependency where
  assumption := fun _ => True
  guarantee := fun _ => True
  dependency := Level1Counterexample.candidate.source
  covered := fun d =>
    Level1Counterexample.F.cov
      Level1Counterexample.B.b
      Level1Counterexample.L.l
      Level1Counterexample.S.s
      d
  discharged := fun d =>
    Level1Counterexample.candidate.property d

/-- Target contract corresponding to the expanded target context. -/
def contract_new :
    CoverageAwareContract Level1Counterexample.F.Dependency where
  assumption := fun _ => True
  guarantee := fun _ => True
  dependency := Level1Counterexample.candidate.target
  covered := fun d =>
    Level1Counterexample.F.cov
      Level1Counterexample.B.b
      Level1Counterexample.L.l
      Level1Counterexample.S.s
      d
  discharged := fun d =>
    Level1Counterexample.candidate.property d

theorem assumptions_transfer :
    ∀ d, contract_new.assumption d → contract_old.assumption d := by
  intro d h
  trivial

theorem guarantees_transfer :
    ∀ d, contract_new.guarantee d → contract_old.guarantee d := by
  intro d h
  trivial

theorem coverage_transfer_fails :
    ¬ (∀ d, contract_new.dependency d → contract_new.covered d) := by
  intro h
  have hd2 : contract_new.dependency Level1Counterexample.D.d2 := by
    trivial
  have hc2 : contract_new.covered Level1Counterexample.D.d2 :=
    h Level1Counterexample.D.d2 hd2
  exact Level1Counterexample.target_dependency_is_uncovered hc2

theorem transfer_valid_fails :
    ¬ TransferValid contract_old contract_new := by
  intro h
  exact coverage_transfer_fails h.2.2.1

theorem darm_rejects_same_witness :
    ¬ GRBS.DCEE1ContractTransfer.DARMTransferAdmissible
      Level1Counterexample.F
      Level1Counterexample.G.g
      Level1Counterexample.S.s
      Level1Counterexample.B.b
      Level1Counterexample.L.l
      Level1Counterexample.candidate :=
  Level1Counterexample.darm_transfer_fails

theorem both_formalisms_reject_uncovered_dependency :
    ¬ TransferValid contract_old contract_new ∧
    ¬ GRBS.DCEE1ContractTransfer.DARMTransferAdmissible
      Level1Counterexample.F
      Level1Counterexample.G.g
      Level1Counterexample.S.s
      Level1Counterexample.B.b
      Level1Counterexample.L.l
      Level1Counterexample.candidate := by
  exact ⟨transfer_valid_fails, darm_rejects_same_witness⟩

end Level1CCoverageAwareContract

namespace Level1DPositiveCorrespondence

inductive D
  | d1
  | d2

inductive G
  | g

inductive S
  | s

inductive B
  | b

inductive L
  | l

def F : Frame where
  Trace := Unit
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := Unit
  Safe := fun _ _ => True
  dep := fun _ _ _ => True
  cov := fun _ _ _ _ => True
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def candidate :
    GRBS.DCEE1ContractTransfer.TransferCandidate F.Dependency where
  source := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  target := fun _ => True
  property := fun _ => True

theorem darm_transfer_holds :
    GRBS.DCEE1ContractTransfer.DARMTransferAdmissible
      F G.g S.s B.b L.l candidate := by
  constructor
  · intro d h
    cases d <;> trivial
  · constructor
    · intro d hd
      trivial
    · intro d hd hcov
      trivial

def contract_old :
    Level1CCoverageAwareContract.CoverageAwareContract F.Dependency where
  assumption := fun _ => True
  guarantee := fun _ => True
  dependency := candidate.source
  covered := fun _ => True
  discharged := fun _ => True

def contract_new :
    Level1CCoverageAwareContract.CoverageAwareContract F.Dependency where
  assumption := fun _ => True
  guarantee := fun _ => True
  dependency := candidate.target
  covered := fun _ => True
  discharged := fun _ => True

theorem contract_transfer_holds :
    Level1CCoverageAwareContract.TransferValid
      contract_old contract_new := by
  constructor
  · intro d h
    trivial
  · constructor
    · intro d h
      trivial
    · constructor
      · intro d h
        trivial
      · intro d h
        trivial

theorem positive_correspondence_witness :
    GRBS.DCEE1ContractTransfer.DARMTransferAdmissible
      F G.g S.s B.b L.l candidate ∧
    Level1CCoverageAwareContract.TransferValid
      contract_old contract_new := by
  exact ⟨darm_transfer_holds, contract_transfer_holds⟩

end Level1DPositiveCorrespondence
