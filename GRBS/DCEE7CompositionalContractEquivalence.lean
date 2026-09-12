import DARMCoreCalculus

namespace GRBS.DCEE7CompositionalContractEquivalence

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge
open GRBS.DARMCoreCalculus

/-!
DCEE-7: Compositional Contract Equivalence

Purpose:
  Test whether an explicitly dependency/coverage/discharge-aware
  compositional contract can reproduce the same transfer judgment as DARM.

The experiment is deliberately adversarial to DARM's novelty claim.

If the enriched contract and DARM become equivalent, the result is evidence
that DARM is not more expressive than a sufficiently rich contract calculus.

The remaining question is then architectural:
  whether DARM's first-class transfer representation provides a useful
  normalization/interface independent of the assurance-production backend.
-/

structure CompositionalContract (D : Type) where
  dependency : D → Prop
  covered : D → Prop
  discharged : D → Prop

def ContractTransferValid
    {D : Type}
    (target : D → Prop)
    (c : CompositionalContract D) : Prop :=
  (∀ d, target d → c.dependency d) ∧
  (∀ d, target d → c.covered d) ∧
  (∀ d, target d → c.discharged d)

def Compose
    {D : Type}
    (left right : CompositionalContract D) :
    CompositionalContract D where
  dependency := fun d => left.dependency d ∨ right.dependency d
  covered := fun d => left.covered d ∨ right.covered d
  discharged := fun d => left.discharged d ∨ right.discharged d

inductive D
  | d1
  | d2

inductive G
  | g

inductive S
  | s

inductive B
  | composed
  | incomplete

inductive L
  | composed
  | incomplete

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
  cov := fun b l _ d =>
    match b, l, d with
    | B.composed, L.composed, D.d1 => True
    | B.composed, L.composed, D.d2 => True
    | B.incomplete, L.incomplete, D.d1 => True
    | B.incomplete, L.incomplete, D.d2 => False
    | _, _, _ => False
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def source : D → Prop
  | D.d1 => True
  | D.d2 => True

def target : D → Prop
  | D.d1 => True
  | D.d2 => True

def property : D → Prop
  | D.d1 => True
  | D.d2 => True

def candidate :
    TransferCandidate F.Dependency where
  source := source
  target := target
  property := property

def leftContract : CompositionalContract D where
  dependency := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  covered := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  discharged := property

def rightContract : CompositionalContract D where
  dependency := fun d =>
    match d with
    | D.d1 => False
    | D.d2 => True
  covered := fun d =>
    match d with
    | D.d1 => False
    | D.d2 => True
  discharged := property

def composedContract : CompositionalContract D :=
  Compose leftContract rightContract

def incompleteContract : CompositionalContract D where
  dependency := target
  covered := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  discharged := property

theorem source_assurance_holds :
    SourceAssured D source property := by
  intro d hd
  cases d <;> trivial

theorem composed_contract_transfer_holds :
    ContractTransferValid target composedContract := by
  constructor
  · intro d hd
    cases d <;> simp [composedContract, Compose, leftContract, rightContract]
  · constructor
    · intro d hd
      cases d <;> simp [composedContract, Compose, leftContract, rightContract]
    · intro d hd
      cases d <;> simp [composedContract, Compose, leftContract, rightContract, property]

theorem incomplete_contract_transfer_fails :
    ¬ ContractTransferValid target incompleteContract := by
  intro h
  have hCovered :
      incompleteContract.covered D.d2 :=
    h.2.1 D.d2 trivial
  exact hCovered

theorem darm_transfer_holds :
    DARMTransferAdmissible
      F G.g S.s B.composed L.composed candidate := by
  constructor
  · intro d hd
    cases d <;> simp [F]
  · constructor
    · intro d hd
      cases d <;> simp [F]
    · intro d hd hCovered
      cases d <;> trivial

theorem darm_transfer_fails_incomplete :
    ¬ DARMTransferAdmissible
      F G.g S.s B.incomplete L.incomplete candidate := by
  intro h
  have hCovered :
      F.cov B.incomplete L.incomplete S.s D.d2 :=
    h.2.1 D.d2 trivial
  exact hCovered

theorem compositional_contract_and_darm_agree_positive :
    ContractTransferValid target composedContract ∧
    DARMTransferAdmissible
      F G.g S.s B.composed L.composed candidate := by
  constructor
  · exact composed_contract_transfer_holds
  · exact darm_transfer_holds

theorem compositional_contract_and_darm_agree_negative :
    (¬ ContractTransferValid target incompleteContract) ∧
    (¬ DARMTransferAdmissible
      F G.g S.s B.incomplete L.incomplete candidate) := by
  constructor
  · exact incomplete_contract_transfer_fails
  · exact darm_transfer_fails_incomplete

theorem coverage_composition_is_union :
    ∀ d,
      composedContract.covered d ↔
      (leftContract.covered d ∨ rightContract.covered d) := by
  intro d
  rfl

theorem dependency_composition_is_union :
    ∀ d,
      composedContract.dependency d ↔
      (leftContract.dependency d ∨ rightContract.dependency d) := by
  intro d
  rfl

end GRBS.DCEE7CompositionalContractEquivalence
