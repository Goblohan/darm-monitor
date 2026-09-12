import DARMCoreCalculus

namespace GRBS.DCEE8TransferVsContractRefinement

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge
open GRBS.DARMCoreCalculus

/-!
DCEE-8: Transfer Judgment vs Contract Refinement

Purpose:
  Test whether ordinary contract refinement is sufficient to establish
  assurance transfer across a changed dependency/boundary context.

The experiment deliberately separates:
  1. contract refinement,
  2. source assurance,
  3. target dependency representation,
  4. boundary coverage,
  5. semantic discharge.

The key negative case asks whether contract refinement can succeed while
DARM transfer fails because a newly introduced target dependency is not
covered by the enforcement boundary.

The experiment does NOT claim that sufficiently enriched contracts cannot
represent this condition. DCEE-7 already demonstrates that they can.
The question here is whether ordinary refinement, without an explicit
transfer obligation, is enough.
-/

structure Contract (D : Type) where
  assumption : D → Prop
  guarantee : D → Prop

def ContractRefines
    {D : Type}
    (new old : Contract D) : Prop :=
  (∀ d, new.assumption d → old.assumption d) ∧
  (∀ d, new.guarantee d → old.guarantee d)

def ContractValid
    {D : Type}
    (c : Contract D) : Prop :=
  ∀ d, c.assumption d → c.guarantee d

inductive D
  | d1
  | d2

inductive G
  | g

inductive S
  | s

inductive B
  | weak
  | strong

inductive L
  | weak
  | strong

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
    | B.weak, L.weak, D.d1 => True
    | B.weak, L.weak, D.d2 => False
    | B.strong, L.strong, D.d1 => True
    | B.strong, L.strong, D.d2 => True
    | _, _, _ => False
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def source : D → Prop
  | D.d1 => True
  | D.d2 => False

def target : D → Prop
  | D.d1 => True
  | D.d2 => True

def property : D → Prop := fun _ => True

def oldContract : Contract D where
  assumption := fun _ => True
  guarantee := property

def newContract : Contract D where
  assumption := fun _ => True
  guarantee := property

theorem old_contract_valid :
    ContractValid oldContract := by
  intro d hd
  cases d <;> trivial

theorem new_contract_valid :
    ContractValid newContract := by
  intro d hd
  cases d <;> trivial

theorem contract_refinement_holds :
    ContractRefines newContract oldContract := by
  constructor
  · intro d hd
    cases d
    · exact hd
    · trivial
  · intro d hd
    trivial

theorem source_assurance_holds :
    SourceAssured D source property := by
  intro d hd
  cases d
  · trivial
  · contradiction

def candidate :
    TransferCandidate F.Dependency where
  source := source
  target := target
  property := property

theorem target_dependency_d2_is_represented :
    target D.d2 → F.dep G.g S.s D.d2 := by
  intro hd
  trivial

theorem weak_boundary_d2_is_uncovered :
    ¬ F.cov B.weak L.weak S.s D.d2 := by
  simp [F]

theorem weak_boundary_grbs_fails :
    ¬ GRBS F G.g S.s B.weak L.weak := by
  intro h
  have hCovered : F.cov B.weak L.weak S.s D.d2 :=
    h D.d2 (target_dependency_d2_is_represented trivial)
  exact weak_boundary_d2_is_uncovered hCovered

theorem weak_boundary_transfer_fails :
    ¬ DARMTransferAdmissible
      F G.g S.s B.weak L.weak candidate := by
  intro h
  exact weak_boundary_grbs_fails h.2.1

theorem strong_boundary_grbs_holds :
    GRBS F G.g S.s B.strong L.strong := by
  intro d hd
  cases d <;> trivial

theorem strong_boundary_transfer_holds :
    DARMTransferAdmissible
      F G.g S.s B.strong L.strong candidate := by
  constructor
  · intro d hd
    cases d <;> trivial
  · constructor
    · exact strong_boundary_grbs_holds
    · intro d hd hCovered
      cases d <;> trivial

theorem refinement_survives_while_weak_transfer_fails :
    ContractRefines newContract oldContract ∧
    ¬ DARMTransferAdmissible
      F G.g S.s B.weak L.weak candidate := by
  constructor
  · exact contract_refinement_holds
  · exact weak_boundary_transfer_fails

theorem refinement_and_strong_transfer_both_hold :
    ContractRefines newContract oldContract ∧
    DARMTransferAdmissible
      F G.g S.s B.strong L.strong candidate := by
  constructor
  · exact contract_refinement_holds
  · exact strong_boundary_transfer_holds

theorem refinement_does_not_determine_transfer :
    ContractRefines newContract oldContract ∧
    ¬ DARMTransferAdmissible
      F G.g S.s B.weak L.weak candidate ∧
    DARMTransferAdmissible
      F G.g S.s B.strong L.strong candidate := by
  constructor
  · exact contract_refinement_holds
  · constructor
    · exact weak_boundary_transfer_fails
    · exact strong_boundary_transfer_holds

end GRBS.DCEE8TransferVsContractRefinement
