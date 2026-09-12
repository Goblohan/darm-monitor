import GRBS
import R6GRBSDeltaBridge

open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge
namespace GRBS.R7ContractRefinementSeparation

def Contract (A G : Type) := (A → Prop) × (G → Prop)

def ContractRefines
    {A G : Type}
    (c' c : Contract A G) : Prop :=
  (∀ x, c'.1 x → c.1 x) ∧
  (∀ x, c.2 x → c'.2 x)


namespace R7a

inductive Tr where
  | unit

inductive G where
  | g

inductive S where
  | s

inductive B where
  | b

inductive L where
  | l
  | good
  | bad
inductive D where
  | required

inductive E where
  | e

def F : Frame where
  Trace := Tr
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := E
  Safe := fun _ _ => True
  dep := fun _ _ d => d = D.required
  cov := fun _ l _ d =>
    l = L.good ∧ d = D.required
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => False

def g : F.Guarantee := G.g
def s : F.System := S.s
def b : F.Boundary := B.b

def l_good : F.Locus := L.good
def l_bad : F.Locus := L.bad

def contract_old : Contract Unit Unit :=
  (fun _ => True, fun _ => True)

def contract_new : Contract Unit Unit :=
  (fun _ => True, fun _ => True)

theorem contract_refinement_holds :
    ContractRefines contract_new contract_old := by
  constructor
  · intro x h
    exact h
  · intro x h
    exact h

theorem grbs_holds_at_good_locus :
    GRBS F g s b l_good := by
  intro d hd
  cases d with
  | required =>
      constructor <;> trivial

theorem grbs_fails_at_bad_locus :
    ¬ GRBS F g s b l_bad := by
  intro h
  have hd : F.dep g s D.required := by
    rfl
  have hc := h D.required hd
  cases hc.left

end R7a


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


theorem darm_transfer_preserves_assurance
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop)
    (hTransfer : DARMTransfer F g s b l source target property) :
    TargetAssured F.Dependency target property := by
  rcases hTransfer with ⟨hSource, hGRBS, hDeltaDep, hCovered⟩
  have hDelta :
      DeltaObligation F.Dependency source target property :=
    grbs_implies_delta_obligation
      F g s b l source target property
      hGRBS hDeltaDep hCovered
  exact conserving_transfer_preserves_assurance
    F.Dependency source target property hSource hDelta


namespace R7b

inductive Tr where
  | unit
  deriving DecidableEq

inductive G where
  | g
  deriving DecidableEq

inductive S where
  | s
  deriving DecidableEq

inductive B where
  | b
  deriving DecidableEq

inductive L where
  | l
  deriving DecidableEq

inductive D where
  | d
  deriving DecidableEq

inductive E where
  | e
  deriving DecidableEq

def F : Frame where
  Trace := Tr
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := E
  Safe := fun _ _ => True
  dep := fun _ _ _ => True
  cov := fun _ _ _ _ => True
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => False

def g : F.Guarantee := G.g
def s : F.System := S.s
def b : F.Boundary := B.b
def l : F.Locus := L.l

def source : F.Dependency → Prop :=
  fun _ => True

def target : F.Dependency → Prop :=
  fun _ => True

def property : F.Dependency → Prop :=
  fun _ => True

def contract_old : Contract Unit Unit :=
  (fun _ => False, fun _ => True)

def contract_new : Contract Unit Unit :=
  (fun _ => True, fun _ => True)

theorem source_assured :
    SourceAssured F.Dependency source property := by
  intro d hd
  trivial

theorem grbs_holds :
    GRBS F g s b l := by
  intro d hd
  constructor <;> trivial

theorem delta_subset_dependency :
    DeltaSubsetDependency F g s source target := by
  intro d hd
  trivial

theorem covered_discharges_property :
    CoveredDischargesProperty F g s b l property := by
  intro d hdep hcov
  trivial

theorem darm_transfer_holds :
    DARMTransfer F g s b l source target property := by
  exact ⟨
    source_assured,
    grbs_holds,
    delta_subset_dependency,
    covered_discharges_property
  ⟩

theorem contract_refinement_fails :
    ¬ ContractRefines contract_new contract_old := by
  intro h
  have hNew := h.1 ()
  exact hNew trivial

theorem darm_transfer_does_not_imply_contract_refinement :
    DARMTransfer F g s b l source target property ∧
    ¬ ContractRefines contract_new contract_old :=
  ⟨darm_transfer_holds, contract_refinement_fails⟩

end R7b

end GRBS.R7ContractRefinementSeparation
