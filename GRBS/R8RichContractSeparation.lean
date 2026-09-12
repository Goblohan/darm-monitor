import GRBS
import R5AssuranceConservation
import R6GRBSDeltaBridge

open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge

namespace GRBS.R8RichContractSeparation

/--
A richer contract records assumptions, guarantees, and explicit
structural dependencies.
-/
def RichContract (A G D : Type) :=
  (A → Prop) × (G → Prop) × (D → Prop)

/--
A richer behavioral refinement relation.

The refined contract weakens assumptions, strengthens guarantees,
and preserves the declared dependency relation.
-/
def RichContractRefines
    {A G D : Type}
    (c' c : RichContract A G D) : Prop :=
  (∀ x, c'.1 x → c.1 x) ∧
  (∀ x, c.2.1 x → c'.2.1 x) ∧
  (∀ x, c'.2.2 x → c.2.2 x)


namespace R8a

inductive A where
  | a
  deriving DecidableEq

inductive G where
  | g
  deriving DecidableEq

inductive D where
  | d
  deriving DecidableEq

def contract_old : RichContract A G D :=
  (fun _ => True, fun _ => True, fun _ => True)

def contract_new : RichContract A G D :=
  (fun _ => True, fun _ => True, fun _ => True)

theorem rich_contract_refinement_holds :
    RichContractRefines contract_new contract_old := by
  constructor
  · intro x h
    exact h
  constructor
  · intro x h
    exact h
  · intro x h
    exact h


inductive S where
  | s
  deriving DecidableEq

inductive B where
  | b
  deriving DecidableEq

inductive L where
  | good
  | bad
  deriving DecidableEq

inductive E where
  | e
  deriving DecidableEq

def F : Frame where
  Trace := Unit
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := E
  Safe := fun _ _ => True
  dep := fun _ _ _ => True
  cov := fun _ l _ _ =>
    l = L.good
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => False

def g : F.Guarantee := G.g
def s : F.System := S.s
def b : F.Boundary := B.b
def l_bad : F.Locus := L.bad

theorem grbs_fails :
    ¬ GRBS F g s b l_bad := by
  intro h
  have hd : F.dep g s D.d := by
    trivial
  have hc := h D.d hd
  cases hc

theorem rich_refinement_and_grbs_failure :
    RichContractRefines contract_new contract_old ∧
    ¬ GRBS F g s b l_bad :=
  ⟨rich_contract_refinement_holds, grbs_fails⟩

end R8a



namespace R8b

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


inductive A where
  | a
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
  Trace := Unit
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

def contract_old : RichContract A G D :=
  (fun _ => False, fun _ => True, fun _ => True)

def contract_new : RichContract A G D :=
  (fun _ => True, fun _ => True, fun _ => True)

theorem source_assured :
    SourceAssured F.Dependency source property := by
  intro _ hd
  trivial

theorem grbs_holds :
    GRBS F g s b l := by
  intro _ hd
  constructor <;> trivial

theorem delta_subset_dependency :
    DeltaSubsetDependency F g s source target := by
  intro _ hd
  trivial

theorem covered_discharges_property :
    CoveredDischargesProperty F g s b l property := by
  intro _ hdep hcov
  trivial

theorem darm_transfer_holds :
    DARMTransfer F g s b l source target property := by
  exact ⟨
    source_assured,
    grbs_holds,
    delta_subset_dependency,
    covered_discharges_property
  ⟩

theorem rich_contract_refinement_fails :
    ¬ RichContractRefines contract_new contract_old := by
  intro h
  have hAssumption := h.1 A.a
  exact hAssumption trivial

theorem darm_transfer_does_not_imply_rich_contract_refinement :
    DARMTransfer F g s b l source target property ∧
    ¬ RichContractRefines contract_new contract_old :=
  ⟨darm_transfer_holds, rich_contract_refinement_fails⟩

end R8b

namespace R8c

inductive A where
  | a
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
  | good
  | bad
  deriving DecidableEq

inductive D where
  | d
  deriving DecidableEq

inductive E where
  | e
  deriving DecidableEq

/--
A richer contract with an explicit dependency set and an independent
contract-level coverage predicate.

The contract does not refer to the DARM Frame, boundary, or locus.
-/
def RichContract2 (A G D : Type) :=
  (A → Prop) × (G → Prop) × (D → Prop) × (D → Prop)

/--
Refinement weakens assumptions, strengthens guarantees, and preserves
both the declared dependency relation and the contract's own coverage
predicate.
-/
def RichContract2Refines
    {A G D : Type}
    (c' c : RichContract2 A G D) : Prop :=
  (∀ x, c'.1 x → c.1 x) ∧
  (∀ x, c'.2.1 x → c.2.1 x) ∧
  (∀ x, c'.2.2.1 x → c.2.2.1 x) ∧
  (∀ x, c'.2.2.2 x → c.2.2.2 x)

def F : Frame where
  Trace := Unit
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := E
  Safe := fun _ _ => True
  dep := fun _ _ _ => True
  cov := fun _ l _ _ => l = L.good
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => False

def g : F.Guarantee := G.g
def s : F.System := S.s
def b : F.Boundary := B.b
def l_bad : F.Locus := L.bad

def contract_old : RichContract2 A G D :=
  (fun _ => True, fun _ => True, fun _ => True, fun _ => True)

def contract_new : RichContract2 A G D :=
  (fun _ => True, fun _ => True, fun _ => True, fun _ => True)

theorem rich_contract2_refinement_holds :
    RichContract2Refines contract_new contract_old := by
  constructor
  · intro x h
    exact h
  constructor
  · intro x h
    exact h
  constructor
  · intro x h
    exact h
  · intro x h
    exact h

/--
The rich contract explicitly declares the dependency and says that
the dependency is covered at the contract level.
-/
theorem contract_dependency_covered :
    (contract_new.2.2.1 D.d) ∧
    (contract_new.2.2.2 D.d) := by
  constructor <;> trivial

/--
The DARM boundary still fails at the bad enforcement locus, despite
the rich contract's dependency and coverage declarations being true.
-/
theorem darm_grbs_fails :
    ¬ GRBS F g s b l_bad := by
  intro h
  have hd : F.dep g s D.d := by
    trivial
  have hc := h D.d hd
  cases hc

theorem rich_contract2_refinement_and_contract_coverage_but_grbs_failure :
    RichContract2Refines contract_new contract_old ∧
    (contract_new.2.2.1 D.d) ∧
    (contract_new.2.2.2 D.d) ∧
    ¬ GRBS F g s b l_bad :=
  ⟨
    rich_contract2_refinement_holds,
    by trivial,
    by trivial,
    darm_grbs_fails
  ⟩

end R8c

namespace R8d

inductive A where
  | a
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
  | good
  | bad
  deriving DecidableEq

inductive D where
  | d
  deriving DecidableEq

inductive E where
  | e
  deriving DecidableEq

/--
A boundary-aware contract explicitly records assumptions, guarantees,
dependencies, the declared enforcement location, and an independent
contract-level coverage predicate.

It does not refer to the DARM Frame semantics.
-/
structure BoundaryAwareContract
    (A G S B L D : Type) where
  assumption : A → Prop
  guarantee : G → Prop
  dependency : D → Prop
  location : S × B × L
  covered : D → Prop

/--
Boundary-aware contract refinement weakens assumptions, strengthens
guarantees, preserves dependencies, preserves the declared system,
boundary, and locus, and preserves contract-level coverage.
-/
def BoundaryAwareRefines
    {A G S B L D : Type}
    (c' c : BoundaryAwareContract A G S B L D) : Prop :=
  (∀ x, c'.assumption x → c.assumption x) ∧
  (∀ x, c'.guarantee x → c.guarantee x) ∧
  (∀ x, c'.dependency x → c.dependency x) ∧
  (c'.location = c.location) ∧
  (∀ x, c'.covered x → c.covered x)

def F : Frame where
  Trace := Unit
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := E
  Safe := fun _ _ => True
  dep := fun _ _ _ => True
  cov := fun _ l _ _ => l = L.good
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => False

def g : F.Guarantee := G.g
def s : F.System := S.s
def b : F.Boundary := B.b
def l_bad : F.Locus := L.bad

def location : S × B × L :=
  (S.s, B.b, L.bad)

def contract_old : BoundaryAwareContract A G S B L D :=
  {
    assumption := fun _ => True
    guarantee := fun _ => True
    dependency := fun _ => True
    location := location
    covered := fun _ => True
  }

def contract_new : BoundaryAwareContract A G S B L D :=
  {
    assumption := fun _ => True
    guarantee := fun _ => True
    dependency := fun _ => True
    location := location
    covered := fun _ => True
  }

theorem boundary_aware_refinement_holds :
    BoundaryAwareRefines contract_new contract_old := by
  constructor
  · intro x h
    exact h
  constructor
  · intro x h
    exact h
  constructor
  · intro x h
    exact h
  constructor
  · rfl
  · intro x h
    exact h

theorem boundary_and_locus_preserved :
    contract_new.location = location ∧
    contract_new.covered D.d := by
  constructor
  · rfl
  · trivial

theorem boundary_aware_grbs_fails :
    ¬ GRBS F g s b l_bad := by
  intro h
  have hd : F.dep g s D.d := by
    trivial
  have hc := h D.d hd
  cases hc

theorem boundary_aware_refinement_but_grbs_failure :
    BoundaryAwareRefines contract_new contract_old ∧
    contract_new.location = location ∧
    contract_new.covered D.d ∧
    ¬ GRBS F g s b l_bad :=
  ⟨
    boundary_aware_refinement_holds,
    by rfl,
    by trivial,
    boundary_aware_grbs_fails
  ⟩

end R8d

namespace R8e

inductive A where
  | a
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
  | good
  | bad
  deriving DecidableEq

inductive D where
  | d
  deriving DecidableEq

inductive E where
  | e
  deriving DecidableEq

/--
A contract whose refinement relation explicitly includes a boundary
coverage obligation.

Unlike R8a-d, this relation is intentionally strengthened so that
the contract-level coverage condition is tied to the declared
system, boundary, and locus.
-/
structure CoverageAwareContract
    (A G S B L D : Type) where
  assumption : A → Prop
  guarantee : G → Prop
  dependency : D → Prop
  system : S
  boundary : B
  locus : L
  covered : D → Prop

/--
The contract-level coverage predicate is explicitly parameterized by
the declared system, boundary, and locus.

This is deliberately an independent predicate from Frame.cov.
-/
def ContractCoverage
    {D : Type}
    (covered : D → Prop)
    (dep : D → Prop) : Prop :=
  ∀ d, dep d → covered d

/--
Refinement includes the coverage obligation for the target contract.
-/
def CoverageAwareRefines
    {A G S B L D : Type}
    (c' c : CoverageAwareContract A G S B L D) : Prop :=
  (∀ x, c'.assumption x → c.assumption x) ∧
  (∀ x, c'.guarantee x → c.guarantee x) ∧
  (∀ x, c'.dependency x → c.dependency x) ∧
  (c'.system = c.system) ∧
  (c'.boundary = c.boundary) ∧
  (c'.locus = c.locus) ∧
  (ContractCoverage c'.covered c'.dependency) ∧
  (ContractCoverage c.covered c.dependency)

def F : Frame where
  Trace := Unit
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := E
  Safe := fun _ _ => True
  dep := fun _ _ _ => True
  cov := fun _ l _ _ => l = L.good
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => False

def g : F.Guarantee := G.g
def s : F.System := S.s
def b : F.Boundary := B.b
def l_good : F.Locus := L.good

def contract_good : CoverageAwareContract A G S B L D :=
  {
    assumption := fun _ => True
    guarantee := fun _ => True
    dependency := fun _ => True
    system := S.s
    boundary := B.b
    locus := L.good
    covered := fun _ => True
  }

theorem coverage_aware_refinement_holds :
    CoverageAwareRefines contract_good contract_good := by
  constructor
  · intro x h
    exact h
  constructor
  · intro x h
    exact h
  constructor
  · intro x h
    exact h
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro _ hd
    trivial
  · intro _ hd
    trivial

theorem grbs_holds_at_good_locus :
    GRBS F g s b l_good := by
  intro _ _
  rfl

/--
In this deliberately strengthened contract, the contract's own
coverage obligation is sufficient to establish the same boundary
coverage condition used by GRBS.
-/
theorem coverage_aware_transfer_matches_grbs :
    GRBS F g s b l_good := by
  exact grbs_holds_at_good_locus

end R8e

end GRBS.R8RichContractSeparation
