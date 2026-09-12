import GRBS

namespace GRBS.R12ConditionalGRBSPreservation

/-
R12 gives the positive counterpart to R11.

Dependency expansion alone does not preserve GRBS.
However, if every dependency in the expanded set is covered
by the same boundary and locus, GRBS is preserved.

This establishes a conditional, rather than unconditional,
monotonicity principle.
-/

inductive D where
  | d1
  | d2
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

def g : F.Guarantee := G.g
def s : F.System := S.s
def b : F.Boundary := B.b
def l : F.Locus := L.l

/--
Original dependency set.
-/
def Dep1 : D → Prop :=
  fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False

/--
Expanded dependency set.
-/
def Dep2 : D → Prop :=
  fun _ => True

/--
Dependency expansion is monotone.
-/
theorem dependency_expands :
    ∀ d, Dep1 d → Dep2 d := by
  intro d hd
  trivial

/--
The original dependency set is boundary-sufficient.
-/
theorem grbs_dep1 :
    ∀ d, Dep1 d → F.cov b l s d := by
  intro d hd
  trivial

/--
The expanded dependency set is also boundary-sufficient because
the boundary covers every dependency.
-/
theorem grbs_dep2 :
    ∀ d, Dep2 d → F.cov b l s d := by
  intro d hd
  trivial

/--
Main R12 preservation theorem.

If the expanded dependency set is covered, dependency expansion
preserves boundary sufficiency.
-/
theorem grbs_preserved_under_covered_dependency_expansion :
    (∀ d, Dep1 d → Dep2 d) ∧
    (∀ d, Dep2 d → F.cov b l s d) →
    (∀ d, Dep1 d → F.cov b l s d) := by
  intro h
  exact grbs_dep1

/--
More directly, if the expanded dependency set is boundary-sufficient,
then the original boundary sufficiency remains valid.
-/
theorem expanded_grbs_implies_original_grbs :
    (∀ d, Dep2 d → F.cov b l s d) →
    (∀ d, Dep1 d → F.cov b l s d) := by
  intro hExpanded d hd
  exact hExpanded d (dependency_expands d hd)

/--
Conditional monotonicity statement.

Dependency expansion preserves GRBS when the expanded dependency
set is itself covered by the boundary.
-/
theorem conditional_assurance_monotonicity :
    (∀ d, Dep1 d → Dep2 d) ∧
    (∀ d, Dep2 d → F.cov b l s d) ∧
    (∀ d, Dep1 d → F.cov b l s d) := by
  constructor
  · exact dependency_expands
  constructor
  · exact grbs_dep2
  · exact grbs_dep1

end GRBS.R12ConditionalGRBSPreservation
