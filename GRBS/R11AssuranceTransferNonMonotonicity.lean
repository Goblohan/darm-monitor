import GRBS

namespace GRBS.R11AssuranceTransferNonMonotonicity

/-
R11 studies monotonicity of boundary sufficiency under
dependency expansion.

The question is whether a boundary sufficient for an earlier
dependency set remains sufficient when the relevant dependency
set grows.

The answer is no in general.
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
  dep := fun _ _ d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  cov := fun _ _ _ d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def g : F.Guarantee := G.g
def s : F.System := S.s
def b : F.Boundary := B.b
def l : F.Locus := L.l

/--
The original dependency set contains only d1.
-/
def Dep1 : D → Prop :=
  fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False

/--
The expanded dependency set adds d2.
-/
def Dep2 : D → Prop :=
  fun _ => True

/--
The boundary covers the original dependency set.
-/
theorem grbs_dep1 :
    ∀ d, Dep1 d → F.cov b l s d := by
  intro d hd
  cases d with
  | d1 =>
      trivial
  | d2 =>
      cases hd

/--
The original dependency set is sufficient for the boundary.
-/
theorem grbs_dep1_holds :
    ∀ d, Dep1 d → F.cov b l s d := by
  exact grbs_dep1

/--
Dependency expansion is monotone.
-/
theorem dependency_expansion :
    ∀ d, Dep1 d → Dep2 d := by
  intro d hd
  trivial

/--
The newly introduced dependency d2 is not covered.
-/
theorem d2_uncovered :
    ¬ F.cov b l s D.d2 := by
  intro h
  exact h

/--
The expanded dependency set is not boundary-sufficient.
-/
theorem grbs_dep2_fails :
    ¬ (∀ d, Dep2 d → F.cov b l s d) := by
  intro h
  exact d2_uncovered (h D.d2 trivial)

/--
Main R11 witness.

A dependency expansion can preserve inclusion while destroying
boundary sufficiency.
-/
theorem assurance_transfer_is_not_monotone_under_dependency_expansion :
    (∀ d, Dep1 d → Dep2 d) ∧
    (∀ d, Dep1 d → F.cov b l s d) ∧
    ¬ (∀ d, Dep2 d → F.cov b l s d) := by
  constructor
  · exact dependency_expansion
  constructor
  · exact grbs_dep1
  · exact grbs_dep2_fails

end GRBS.R11AssuranceTransferNonMonotonicity
