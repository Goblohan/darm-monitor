import GRBS
import R5AssuranceConservation
open GRBS.R5AssuranceConservation

namespace GRBS.R6GRBSDeltaBridge

/--
Every object introduced by the assurance transformation must be represented
as a structural dependency of the guarantee.
-/
def DeltaSubsetDependency
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (source target : F.Dependency → Prop) : Prop :=
  ∀ d, Delta F.Dependency source target d → F.dep g s d

/--
Coverage of a guarantee-relative structural dependency must be sufficient
to establish the property required by the assurance delta.
-/
def CoveredDischargesProperty
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (property : F.Dependency → Prop) : Prop :=
  ∀ d, F.dep g s d → F.cov b l s d → property d

/--
GRBS plus the two explicit bridge conditions discharges the R5 delta
obligation.
-/
theorem grbs_implies_delta_obligation
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop)
    (hGRBS : GRBS F g s b l)
    (hDeltaDep : DeltaSubsetDependency F g s source target)
    (hCovered : CoveredDischargesProperty F g s b l property) :
    DeltaObligation F.Dependency source target property := by
  intro d hd
  exact hCovered d (hDeltaDep d hd) (hGRBS d (hDeltaDep d hd))

section Counterexample

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

inductive E where
  | e
  deriving DecidableEq

inductive D where
  | x
  deriving DecidableEq

/--
R6b.1

GRBS may hold vacuously while the assurance delta contains an object that is
not represented in the structural dependency relation.
-/
def F_unrepresented : Frame where
  Trace := Tr
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := E
  Safe := fun _ _ => True
  dep := fun _ _ _ => False
  cov := fun _ _ _ _ => False
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => False

def g_unrepresented : F_unrepresented.Guarantee := G.g
def s_unrepresented : F_unrepresented.System := S.s
def b_unrepresented : F_unrepresented.Boundary := B.b
def l_unrepresented : F_unrepresented.Locus := L.l

def source_unrepresented :
    F_unrepresented.Dependency → Prop :=
  fun _ => False

def target_unrepresented :
    F_unrepresented.Dependency → Prop :=
  fun _ => True

def property_unrepresented :
    F_unrepresented.Dependency → Prop :=
  fun _ => False

theorem grbs_holds_unrepresented :
    GRBS
      F_unrepresented
      g_unrepresented
      s_unrepresented
      b_unrepresented
      l_unrepresented := by
  intro d hd
  exact False.elim hd

theorem delta_contains_unrepresented :
    Delta
      F_unrepresented.Dependency
      source_unrepresented
      target_unrepresented
      D.x := by
  constructor
  · trivial
  · intro h
    exact h

theorem delta_obligation_fails_unrepresented :
    ¬ DeltaObligation
      F_unrepresented.Dependency
      source_unrepresented
      target_unrepresented
      property_unrepresented := by
  intro h
  exact h D.x delta_contains_unrepresented

theorem grbs_does_not_imply_delta_obligation :
    GRBS
      F_unrepresented
      g_unrepresented
      s_unrepresented
      b_unrepresented
      l_unrepresented
    ∧
    ¬ DeltaObligation
      F_unrepresented.Dependency
      source_unrepresented
      target_unrepresented
      property_unrepresented :=
  ⟨
    grbs_holds_unrepresented,
    delta_obligation_fails_unrepresented
  ⟩

/--
R6b.2

Even if every delta object is a structural dependency and GRBS therefore
covers it, coverage alone need not establish the property required by R5.
This isolates the second bridge condition.
-/
def F_covered_but_insufficient : Frame where
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

def g_covered : F_covered_but_insufficient.Guarantee := G.g
def s_covered : F_covered_but_insufficient.System := S.s
def b_covered : F_covered_but_insufficient.Boundary := B.b
def l_covered : F_covered_but_insufficient.Locus := L.l

def source_covered :
    F_covered_but_insufficient.Dependency → Prop :=
  fun _ => False

def target_covered :
    F_covered_but_insufficient.Dependency → Prop :=
  fun _ => True

def property_covered :
    F_covered_but_insufficient.Dependency → Prop :=
  fun _ => False

theorem grbs_holds_covered :
    GRBS
      F_covered_but_insufficient
      g_covered
      s_covered
      b_covered
      l_covered := by
  intro d hd
  trivial

theorem delta_subset_dependency_holds :
    DeltaSubsetDependency
      F_covered_but_insufficient
      g_covered
      s_covered
      source_covered
      target_covered := by
  intro d hd
  trivial

theorem delta_contains_covered :
    Delta
      F_covered_but_insufficient.Dependency
      source_covered
      target_covered
      D.x := by
  constructor
  · trivial
  · intro h
    exact h

theorem covered_does_not_discharge_property :
    ¬ CoveredDischargesProperty
      F_covered_but_insufficient
      g_covered
      s_covered
      b_covered
      l_covered
      property_covered := by
  intro h
  exact h D.x trivial trivial

theorem delta_obligation_fails_covered :
    ¬ DeltaObligation
      F_covered_but_insufficient.Dependency
      source_covered
      target_covered
      property_covered := by
  intro h
  exact h D.x delta_contains_covered

theorem grbs_and_dependency_coverage_still_insufficient :
    GRBS
      F_covered_but_insufficient
      g_covered
      s_covered
      b_covered
      l_covered
    ∧
    DeltaSubsetDependency
      F_covered_but_insufficient
      g_covered
      s_covered
      source_covered
      target_covered
    ∧
    ¬ DeltaObligation
      F_covered_but_insufficient.Dependency
      source_covered
      target_covered
      property_covered :=
  ⟨
    grbs_holds_covered,
    delta_subset_dependency_holds,
    delta_obligation_fails_covered
  ⟩

end Counterexample

end GRBS.R6GRBSDeltaBridge
