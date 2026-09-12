import DARMCoreCalculus

namespace GRBS.DCEE6CBoundaryComposition

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge
open GRBS.DARMCoreCalculus

/-!
DCEE-6C: Boundary Composition

Purpose:
  Test whether boundary coverage composes when multiple enforcement
  boundaries jointly cover the dependency set required by a guarantee.

The experiment distinguishes:
  1. partial boundary coverage,
  2. composed coverage,
  3. complete coverage,
  4. residual uncovered dependencies.

It does NOT claim that compositional coverage is absent from existing
assurance or security formalisms. It tests the explicit transfer semantics
of composing boundary coverage.
-/

inductive D
  | d1
  | d2

inductive G
  | g

inductive S
  | s

inductive B
  | left
  | right
  | composed
  | incomplete

inductive L
  | left
  | right
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
  dep := fun _ _ d =>
    match d with
    | D.d1 => True
    | D.d2 => True
  cov := fun b l _ d =>
    match b, l, d with
    | B.left, L.left, D.d1 => True
    | B.left, L.left, D.d2 => False
    | B.right, L.right, D.d1 => False
    | B.right, L.right, D.d2 => True
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

theorem source_assurance_holds :
    SourceAssured D source property := by
  intro d hd
  cases d <;> trivial

theorem target_dependencies_are_represented :
    ∀ d, target d → F.dep G.g S.s d := by
  intro d hd
  cases d <;> trivial

theorem left_boundary_is_partial :
    F.cov B.left L.left S.s D.d1 ∧
    ¬ F.cov B.left L.left S.s D.d2 := by
  constructor
  · simp [F]
  · simp [F]

theorem right_boundary_is_partial :
    ¬ F.cov B.right L.right S.s D.d1 ∧
    F.cov B.right L.right S.s D.d2 := by
  constructor
  · simp [F]
  · simp [F]

theorem composed_boundary_covers_all :
    ∀ d, target d → F.cov B.composed L.composed S.s d := by
  intro d hd
  cases d <;> trivial

theorem composed_boundary_satisfies_grbs :
    GRBS F G.g S.s B.composed L.composed := by
  intro d hd
  exact composed_boundary_covers_all d
    (target_dependencies_are_represented d hd)

theorem incomplete_boundary_remains_insufficient :
    ¬ GRBS F G.g S.s B.incomplete L.incomplete := by
  intro h
  have hCovered : F.cov B.incomplete L.incomplete S.s D.d2 :=
    h D.d2 (target_dependencies_are_represented D.d2 trivial)
  exact hCovered

theorem composed_transfer_holds :
    DARMTransferAdmissible
      F G.g S.s B.composed L.composed candidate := by
  constructor
  · intro d hd
    cases d <;> simp [F]
  · constructor
    · exact composed_boundary_satisfies_grbs
    · intro d hd hCovered
      cases d <;> trivial

theorem incomplete_transfer_fails :
    ¬ DARMTransferAdmissible
      F G.g S.s B.incomplete L.incomplete candidate := by
  intro h
  exact incomplete_boundary_remains_insufficient h.2.1

theorem boundary_composition_preserves_transfer_when_coverage_is_complete :
    SourceAssured D source property ∧
    GRBS F G.g S.s B.composed L.composed ∧
    DARMTransferAdmissible
      F G.g S.s B.composed L.composed candidate := by
  constructor
  · exact source_assurance_holds
  · constructor
    · exact composed_boundary_satisfies_grbs
    · exact composed_transfer_holds

theorem residual_uncovered_dependency_blocks_composition :
    SourceAssured D source property ∧
    ¬ GRBS F G.g S.s B.incomplete L.incomplete ∧
    ¬ DARMTransferAdmissible
      F G.g S.s B.incomplete L.incomplete candidate := by
  constructor
  · exact source_assurance_holds
  · constructor
    · exact incomplete_boundary_remains_insufficient
    · exact incomplete_transfer_fails

end GRBS.DCEE6CBoundaryComposition
