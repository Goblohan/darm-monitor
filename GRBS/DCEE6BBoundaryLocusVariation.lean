import DARMCoreCalculus

namespace GRBS.DCEE6BBoundaryLocusVariation

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge
open GRBS.DARMCoreCalculus

/-!
DCEE-6B: Boundary/Locus Variation

Purpose:
  Test whether identical source assurance and identical target dependency
  representations can yield different transfer outcomes solely because the
  enforcement boundary/locus differs.

The experiment isolates boundary-indexed transfer from assurance production.

It does NOT claim that boundary/locus is absent from existing assurance
formalisms. It tests whether making this dimension explicit changes the
transfer judgment.
-/

inductive D
  | d

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
    | B.weak, L.weak, D.d => False
    | B.strong, L.strong, D.d => True
    | _, _, D.d => False
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def source : D → Prop
  | D.d => True

def target : D → Prop
  | D.d => True

def property : D → Prop
  | D.d => True

def candidate :
    TransferCandidate F.Dependency where
  source := source
  target := target
  property := property

theorem source_assurance_holds :
    SourceAssured D source property := by
  intro d hd
  cases d
  trivial

theorem target_dependency_is_represented :
    ∀ d, target d → F.dep G.g S.s d := by
  intro d hd
  cases d
  trivial

theorem weak_boundary_fails_grbs :
    ¬ GRBS F G.g S.s B.weak L.weak := by
  intro h
  have hCovered : F.cov B.weak L.weak S.s D.d :=
    h D.d (target_dependency_is_represented D.d trivial)
  exact hCovered

theorem strong_boundary_satisfies_grbs :
    GRBS F G.g S.s B.strong L.strong := by
  intro d hd
  cases d
  trivial

theorem weak_transfer_fails :
    ¬ DARMTransferAdmissible
      F G.g S.s B.weak L.weak candidate := by
  intro h
  exact weak_boundary_fails_grbs h.2.1

theorem strong_transfer_holds :
    DARMTransferAdmissible
      F G.g S.s B.strong L.strong candidate := by
  constructor
  · intro d hd
    cases d
    trivial
  · constructor
    · exact strong_boundary_satisfies_grbs
    · intro d hd hCovered
      cases d
      trivial

theorem same_source_assurance_different_boundary_outcome :
    SourceAssured D source property ∧
    (¬ DARMTransferAdmissible
      F G.g S.s B.weak L.weak candidate) ∧
    DARMTransferAdmissible
      F G.g S.s B.strong L.strong candidate := by
  constructor
  · exact source_assurance_holds
  · constructor
    · exact weak_transfer_fails
    · exact strong_transfer_holds

end GRBS.DCEE6BBoundaryLocusVariation
