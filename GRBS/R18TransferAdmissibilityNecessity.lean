import GRBS
import R5AssuranceConservation
import R6GRBSDeltaBridge

namespace GRBS.R18TransferAdmissibilityNecessity

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge

/-
R18: TRANSFER ADMISSIBILITY NECESSITY

The positive DARM calculus establishes:

  SourceAssured ∧ DARMTransferAdmissible
    → TargetAssured

R18 attacks the unrestricted converse:

  TargetAssured → DARMTransferAdmissible

The countermodel below shows that this converse is false in arbitrary
assurance models. Target assurance may hold independently of the
particular DARM transfer representation, boundary coverage, and
discharge conditions.

This is a deliberate negative result. It prevents DARM from being
mistaken for a necessary condition of semantic assurance itself.
-/


/-- Minimal local representation of a transfer candidate for R18. -/
structure TransferCandidate (D : Type) where
  source : D → Prop
  target : D → Prop
  property : D → Prop

def DeltaRepresented
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (c : TransferCandidate F.Dependency) : Prop :=
  DeltaSubsetDependency
    F g s c.source c.target

def DeltaCovered
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus) : Prop :=
  GRBS F g s b l

def DeltaDischarged
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency) : Prop :=
  CoveredDischargesProperty
    F g s b l c.property

def DARMTransferAdmissible
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency) : Prop :=
  DeltaRepresented F g s c ∧
  DeltaCovered F g s b l ∧
  DeltaDischarged F g s b l c

namespace R18a

inductive D
  | d

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

  /-
  The guarantee depends on the single dependency.
  -/
  dep := fun _ _ dep =>
    match dep with
    | D.d => True

  /-
  The boundary deliberately does not cover the dependency.
  -/
  cov := fun _ _ _ dep =>
    match dep with
    | D.d => False

  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def candidate : TransferCandidate F.Dependency where
  source := fun _ => True
  target := fun _ => True
  property := fun _ => True

theorem target_assured :
    TargetAssured
      F.Dependency
      candidate.target
      candidate.property := by
  intro dep hd
  exact hd

theorem delta_is_represented :
    DeltaRepresented
      F
      G.g
      S.s
      candidate := by
  intro dep hd
  simp [F]

theorem delta_is_not_covered :
    ¬ DeltaCovered
      F
      G.g
      S.s
      B.b
      L.l := by
  intro h
  have hCov := h D.d
  simp [F] at hCov

theorem darm_admissibility_fails :
    ¬ DARMTransferAdmissible
      F
      G.g
      S.s
      B.b
      L.l
      candidate := by
  intro h
  exact delta_is_not_covered h.2.1

theorem target_assurance_does_not_imply_darm_admissibility :
    TargetAssured
        F.Dependency
        candidate.target
        candidate.property
      ∧
    ¬ DARMTransferAdmissible
        F
        G.g
        S.s
        B.b
        L.l
        candidate := by
  exact ⟨target_assured, darm_admissibility_fails⟩

end R18a


namespace R18b

/--
Target assurance is semantically sufficient to discharge the assurance
obligation on every newly introduced target item.

This is a consequence of the definition of TargetAssured, not a
DARM-specific result.
-/
theorem target_assured_implies_delta_obligation
    (X : Type)
    (source target : X → Prop)
    (property : X → Prop)
    (hTarget : TargetAssured X target property) :
    DeltaObligation X source target property := by
  intro x hDelta
  exact hTarget x hDelta.1

/--
DARM admissibility is therefore stronger than the semantic delta
obligation: it additionally requires structural representation and
boundary coverage.
-/
theorem darm_admissibility_implies_delta_obligation
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency)
    (hAdmissible :
      DARMTransferAdmissible F g s b l c) :
    DeltaObligation
      F.Dependency
      c.source
      c.target
      c.property := by
  rcases hAdmissible with ⟨hRepresented, hCovered, hDischarged⟩
  exact grbs_implies_delta_obligation
    F g s b l
    c.source c.target c.property
    hCovered
    hRepresented
    hDischarged

end R18b

end GRBS.R18TransferAdmissibilityNecessity
