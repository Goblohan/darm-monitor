import GRBS
import R5AssuranceConservation
import R6GRBSDeltaBridge

namespace GRBS.DARMCoreCalculus

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge

/-
DARM CORE CALCULUS

PURPOSE

This module defines the core assurance-transfer calculus for DARM. It
separates assurance generation from assurance transfer and makes the
conditions for expanding an assurance claim explicit.

ARCHITECTURE

A backend establishes `SourceAssured`. DARM then evaluates whether that
assurance may be transferred to a target context. The transfer requires
three explicit conditions:

  1. Delta representation: every assurance-relevant item introduced by
     the source-to-target change is represented as a structural dependency
     of the guarantee;
  2. boundary sufficiency: the guarantee-relative dependency surface is
     covered by the applicable boundary and enforcement locus (`GRBS`);
  3. semantic discharge: the required property is established for covered
     structural dependencies.

The current calculus deliberately uses whole-guarantee `GRBS` for the
second condition. `DeltaCovered` therefore names the boundary-coverage
condition required by the transfer rule. It does not mean that only the
newly introduced delta items are checked.

CORE TRANSFER THEOREM

  `SourceAssured ∧ DARMTransferAdmissible → TargetAssured`

`DARMTransferAdmissible` is an assurance-transfer condition. It is not
identical to `TargetAssured` and does not by itself establish semantic
safety.

SEMANTIC SAFETY BOUNDARY

The original GRBS kernel retains semantic system transfer through
`Transfer`. Its negative coverage result additionally requires the explicit
`Exploitability` and `Dependence` seams:

  `¬GRBS ∧ Exploitability ∧ Dependence → ¬Transfer`

Thus DARM does not claim to be a semantic safety verifier. It consumes or
relies on the semantic evidence needed to discharge transfer obligations.
-/

/-- A DARM transfer candidate consists of source and target domains,
    together with the property whose assurance is being transferred. -/
structure TransferCandidate (D : Type) where
  source : D → Prop
  target : D → Prop
  property : D → Prop

/-- The structural representation obligation for the transfer delta. -/
def DeltaRepresented
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (c : TransferCandidate F.Dependency) : Prop :=
  DeltaSubsetDependency
    F g s c.source c.target

/-- The whole-guarantee boundary coverage condition required by the
    current DARM transfer rule. This is `GRBS`, not merely coverage of the
    newly introduced delta. -/
def DeltaCovered
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus) : Prop :=
  GRBS F g s b l

/-- Semantic discharge of the property for covered structural dependencies. -/
def DeltaDischarged
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency) : Prop :=
  CoveredDischargesProperty
    F g s b l c.property

/-- DARM's transfer-admissibility judgment.

    This is an assurance-transfer condition, not a semantic safety theorem.
-/
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

/-- DARM admissibility discharges the R5 assurance delta obligation. -/
theorem darm_admissibility_discharges_delta
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency)
    (hAdmissible : DARMTransferAdmissible F g s b l c) :
    DeltaObligation
      F.Dependency c.source c.target c.property := by
  rcases hAdmissible with ⟨hRepresented, hCovered, hDischarged⟩
  exact grbs_implies_delta_obligation
    F g s b l
    c.source c.target c.property
    hCovered
    hRepresented
    hDischarged

/-- **Principal positive transfer theorem.**

    If the source assurance is established and DARM transfer is admissible,
    the target assurance follows.

    This theorem composes the backend-independent assurance result from R5
    with DARM's explicit boundary-transfer conditions. -/
theorem darm_admissibility_preserves_assurance
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (c : TransferCandidate F.Dependency)
    (hSource :
      SourceAssured
        F.Dependency c.source c.property)
    (hAdmissible :
      DARMTransferAdmissible F g s b l c) :
    TargetAssured
      F.Dependency c.target c.property := by
  have hDelta :
      DeltaObligation
        F.Dependency c.source c.target c.property :=
    darm_admissibility_discharges_delta
      F g s b l c hAdmissible
  exact target_assured_of_source_and_delta
    F.Dependency
    c.source c.target c.property
    hSource hDelta

/-- **Semantic boundary theorem.**

    DARM does not claim that failure of GRBS alone proves semantic transfer
    failure. The original GRBS kernel requires the explicit `Exploitability`
    and `Dependence` seams to connect uncovered structural dependencies to
    semantic transfer failure.

    This preserves the distinction between DARM's assurance-transfer
    discipline and the underlying semantic safety relation.
-/
theorem uncovered_boundary_blocks_semantic_transfer
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (hExploit :
      Exploitability F g s b l)
    (hDependence :
      Dependence F g s b l)
    (hUncovered :
      ¬ GRBS F g s b l) :
    ¬ Transfer F g s b :=
  transfer_fails_of_uncovered
    F g s b l
    hExploit hDependence hUncovered

end GRBS.DARMCoreCalculus
