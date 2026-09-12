import GRBS
import DARMCoreCalculus

namespace GRBS.DCEE9AgentToolExpansion

open GRBS
open GRBS.Concrete
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge
open GRBS.DARMCoreCalculus

/-!
# DCEE-9: Agent Tool Expansion

This case study instantiates the DARM transfer calculus against the canonical
`GRBS.Concrete` semantic model.

The source configuration contains one assurance-relevant authority (`authA`).
The target configuration introduces a new consequential tool path represented
by `authB`.

The source/target delta is represented explicitly, while the canonical target
model already records both authorities as structural dependencies. The original
boundary mediates only `authA`.

The experiment separates:

1. DARM transfer admissibility, which fails because the target
   guarantee-relative dependency surface is not boundary-sufficient; and
2. semantic `Transfer`, whose failure follows independently from the canonical
   `Exploitability` and `Dependence` seams.

DARM therefore does not equate structural coverage with semantic safety.
-/

/-- Source assurance domain: only the originally approved authority/tool. -/
def sourceDomain : Auth → Prop
  | Auth.authA => True
  | Auth.authB => False

/-- Target assurance domain: original authority plus the newly introduced one. -/
def targetDomain : Auth → Prop
  | Auth.authA => True
  | Auth.authB => True

/-- Property required by the structural delta obligation.

This is deliberately independent of `Concrete.safeC`. The experiment is
testing whether structural transfer is blocked by boundary coverage, not
identifying DARM's property predicate with the semantic trace predicate.
-/
def deltaProperty : Auth → Prop
  | Auth.authA => True
  | Auth.authB => True

/-- `authB` is exactly the newly introduced assurance-relevant item. -/
theorem tool_expansion_delta_is_authB :
    Delta Auth sourceDomain targetDomain Auth.authB := by
  constructor <;> simp [sourceDomain, targetDomain]

/-- The entire source-to-target delta is represented as a structural
dependency of the target guarantee.

The canonical `depC` makes both authorities dependencies.
-/
theorem tool_expansion_is_represented :
    DeltaSubsetDependency Concrete.F () () sourceDomain targetDomain := by
  intro d hd
  cases d with
  | authA =>
      exfalso
      simp [Delta, sourceDomain, targetDomain] at hd
  | authB =>
      trivial

/-- The newly introduced item satisfies the delta property. -/
theorem tool_expansion_delta_is_property_discharged :
    DeltaObligation Auth sourceDomain targetDomain deltaProperty := by
  intro d hd
  cases d with
  | authA =>
      exfalso
      simp [Delta, sourceDomain, targetDomain] at hd
  | authB =>
      simp [deltaProperty]

/-- The unchanged boundary is insufficient for the expanded target dependency
surface: `authB` is a dependency but is not covered.
-/
theorem tool_expansion_grbs_fails :
    ¬ GRBS Concrete.F () () () () :=
  Concrete.grbs_fails

/-- DARM rejects transfer to the expanded configuration even though the delta
is represented and its required property is available.

The failure is caused by the unchanged boundary's lack of coverage for
`authB`.
-/
theorem tool_expansion_breaks_darm_admissibility :
    ¬ DARMTransferAdmissible
      Concrete.F () () () ()
      { source := sourceDomain
        target := targetDomain
        property := deltaProperty } := by
  intro h
  exact tool_expansion_grbs_fails h.2.1

/-- The canonical semantic model independently establishes failure of semantic
transfer through its explicit `Exploitability` and `Dependence` seams.
-/
theorem tool_expansion_breaks_semantic_transfer :
    ¬ Transfer Concrete.F () () () :=
  Concrete.transfer_fails_concretely

/-- DARM's semantic boundary theorem reproduces the same semantic failure when
the canonical exploitability and dependence seams are supplied.
-/
theorem darm_semantic_failure_for_tool_expansion :
    ¬ Transfer Concrete.F () () () := by
  exact uncovered_boundary_blocks_semantic_transfer
    Concrete.F () () () ()
    Concrete.exploitability_holds
    Concrete.dependence_holds
    Concrete.grbs_fails

/-- The source assurance domain satisfies the delta property. -/
theorem source_is_assured :
    SourceAssured Auth sourceDomain deltaProperty := by
  intro d hd
  cases d with
  | authA =>
      trivial
  | authB =>
      simp [sourceDomain] at hd

/-- Conditional positive result.

If DARM transfer admissibility were established, the existing R5/R6 bridge
would derive target assurance from source assurance. This theorem does not
claim that the unchanged boundary actually satisfies the condition.
-/
theorem conditional_target_assurance :
    DARMTransferAdmissible
        Concrete.F () () () ()
        { source := sourceDomain
          target := targetDomain
          property := deltaProperty } →
      TargetAssured Auth targetDomain deltaProperty := by
  intro hAdmissible
  exact darm_admissibility_preserves_assurance
    Concrete.F () () () ()
    { source := sourceDomain
      target := targetDomain
      property := deltaProperty }
    source_is_assured hAdmissible

end GRBS.DCEE9AgentToolExpansion
