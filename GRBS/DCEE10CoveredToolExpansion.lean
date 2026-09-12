import GRBS
import DARMCoreCalculus

namespace GRBS.DCEE10CoveredToolExpansion

open GRBS
open GRBS.Concrete
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge
open GRBS.DARMCoreCalculus

/-!
# DCEE-10: Covered Agent Tool Expansion

This is the positive structural counterpart to DCEE-9.

The target configuration introduces `authB`, exactly as in DCEE-9, but the
boundary is expanded so that both `authA` and `authB` are covered.

The experiment therefore separates two questions:

1. Does boundary coverage become sufficient for DARM transfer admissibility?
2. Does structural DARM admissibility by itself establish the canonical
   semantic `Transfer` property?

The first is positive. The second remains independent: the canonical semantic
model still contains the `bypassB -> usedB` unsafe path.

Thus removing the DARM coverage obstruction does not silently become a proof
of semantic safety.
-/

/-- Source assurance domain: only the originally approved authority/tool. -/
def agentSourceDomain : Auth → Prop
  | Auth.authA => True
  | Auth.authB => False

/-- Target assurance domain: original authority plus the newly introduced one. -/
def agentTargetDomain : Auth → Prop
  | Auth.authA => True
  | Auth.authB => True

/-- Property required by the structural delta obligation. -/
def agentDeltaProperty : Auth → Prop
  | Auth.authA => True
  | Auth.authB => True

/-- The newly introduced `authB` is represented by the canonical dependency
surface. -/
theorem agent_expansion_is_represented :
    DeltaSubsetDependency
      Concrete.F () () agentSourceDomain agentTargetDomain := by
  intro d hd
  cases d with
  | authA =>
      exfalso
      simp [Delta, agentSourceDomain, agentTargetDomain] at hd
  | authB =>
      trivial

/-- The agent/tool expansion satisfies its structural delta obligation. -/
theorem agent_expansion_is_discharged :
    DeltaObligation
      Auth agentSourceDomain agentTargetDomain agentDeltaProperty := by
  intro d hd
  cases d with
  | authA =>
      exfalso
      simp [Delta, agentSourceDomain, agentTargetDomain] at hd
  | authB =>
      simp [agentDeltaProperty]

/-- Source assurance holds for the unchanged source configuration. -/
theorem agent_source_is_assured :
    SourceAssured Auth agentSourceDomain agentDeltaProperty := by
  intro d hd
  cases d with
  | authA =>
      trivial
  | authB =>
      simp [agentSourceDomain] at hd

/-- Expanded boundary: both assurance-relevant authorities are mediated. -/
def expandedCov : Unit → Unit → Unit → Auth → Prop
  | _, _, _, Auth.authA => True
  | _, _, _, Auth.authB => True

/-- The same semantic model with the expanded boundary. -/
def ExpandedF : Frame where
  Trace := Concrete.F.Trace
  Guarantee := Concrete.F.Guarantee
  System := Concrete.F.System
  Boundary := Concrete.F.Boundary
  Locus := Concrete.F.Locus
  Dependency := Concrete.F.Dependency
  Environment := Concrete.F.Environment
  Safe := Concrete.F.Safe
  dep := Concrete.F.dep
  cov := expandedCov
  Envs := Concrete.F.Envs
  Traces := Concrete.F.Traces
  Perturbs := Concrete.F.Perturbs

/-- The expanded boundary covers the entire target dependency surface. -/
theorem expanded_boundary_is_grbs :
    GRBS ExpandedF () () () () := by
  intro d hd
  cases d with
  | authA =>
      trivial
  | authB =>
      trivial


/-- The expanded boundary is sufficient for the DARM structural coverage
condition. -/
theorem covered_tool_expansion_is_darm_admissible :
    DARMTransferAdmissible
      ExpandedF () () () ()
      { source := agentSourceDomain
        target := agentTargetDomain
        property := agentDeltaProperty } := by
  constructor
  · exact agent_expansion_is_represented
  · constructor
    · exact expanded_boundary_is_grbs
    · intro d hd hcov
      cases d with
      | authA =>
          trivial
      | authB =>
          trivial

/-- Source assurance is unchanged by the boundary expansion. -/
theorem covered_tool_expansion_source_assured :
    SourceAssured Auth agentSourceDomain agentDeltaProperty :=
  agent_source_is_assured

/-- With the expanded boundary, the DARM calculus derives target assurance. -/
theorem covered_tool_expansion_target_assured :
    TargetAssured Auth agentTargetDomain agentDeltaProperty :=
  darm_admissibility_preserves_assurance
    ExpandedF () () () ()
    { source := agentSourceDomain
      target := agentTargetDomain
      property := agentDeltaProperty }
    covered_tool_expansion_source_assured
    covered_tool_expansion_is_darm_admissible

/-- Structural DARM admissibility does not establish semantic `Transfer`.

The expanded boundary changes only the coverage relation. The environment,
transition, and safety semantics remain those of the canonical model, so the
`bypassB -> usedB` execution remains unsafe.
-/
theorem semantic_transfer_still_fails :
    ¬ Transfer ExpandedF () () () := by
  intro hTransfer
  have hUnsafe :
      ExpandedF.Safe () Tr.usedB = False := by
    simp [ExpandedF, Concrete.F, safeC]
  have hTrace :
      ExpandedF.Traces () Env.bypassB () Tr.usedB := by
    simp [ExpandedF, Concrete.F, tracesC]
  have hEnv :
      ExpandedF.Envs () Env.bypassB := by
    simp [ExpandedF, Concrete.F, envsC]
  have hSafe := hTransfer Env.bypassB hEnv Tr.usedB hTrace
  rw [hUnsafe] at hSafe
  exact hSafe

/-- The positive DARM result and the negative semantic result coexist.

This is the key separation result for the experiment:
structural target assurance under the expanded boundary does not constitute a
semantic safety proof for the same expanded frame.
-/
theorem structural_assurance_does_not_imply_semantic_transfer :
    TargetAssured Auth agentTargetDomain agentDeltaProperty ∧
      ¬ Transfer ExpandedF () () () :=
  ⟨covered_tool_expansion_target_assured, semantic_transfer_still_fails⟩

end GRBS.DCEE10CoveredToolExpansion
