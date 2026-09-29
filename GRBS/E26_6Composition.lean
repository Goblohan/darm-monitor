import E26InvocationExecutionCorrespondence
import E15CausalCoverageContractEquivalence
import B8TypedEffectLog

namespace DARM.E26_6

open DARM.Kernel
open DARM.Broker (Proposal)
open DARM.Broker3
open DARM.E24d
open DARM.E26
open DARM.EffectIntegrity2

open GRBS.E13CausalSemanticCorrespondence
open GRBS.E15CausalCoverageContractEquivalence

/-
E26.6 — Composition

E26 establishes Invocation → BrokerOp correspondence for the pinned
write case.

B8 establishes BrokerOp → World transition semantics.

This experiment composes those relations while keeping the
Invocation → BrokerOp edge explicit.

NOT claimed (added on review): execution identity. Where a theorem concludes
that an authorized invocation reaches a world transition, it assumes the
corresponding operation is the one applied (the open question of E27).
invocationMediated does not consult its invocation: it says only that some
broker operation produces the transition. The substantive results are that
every broker operation appends to the log, and hence that no invocation
represents an external creation: the mediated domain is incomplete over any
causeable domain that includes creation, and the boundary is drawn by evidence.
-/

/-- An Invocation represents a World transition when a corresponding
    BrokerOp actually produces that transition. -/
def invocationRepresents
    (inv : DARM.Kernel.Invocation)
    (w w' : World) : Prop :=
  ∃ op : BrokerOp,
    ExecCorresponds inv op ∧
    DARM.EffectIntegrity2.apply w op = w'

/-- A World transition is mediated by the B8 BrokerOp vocabulary: some broker
    operation produces it. The invocation is not consulted. -/
def invocationMediated
    (_inv : DARM.Kernel.Invocation)
    (w w' : World) : Prop :=
  ∃ op : BrokerOp,
    DARM.EffectIntegrity2.apply w op = w'

/-- E26 correspondence plus an actual B8 transition composes into
    Invocation → World representation. -/
theorem exec_world_composition
    (inv : DARM.Kernel.Invocation)
    (w w' : World)
    (op : BrokerOp)
    (hExec : ExecCorresponds inv op)
    (hWorld : DARM.EffectIntegrity2.apply w op = w') :
    invocationRepresents inv w w' := by
  exact ⟨op, hExec, hWorld⟩

/-- Invocation representation implies mediated B8 execution, in the weaker,
    invocation-independent sense: the correspondence is discarded. -/
theorem representation_implies_mediated
    (inv : DARM.Kernel.Invocation)
    (w w' : World) :
    invocationRepresents inv w w' →
    invocationMediated inv w w' := by
  intro h
  obtain ⟨op, _, hWorld⟩ := h
  exact ⟨op, hWorld⟩

/-- E26 supplies the correspondence witness for a pinned execution (a
    restatement of E26.pinned_execution_has_corresponding_broker_op).
    It does not yet supply the World transition. -/
theorem pinned_execution_has_correspondence
    (p : Proposal)
    (e : DARM.Kernel.Invocation)
    (hFit : DARM.E24d.pinnedReport.fits p = true)
    (hExec :
      DARM.Broker3.brokerStep DARM.Broker3.writeCfg p = some e) :
    ∃ op, ExecCorresponds e op := by
  exact DARM.E26.pinned_execution_has_corresponding_broker_op
    p e hFit hExec

/-- If a corresponding BrokerOp is actually applied by B8, the Invocation
    reaches a World transition representation. The fit and admission premises
    are not used: the conclusion follows from the correspondence and the
    transition alone (exec_world_composition). That the corresponding operation
    is the one applied is assumed (hWorld): execution identity, E27's question. -/
theorem pinned_execution_composes_with_world
    (p : Proposal)
    (e : DARM.Kernel.Invocation)
    (w w' : World)
    (hFit : DARM.E24d.pinnedReport.fits p = true)
    (hExec :
      DARM.Broker3.brokerStep DARM.Broker3.writeCfg p = some e)
    (op : BrokerOp)
    (hCorresponds : ExecCorresponds e op)
    (hWorld :
      DARM.EffectIntegrity2.apply w op = w') :
    invocationRepresents e w w' := by
  exact exec_world_composition e w w' op hCorresponds hWorld

/-
Structural B8 fact used for the domain boundary.

Every BrokerOp adds at least one entry to the B8 log.
External creation changes files without changing the log.
Therefore creation cannot be the result of applying a BrokerOp.
-/

theorem apply_log_strictly_grows
    (w : World) (op : BrokerOp) :
    w.log.length <
      (DARM.EffectIntegrity2.apply w op).log.length := by
  cases op with
  | wr rid t d =>
      simp [DARM.EffectIntegrity2.apply,
        DARM.EffectIntegrity2.brokerWrite]
  | dl rid t =>
      simp [DARM.EffectIntegrity2.apply,
        DARM.EffectIntegrity2.brokerDelete]
  | mv rid src dst d =>
      simp [DARM.EffectIntegrity2.apply,
        DARM.EffectIntegrity2.brokerRename]
      omega

/-- External creation is outside the B8 BrokerOp execution vocabulary. -/
theorem external_creation_not_represented
    (w : World) (t d : String) :
    ¬ ∃ inv : DARM.Kernel.Invocation,
        invocationRepresents inv w (create w t d) := by
  intro h
  obtain ⟨inv, hRep⟩ := h
  obtain ⟨op, _, hApply⟩ := hRep
  have hg := apply_log_strictly_grows w op
  have hLog :
      (create w t d).log = w.log := rfl
  rw [hApply, hLog] at hg
  exact Nat.lt_irrefl _ hg

/-
The causal-domain consequence.

The composed mediated domain excludes external creation. Therefore
representation of the mediated execution path does not establish
domain completeness over a causeable domain that includes creation.
-/

def externalCreation (w w' : World) : Prop :=
  ∃ t d, w' = create w t d

def causeable (w w' : World) : Prop :=
  invocationMediated
      (DARM.Broker3.canonicalize
        DARM.Broker3.writeCfg
        DARM.Broker3.agentWritesReport)
      w w'
    ∨ externalCreation w w'

/-- The causal-domain consequence, stated: every external creation is a
    causeable transition that no invocation represents. Representing the
    mediated execution path therefore does not establish completeness over a
    causeable domain that includes creation. The boundary is drawn by
    evidence: every represented transition appends to the log
    (apply_log_strictly_grows); external creation does not. (Replaces a
    contract_coverage theorem whose dependencies and coverage were both
    defined as True, and so held trivially.) -/
theorem represented_domain_incomplete (w : World) (t d : String) :
    causeable w (create w t d) ∧
    ¬ ∃ inv : DARM.Kernel.Invocation, invocationRepresents inv w (create w t d) :=
  ⟨Or.inr ⟨t, d, rfl⟩, external_creation_not_represented w t d⟩

end DARM.E26_6
