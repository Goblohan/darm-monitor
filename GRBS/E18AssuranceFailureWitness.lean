/-
  E18 — UNIFIED ASSURANCE FAILURE WITNESSES

  Path A artifact: compose the independently established ODATS failure
  witnesses into one typed classification layer.

  E18 carries machine-checkable formal evidence for the established
  failure classes. The E15 witnesses are deletion-minimality witnesses,
  not runtime telemetry.
-/

import E15CausalCoverageContractEquivalence
import E16TemporalFreshness
import E17ProposalAuthoritySeparation

namespace GRBS.E18AssuranceFailureWitness

open GRBS.E15CausalCoverageContractEquivalence
open GRBS.E16TemporalFreshness
open GRBS.E17ProposalAuthoritySeparation

/-- Which ODATS condition caused the transfer to fail. -/
inductive FailureKind where
  | observation
  | domainCompleteness
  | authority
  | temporalFreshness
  | semanticBoundary
deriving DecidableEq, Repr

/--
Formal observation-failure evidence.

The witness is the established E15 deletion-minimality object and the
selected proposition is its observation-correspondence failure component.
-/
structure ObservationFailureEvidence : Prop where
  witness : E15DeletionMinimalityWitnesses

/--
Formal domain-failure evidence.
-/
structure DomainFailureEvidence : Prop where
  witness : E15DeletionMinimalityWitnesses

/--
Formal semantic-boundary failure evidence.

E15's representation-soundness deletion witness is used as the existing
representation-level semantic failure witness. This is a composition
of assurance obligations, not a claim of definitional identity.
-/
structure SemanticFailureEvidence : Prop where
  witness : E15DeletionMinimalityWitnesses

/-- Formal authority-failure evidence from E17. -/
structure AuthorityFailureEvidence (p : Proposal) : Prop where
  canGenerate : AgentCanGenerate p
  unauthorized : authorized (resolve p) ≠ true

/-- Formal temporal-freshness failure evidence from E16. -/
structure TemporalFailureEvidence : Prop where
  observedSafe : G (stateAt observedAt)
  otherConditions : OtherConditionsHold
  stale : ¬ Fresh observedAt decidedAt stateAt
  decisionUnsafe : ¬ G (stateAt decidedAt)

/-- Machine-checkable evidence attached to a rejected transfer. -/
inductive FailureEvidence where
  | observation (e : ObservationFailureEvidence)
  | domainCompleteness (e : DomainFailureEvidence)
  | authority (e : AuthorityFailureEvidence Proposal.execCode)
  | temporalFreshness (e : TemporalFailureEvidence)
  | semanticBoundary (e : SemanticFailureEvidence)

/-- A typed failure witness plus a human-readable diagnosis. -/
structure FailureWitness where
  kind : FailureKind
  evidence : FailureEvidence
  description : String

/-- Result of evaluating the five ODATS conditions. -/
inductive TransferResult where
  | admitted
  | rejected (witness : FailureWitness)

/-- Canonical E15 observation-failure evidence. -/
theorem observationEvidence : ObservationFailureEvidence :=
  { witness := e15_g5_deletion_minimality }

/-- Canonical E15 domain-failure evidence. -/
theorem domainEvidence : DomainFailureEvidence :=
  { witness := e15_g5_deletion_minimality }

/-- Canonical E15 semantic-failure evidence. -/
theorem semanticEvidence : SemanticFailureEvidence :=
  { witness := e15_g5_deletion_minimality }

/-- Canonical E17 authority-failure evidence. -/
theorem authorityEvidence :
    AuthorityFailureEvidence Proposal.execCode :=
  { canGenerate := agent_generates_all Proposal.execCode
    unauthorized := by
      simp [resolve, authorized] }

/-- Canonical E16 temporal-freshness evidence. -/
theorem temporalEvidence : TemporalFailureEvidence :=
  { observedSafe := safe_at_observation
    otherConditions := other_conditions
    stale := freshness_fails
    decisionUnsafe := unsafe_at_decision }

/-- All five formal failure carriers are constructible. -/
theorem all_failure_evidence_constructible :
    Nonempty ObservationFailureEvidence ∧
    Nonempty DomainFailureEvidence ∧
    Nonempty (AuthorityFailureEvidence Proposal.execCode) ∧
    Nonempty TemporalFailureEvidence ∧
    Nonempty SemanticFailureEvidence := by
  exact
    ⟨⟨observationEvidence⟩,
     ⟨domainEvidence⟩,
     ⟨authorityEvidence⟩,
     ⟨temporalEvidence⟩,
     ⟨semanticEvidence⟩⟩

/-- Boolean interface used by the first-failure classifier. -/
structure ODATSCheck where
  observationHolds : Bool
  domainHolds : Bool
  authorityHolds : Bool
  freshnessHolds : Bool
  semanticHolds : Bool

/--
First-failure classifier.

The Boolean interface is deliberately separate from the formal evidence
layer. The latter identifies the established mathematical reason for each
failure class.
-/
def evaluateTransfer (check : ODATSCheck) : TransferResult :=
  if !check.observationHolds then
    TransferResult.rejected
      { kind := FailureKind.observation
        evidence := FailureEvidence.observation observationEvidence
        description := "observation correspondence failed" }
  else if !check.domainHolds then
    TransferResult.rejected
      { kind := FailureKind.domainCompleteness
        evidence := FailureEvidence.domainCompleteness domainEvidence
        description := "domain completeness failed" }
  else if !check.authorityHolds then
    TransferResult.rejected
      { kind := FailureKind.authority
        evidence := FailureEvidence.authority authorityEvidence
        description := "proposal generation did not imply authorization" }
  else if !check.freshnessHolds then
    TransferResult.rejected
      { kind := FailureKind.temporalFreshness
        evidence := FailureEvidence.temporalFreshness temporalEvidence
        description := "observation expired before decision" }
  else if !check.semanticHolds then
    TransferResult.rejected
      { kind := FailureKind.semanticBoundary
        evidence := FailureEvidence.semanticBoundary semanticEvidence
        description := "representation-level semantic boundary failed" }
  else
    TransferResult.admitted

theorem all_pass_admits :
    evaluateTransfer
      { observationHolds := true, domainHolds := true,
        authorityHolds := true, freshnessHolds := true,
        semanticHolds := true } = TransferResult.admitted := by
  rfl

theorem o_failure_classified :
    ∃ w, evaluateTransfer
      { observationHolds := false, domainHolds := true,
        authorityHolds := true, freshnessHolds := true,
        semanticHolds := true } = TransferResult.rejected w ∧
      w.kind = FailureKind.observation := by
  exact ⟨_, rfl, rfl⟩

theorem d_failure_classified :
    ∃ w, evaluateTransfer
      { observationHolds := true, domainHolds := false,
        authorityHolds := true, freshnessHolds := true,
        semanticHolds := true } = TransferResult.rejected w ∧
      w.kind = FailureKind.domainCompleteness := by
  exact ⟨_, rfl, rfl⟩

theorem a_failure_classified :
    ∃ w, evaluateTransfer
      { observationHolds := true, domainHolds := true,
        authorityHolds := false, freshnessHolds := true,
        semanticHolds := true } = TransferResult.rejected w ∧
      w.kind = FailureKind.authority := by
  exact ⟨_, rfl, rfl⟩

theorem t_failure_classified :
    ∃ w, evaluateTransfer
      { observationHolds := true, domainHolds := true,
        authorityHolds := true, freshnessHolds := false,
        semanticHolds := true } = TransferResult.rejected w ∧
      w.kind = FailureKind.temporalFreshness := by
  exact ⟨_, rfl, rfl⟩

theorem s_failure_classified :
    ∃ w, evaluateTransfer
      { observationHolds := true, domainHolds := true,
        authorityHolds := true, freshnessHolds := true,
        semanticHolds := false } = TransferResult.rejected w ∧
      w.kind = FailureKind.semanticBoundary := by
  exact ⟨_, rfl, rfl⟩

/--
An admitted transfer requires every Boolean ODATS condition to hold.
-/
theorem no_false_admits (check : ODATSCheck) :
    evaluateTransfer check = TransferResult.admitted ->
    check.observationHolds = true
    ∧ check.domainHolds = true
    ∧ check.authorityHolds = true
    ∧ check.freshnessHolds = true
    ∧ check.semanticHolds = true := by
  cases hO : check.observationHolds <;>
    cases hD : check.domainHolds <;>
    cases hA : check.authorityHolds <;>
    cases hT : check.freshnessHolds <;>
    cases hS : check.semanticHolds <;>
    simp [evaluateTransfer, hO, hD, hA, hT, hS]

/--
All five single-failure cases are classified with their corresponding
formal evidence carrier.
-/
theorem failure_witness_complete :
    evaluateTransfer
      { observationHolds := true, domainHolds := true,
        authorityHolds := true, freshnessHolds := true,
        semanticHolds := true } = TransferResult.admitted
    ∧ (∃ w, evaluateTransfer
        { observationHolds := false, domainHolds := true,
          authorityHolds := true, freshnessHolds := true,
          semanticHolds := true } = TransferResult.rejected w ∧
        w.kind = FailureKind.observation)
    ∧ (∃ w, evaluateTransfer
        { observationHolds := true, domainHolds := false,
          authorityHolds := true, freshnessHolds := true,
          semanticHolds := true } = TransferResult.rejected w ∧
        w.kind = FailureKind.domainCompleteness)
    ∧ (∃ w, evaluateTransfer
        { observationHolds := true, domainHolds := true,
          authorityHolds := false, freshnessHolds := true,
          semanticHolds := true } = TransferResult.rejected w ∧
        w.kind = FailureKind.authority)
    ∧ (∃ w, evaluateTransfer
        { observationHolds := true, domainHolds := true,
          authorityHolds := true, freshnessHolds := false,
          semanticHolds := true } = TransferResult.rejected w ∧
        w.kind = FailureKind.temporalFreshness)
    ∧ (∃ w, evaluateTransfer
        { observationHolds := true, domainHolds := true,
          authorityHolds := true, freshnessHolds := true,
          semanticHolds := false } = TransferResult.rejected w ∧
        w.kind = FailureKind.semanticBoundary) := by
  exact ⟨
    all_pass_admits,
    o_failure_classified,
    d_failure_classified,
    a_failure_classified,
    t_failure_classified,
    s_failure_classified
  ⟩

end GRBS.E18AssuranceFailureWitness
