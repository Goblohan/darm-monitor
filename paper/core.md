# Core: shared results

A dense outline. Each section states its results, cites the theorems, and names
the limit. Prose is written into this skeleton; nothing is claimed that is not
cited here.

## 1. Setting

An agent proposes tool invocations; a reference monitor (the broker) decides,
executes, and records. The boundary observes the proposal's arguments and the
world the broker reads, nothing else. Guarantees are stated relative to explicit
assumptions (complete mediation, key secrecy, an external checkpoint sink).
Kernel admission has no false admits (`K3bKernelR22.k3b_no_false_admits`);
every effect is preceded by durable evidence, under faults
(`B4BrokerLifecycle.step_preserves`); reconciliation reports correspondence,
never causation (`B5EffectReconciliation.success_is_state_confirmation`).

## 2. Authorization completeness, as a calculus

An authorization is complete for an acceptance judgment if every proposal that
fits it and is admitted is acceptable. A mediated mechanism whose authorizations
are all complete executes only acceptable proposals, whoever proposed them
(`CompletenessCalculus.safety`, proved from no axioms). Completeness survives
revocation and consumption (`CompletenessCalculus.revocation_preserves_completeness`,
`CompletenessCalculus.consumption_preserves_completeness`); pinning through an
injective digest is pinning the value (`CompletenessCalculus.pin_by_injective`).

Pinned intents are complete (`E24eLineage.pinned_complete_general`), jointly with
deny-by-default, which is necessary (`E24dRedemption.pinned_incomplete_without_deny_by_default`).
No rule over proposals alone closes the redemption race
(`E24dRedemption.no_exact_rule`); premises close it while false, and the residual
race when they hold is proved (`E24dRedemption.residual_race_when_premise_true`),
for registries as the broker implements them
(`E24dRegistryPremises.no_redemption_without_a_usable_intent`). A failed effect
never spends its intent (`E24dRedemption.no_burn`, `E24dRedemption.unknown_holds`).

## 3. What completeness can reach

Completeness is possible exactly when acceptance is determined by what the
boundary observes (`E24eLineage.complete_intent_exists_iff`, no axioms); two
admitted look-alikes that differ in acceptability admit no complete intent
(`E24eLineage.no_complete_intent_for_hidden_acceptance`). Lineage with a
boundary-evaluated derivation reduces to pinning (`E24eLineage.derived_complete`).

Completeness constrains outputs, not inputs: a complete intent admits a proposal
built from an undeclared input (`E25AuthorizationContractSeparation.complete_yet_inputs_uncovered`),
and when inputs are unobservable, no intent can enforce their coverage
(`E25AuthorizationContractSeparation.input_coverage_not_enforceable`).

Limit: the faithfulness of generated content is not observable at the boundary;
no intent is complete for it.

## 4. From authorization to effect

The authorized payload survives canonicalization and reaches the executed
invocation (`E26InvocationExecutionCorrespondence.canonicalize_projection`,
`E26InvocationExecutionCorrespondence.pinned_execution_reaches_invocation`), with
a unique write semantics (`E26InvocationExecutionCorrespondence.correspondence_same_write_semantics`).
Every mediated transition is logged (`E26_6Composition.apply_log_strictly_grows`),
so the mediated domain excludes external creation
(`E26_6Composition.external_creation_not_represented`,
`E26_6Composition.represented_domain_incomplete`): the boundary of mediation is
drawn by evidence.

Transfer across layers requires a stated assumption, a commuting square between
the model and what realizes it (`E2PhysicalBoundary.preservation_transfers`).

## 5. Execution identity, by two complementary mechanisms

Through the log: a consistently attested file identifies the logged write
(`E27ExecutionIdentity.attested_identifies_write`, propext only), which
corresponds to the authorized invocation (`E27ExecutionIdentity.logged_write_corresponds`),
and was appended by a broker operation in the actual history
(`E27bOperationIdentity.log_provenance`,
`E27bOperationIdentity.attested_file_was_placed_by_broker`, propext only).

Through a path-bound attestation, without the log: every attestation present was
minted by a broker operation (`B8pPathBoundAttestation.evolve_inv`), so a file
whose attestation names its location was placed there under that request
(`B8pPathBoundAttestation.attested_at_location_was_placed`, propext only). The
earlier model is this one with the path forgotten (`B8pPathBoundAttestation.proj_write`).

Neither is redundant. A foreign move defeats an attestation without a path
(`E27ExecutionIdentity.attestation_alone_does_not_bind_location`) and is caught
by the path (`B8pPathBoundAttestation.moved_file_names_its_origin`); a replay
passes the attestation and is caught by the log
(`B8pPathBoundAttestation.replay_accepted_by_attestation_caught_by_log`).
Runtime: each mechanism has a test that isolates it, and removing either check
is caught (mutation gate).

### 5.1 The chain as one theorem

For any path and content: if a proposal fits the pinned intent, B3 admits it as
an invocation, the history executed that invocation under a request, and the
world is consistent with the file carrying that request's attestation, then the
file holds exactly the authorized content, placed by a write in the history that
corresponds to the invocation (`E28AuthorizedEffectIdentity.authorized_effect_to_attested_state`).
Along the way, E26's bridge holds for any path and content
(`E28AuthorizedEffectIdentity.invocation_writes_exactly_of_proposal`). The request
link is an explicit hypothesis: each request is minted for one invocation.

## 6. Composition with other defenses

A layer backs another up only in a dimension it also checks, from an independent
input (`CompositionLayers.independent_backup`): a fault in another dimension, or
in a shared input, passes the composition (`CompositionLayers.different_dimension_no_backup`,
`CompositionLayers.shared_input_no_backup`).

Experiment: composition with a deployed provenance-tracking defense, with
faults injected into each layer and into a shared input, over 1,000 paired
scenarios and a paired payload variant. [withheld pending disclosure]

## 7. The reference implementation, and the evidence discipline

Every guarantee in the threat model names a claim; every claim cites its
theorems at a pinned commit, its gated runtime tests, and its limit; both
directions are checked mechanically. Each load-bearing check is shown guarded by
removing it (nine mutations, all caught); the gate found checks that no test
asserted, each fixed by asserting the exact failure class. Metrics from the
graph: claims with both a theorem and runtime evidence, over all claims.

## 8. Limits

Stated, not hidden: the redemption race when premises hold; generated content's
faithfulness; inputs; kernel correspondence by certification, not refinement;
cryptographic unforgeability assumed; availability under bursts beyond the
backlog; hard links; one effect class (the filesystem) studied in depth.
