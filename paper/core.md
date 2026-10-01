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

Section 2 shows that an intent pinning its content is complete: whatever fits
it and is admitted is exactly the authorized effect. But a principal often
cannot pin content in advance. A report computed from a data file, a summary of
a document, a reply to a message: the principal knows what an acceptable result
would be, not its exact bytes. How far can completeness reach?

### 3.1 The characterization

An intent can constrain a proposal only through what the boundary observes:
the proposal's arguments, and the world the broker reads. Two proposals that
look identical to the boundary are fitted by exactly the same intents. Call
them look-alikes. It follows that a complete intent for a target proposal
exists if and only if every admitted look-alike of that proposal is acceptable
(`E24eLineage.complete_intent_exists_iff`). The theorem is generic in the
kinds of authorization, proposal and observation, and it is proved from no
axioms at all. Its sharp edge is the contrapositive: if two admitted
look-alikes differ in acceptability, no intent fitting them is complete
(`E24eLineage.no_complete_intent_for_hidden_acceptance`).

The characterization turns a design question into a test. To decide whether
any authorization mechanism can make a given acceptance judgment enforceable,
ask whether that judgment is determined by what the boundary observes.

### 3.2 What lies within reach

Known content is within reach: it appears in the proposal, so pinning it makes
the look-alikes of the target exactly the target, as Section 2 shows. So is
content that is a function the broker can evaluate on a source it reads (a
total computed from a data file, a format conversion). The broker reads the
source and evaluates the function at the decision, so the intent pins the
result; such lineage reduces to pinning, computed at redemption
(`E24eLineage.derived_complete`). Both cases share the condition the
characterization names: acceptance is determined by what the boundary
observes.

### 3.3 What lies beyond it

The faithfulness of generated content is not within reach. A faithful summary
of a document and an unfaithful one can be byte-for-byte identical proposals
as far as the boundary can tell, since what distinguishes them is how they were
produced, which the boundary does not observe. By the characterization, no
intent is complete for faithfulness. This is not a gap in this system's
engineering: it bounds every mechanism that decides on what the boundary
observes, including provenance labels, which record where data came from but
not whether a transformation of it was faithful. Closing it would require a
component that makes the generating process observable, and that component's
correctness would then be an assumption of the guarantee, not a consequence of
it.

### 3.4 Outputs, not inputs

Completeness constrains what an action produces, not what the agent drew on.
In one model with both notions, an intent that pins content is complete, yet
it admits a proposal produced from an input that no contract declared
(`E25AuthorizationContractSeparation.complete_yet_inputs_uncovered`). And
where the boundary does not observe an agent's inputs, as it does not here (the
agent reads before it proposes, and its reads never appear in the proposal), no
intent can enforce coverage of them
(`E25AuthorizationContractSeparation.input_coverage_not_enforceable`), by the
same argument: two proposals with identical content and different inputs are
look-alikes. Governing inputs would mean mediating reads, which would enlarge
what the boundary observes; the characterization would then apply to the
enlarged observation.

Limits of this section: the characterization speaks of intent languages that
see proposals only through the boundary's observation and can express exact
look-alike sets; derived content requires a function the broker can evaluate
and a source it can read, and the source may change after the decision.

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

Authorization decides what may happen, and the audit log records what the
broker did. Neither, on its own, answers the question an auditor actually
faces: this file holds this content; was it put there by the operation that was
authorized, or by something else? We call this execution identity. The broker
leaves two independent kinds of evidence for every write, an entry in its audit
log and an attestation carried with the file itself (a signature over the
request, the target and the content digest, stored in an extended attribute).
We show that each yields execution identity under its own assumptions, and that
each catches an attack the other cannot.

### 5.1 Identity through the log

In the typed effect-log model, a path is consistent with the log when its
latest entry determines the file there: after a write under request r with
content d, exactly that content attested (r, d); after a delete, nothing; with
no entry at all, only unattested files. From these definitions alone, an
attested file at a consistent path forces the log's latest entry for that path
to be the write under that request, with that content
(`E27ExecutionIdentity.attested_identifies_write`, which rests on propositional
extensionality only). For a write carrying a pinned payload, the logged write
corresponds to the invocation that carried it
(`E27ExecutionIdentity.logged_write_corresponds`).

The log is only as good as its provenance, so we model the world's history
explicitly, as any interleaving of broker operations and foreign actions
(deletion, tampering, creation, moving). Each broker operation appends exactly
its own entries, and no foreign action appends any, so every entry in the final
log was appended by a broker operation that occurs in the history
(`E27bOperationIdentity.log_provenance`). It follows that, from the empty world
and in any history, a consistently attested file was placed by a broker write
or rename under its request identifier
(`E27bOperationIdentity.attested_file_was_placed_by_broker`, again resting on
propositional extensionality only).

In this model the attestation names a request and a digest but no path. That
is not enough on its own: after a broker write and a foreign move, the moved
file carries an attestation that looks valid, and only the log shows that no
write ever placed it there
(`E27ExecutionIdentity.attestation_alone_does_not_bind_location`).

### 5.2 Identity through the attestation

The implementation signs the target as well, and verification rejects an
attestation whose target is not the file's location. We model that attestation
directly, together with a stronger adversary who may also copy a file with its
attributes. Unforgeability is stated as a property of the foreign actions:
they may move, copy or keep attestations, never mint them. Under it, every
attestation present anywhere was minted by a broker operation in the history,
with exactly that request, target and digest
(`B8pPathBoundAttestation.evolve_inv`). A file whose attestation names its own
location was therefore placed there by a broker write or rename under that
request (`B8pPathBoundAttestation.attested_at_location_was_placed`), without
consulting the log. The log model is exactly this model with the path forgotten
(`B8pPathBoundAttestation.proj_write`), so every result about the log model
holds of an abstraction of this one.

### 5.3 Neither mechanism is redundant

The two mechanisms bind different things. A foreign move leaves an attestation
that names the file's original location, so the path check rejects it without
the log (`B8pPathBoundAttestation.moved_file_names_its_origin`). A replay (a
file copied aside, deleted by the broker, then copied back) carries an
attestation that names its location and was genuinely minted, so the
attestation accepts it; the log's latest entry for that path is the deletion,
so the log does not
(`B8pPathBoundAttestation.replay_accepted_by_attestation_caught_by_log`). The
attestation binds origin and location; the log binds freshness and order.

The implementation behaves as the models predict. One runtime test moves an
attested file onto a path whose log entry expects the same content, so that
only the signed path can catch it; another replays a deleted file, so that only
the log can. Removing the path check from the broker is caught by the first
test alone; removing the log's freshness checks is caught by the second, and
also by an earlier test of the typed log.

### 5.4 The chain as one theorem

The results of Sections 2, 4 and 5 compose. For any path and content: if a
proposal fits the intent pinning them, the kernel admits it as an invocation,
the history executed that invocation under a request, and the world is
consistent with the file carrying that request's attestation, then the file
holds exactly the authorized content, placed by a write in the history that
corresponds to the invocation
(`E28AuthorizedEffectIdentity.authorized_effect_to_attested_state`). On the
way, the correspondence of Section 4 is generalized from one path and content
to all of them (`E28AuthorizedEffectIdentity.invocation_writes_exactly_of_proposal`).

The theorem has one hypothesis about the broker itself, stated rather than
assumed silently: each request identifier belongs to one invocation. A runtime
test checks it directly, over a burst of writes, and follows each attested file
back through its identifier to the invocation that intended exactly its
content. Deriving identifiers from the target instead of minting them fresh
breaks the hypothesis, and the test catches it; notably, the traceback alone
still succeeds under that fault, because a later write overwrites the earlier
one's record. The conclusion, observed at runtime, does not imply the
hypothesis, which is why the theorem states it separately.

Limits of this section: the chain covers pinned writes (deletes and renames are
not yet authorized effects in the correspondence); the implementation's
agreement with the models is tested, not proved; unforgeability is assumed; and
identity holds at verification time, so a later foreign change is detected at
the next verification, not prevented.

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
