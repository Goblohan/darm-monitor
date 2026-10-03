# Core: shared results

A dense outline. Each section states its results, cites the theorems, and names
the limit. Prose is written into this skeleton; nothing is claimed that is not
cited here.

## 1. Setting

An agent proposes tool invocations; a reference monitor, the broker, decides
each one, executes what it admits, and records what happened. The threat is a
compromised agent: one whose proposals may be chosen by an attacker, for
example through injected instructions. The broker, its decision kernel and the
principal who issues authority are trusted; the agent is not. The boundary
observes the proposal's arguments and the world the broker reads, and nothing
else, which Section 3 shows is exactly what limits what any authorization can
guarantee. Guarantees are stated relative to explicit assumptions: complete
mediation (every governed effect passes through the broker), the secrecy of
the broker's signing key, and an external sink for audit checkpoints.

Three properties of the decision and execution path are used throughout. The
kernel decides on a canonical invocation; for the policy that motivated it, in
which policies that name tools alone collapse invocations with different
authority, it never admits an invocation that the policy's semantics forbids
(`K3bKernelR22.k3b_no_false_admits`). In the broker's lifecycle model, the
invariant that durable evidence precedes every effect is preserved by every
step, under any combination of the modeled faults
(`B4BrokerLifecycle.step_preserves`). And reconciliation makes a state claim,
not a causal one: an outcome is confirmed as a success exactly when the
observed state is the intended one (`B5EffectReconciliation.success_is_state_confirmation`).

Section 2 develops authorization completeness as a calculus, Section 3 shows
exactly what it can and cannot reach, Section 4 follows an authorized payload
to the world, Section 5 establishes execution identity and composes the whole
chain into one theorem, Section 6 treats composition with other defenses,
Section 7 describes the reference implementation and the discipline that ties
its guarantees to their evidence, and Section 8 collects the limits.

## 2. Authorization completeness, as a calculus

A principal grants an agent authority by issuing intents, which the broker
redeems when a proposal fits them. Consider an intent to write the quarterly
report. Bound to the tool and the path, it is redeemed by whichever fitting
proposal arrives first, and a hijacked agent's write to that path, with
different content, fits it too. Authorization that names only which tool may
act on which resource admits effects the principal never wanted. What is needed
is a notion of authorization that constrains the effect itself.

### 2.1 Completeness, and the calculus

An authorization is complete for an acceptance judgment, relative to a
boundary, if every proposal that fits it and is admitted by the boundary is
acceptable. A mechanism is mediated if whatever it executes is fitted by some
authorization in its registry and admitted by the boundary. Then a mediated
mechanism whose authorizations are all complete executes only acceptable
proposals, whoever proposed them, in any order (`CompletenessCalculus.safety`).
The theorem is proved from no axioms: the guarantee is a matter of logic once
mediation and completeness hold, and everything particular to a broker enters
only through the mediation property.

Completeness is an invariant, not a property of a single step. A registry that
only shrinks keeps it, so revocation and consumption both preserve it
(`CompletenessCalculus.revocation_preserves_completeness`,
`CompletenessCalculus.consumption_preserves_completeness`).

### 2.2 Pinning, and why it is joint

An intent that pins both the path and the content is complete for writing
exactly that content, for any path and content
(`E24eLineage.pinned_complete_general`). Completeness here is joint: it holds
only together with the kernel's refusal of arguments the policy does not rule.
Lift that refusal for a single extra argument, and the same pinned intent
admits a proposal it should not
(`E24dRedemption.pinned_incomplete_without_deny_by_default`). Content can also
be pinned by digest, which is the same constraint exactly when the digest is
injective on the contents involved (`CompletenessCalculus.pin_by_injective`);
for a real hash, that is the assumption of collision resistance.

### 2.3 The redemption race

Could a smarter rule close the race without pinning? No rule can, even one
that sees the world's state as well as the proposal: a principal's write and a
hijacked agent's identical write, in the same state, receive the same answer
from any rule, so none admits the first and refuses the second
(`E24dRedemption.no_exact_rule`). Premises do not separate them either. What
they do is withhold redemption from everyone until the world reaches a state
the principal named. An intent may carry premises the broker
observes itself (a file present, absent, or with a given digest), never read
from the proposal; while every fitting intent has a false premise, nothing
executes and nothing is spent, whoever proposes, as the broker implements it
over a registry of several intents
(`E24dRegistryPremises.no_redemption_without_a_usable_intent`). When the
premise holds and the content is unpinned, the first fitting proposal still
wins; this residual race is proved rather than hidden
(`E24dRedemption.residual_race_when_premise_true`).

### 2.4 Failures do not spend authority

An intent is reserved when a proposal is admitted and settled only once the
outcome is durable: a confirmed effect spends it, a proven non-effect returns
it, and an unresolved outcome keeps it reserved (`E24dRedemption.no_burn`,
`E24dRedemption.unknown_holds`). A write that fails therefore leaves the
principal's authority intact, and a write whose outcome is unknown is never
counted as either.

Limits of this section: completeness for unpinned content is the subject of
Section 3; the residual race when premises hold is a stated limit; digest
pinning rests on collision resistance; premises hold at the decision, not
throughout the effect.

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
intent is complete for faithfulness
(`E24eLineage.hidden_process_admits_no_complete_intent`). This is not a gap in this system's
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

Section 2 constrains proposals. Effects, though, happen through other
representations: the invocation the kernel decides on, the operation the broker
performs, and the transition the world undergoes. An authorization that held of
the proposal is only worth as much as its survival through each change of
representation. This section follows the authorized payload from the proposal
to the world, and shows where the domain of what is governed ends.

### 4.1 Through canonicalization

The broker never executes the agent's proposal as written. It canonicalizes it
into an invocation, assigning provenance to each argument from the principal's
registry. Canonicalization keeps the tool and every key and value of the
proposal, adding only provenance, for any configuration and any proposal
(`E26InvocationExecutionCorrespondence.canonicalize_projection`). For the
pinned write studied there, completeness therefore reaches the invocation that
is actually executed, not only the proposal
(`E26InvocationExecutionCorrespondence.pinned_execution_reaches_invocation`),
and any two broker operations corresponding to that invocation have the same
write semantics, whatever their execution identifiers
(`E26InvocationExecutionCorrespondence.correspondence_same_write_semantics`).
Two qualifications keep this honest: the correspondence relates two models (the
kernel's invocations and the effect model's operations), and a corresponding
operation exists by construction. Section 5.4 generalizes the payload result
from one path and content to all of them.

### 4.2 The mediated domain is drawn by evidence

Every broker operation appends to the audit log
(`E26_6Composition.apply_log_strictly_grows`). An external creation appends
nothing, so no invocation represents it
(`E26_6Composition.external_creation_not_represented`), and the domain of
mediated transitions is incomplete over any domain of possible transitions that
includes creation (`E26_6Composition.represented_domain_incomplete`). The point
is not that mediation fails, but where its boundary lies: what the reference
monitor governs is defined by what it records. A change that leaves no record
is, by that fact, outside the mediated domain, and the question becomes whether
verification detects it, which Section 5 answers for moves and replays.

### 4.3 Crossing into the physical

A guarantee proved about a model holds of the world only through an assumption
that the world realizes the model. We state that assumption exactly, in a small
setting: a realization map from model states to physical states, and actuator
correctness, a commuting square (running the actuator on the realized state
gives the realization of what the model computed). Under it, preservation in
the model implies preservation in the physical layer, for every meaning, action
and state (`E2PhysicalBoundary.preservation_transfers`); an actuator that
violates it gives the counterexample. For this system, the effect model is the
model layer, and the real filesystem's agreement with it is that assumption,
which the implementation's trace checks test rather than prove.

### 4.4 Through transformations, and the role boundary

Authorization is decided in one representation and often carried into
another: a proposal canonicalized, an invocation rewritten, a pipeline's effect
restated in another domain. An abstract transformation between authorization
domains carries a sound authorization to a sound one when it is a morphism,
reflecting fitting and admission back to the source, preserving acceptability,
and covering every target proposal that fits the transformed authorization and is admitted (`E32bAttributionComposition.transfer`),
and such morphisms compose (`E32bAttributionComposition.compose_transfer`).
Each condition is necessary: for each, a witness keeps the other three, starts
from a sound authorization, and loses soundness. Without fit reflection, the
target authorization fits a proposal the source did not
(`E32bAttributionComposition.fitReflect_necessary`); without admission
reflection, the target boundary admits what the source refused
(`E32bAttributionComposition.admitReflect_necessary`); without preserved
acceptability, the target principal accepts less than the source
(`E32bAttributionComposition.accPreserve_necessary`); and without coverage, an
unacceptable target proposal has no source
(`E32bAttributionComposition.coverage_necessary`). Running two sound
domains side by side is sound only when joint acceptability is determined by
acceptability in each (`E32bAttributionComposition.separability_necessary`).
The redemption race of Section 2.3 reappears here as a failure of coverage, at
the attacker's write (`E32bAttributionComposition.p13_is_coverage_failure`).

Admission reflection has a concrete edge in the kernel, because the role of a
value is decided by the tool's rules. With identical rules for two tools and a
credential naming one of them, changing only the tool turns an admission into
a refusal for authority
(`E32dRoleBoundary.tool_identity_alone_changes_admission`). With the same keys
and allowed values, but rules that make a value a payload under one tool and a
selector under the other, the arguments are allowed alike, the trust required
of selectors differs, and the transformed invocation is refused
(`E32dRoleBoundary.role_is_tool_relative`). A transformation that changes no
argument can therefore move an untrusted value across the boundary between
payload and selector, and an argument that authorization survives a
transformation must account for roles, not only for values.

Limits of this section: the canonicalization result is general, but the
correspondence to effect operations covers writes; the corresponding operation
exists by construction; the physical transfer is an assumption, tested in this
system, not proved.

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

### 5.5 Renames: origin, laundering, and lineage

We froze the chain of Section 5.4 and attacked it. Its hypotheses hold
together in a concrete instance, so it is not vacuous
(`E28aUnderAttack.e28_hypotheses_satisfiable`), and every attack we aimed at it
(request or invocation substitution, shared identifiers, reordering, tampering,
replay, deletion and recreation) is stopped by one of its stated hypotheses.
The attack did find a fault in the effect model itself: its rename placed
content at the destination whatever the source held, so a single rename from an
empty world yields a consistent, attested file that no write produced
(`E28aUnderAttack.rename_mints_content`).

Requiring a rename to move only what its source holds is not enough. Content
created outside the broker and then renamed by it is re-attested under the
rename's request, giving a consistent world with an attested file that no
authorized write produced (`E29FaithfulRename.rename_launders_foreign_content`).
Requiring instead that the source carry an attestation for the content it
moves is enough: every attestation present then names content that some write
in the history produced, through any chain of renames
(`E29FaithfulRename.attested_content_has_write_origin`). The model predicted
that the implementation laundered, and it did (Section 7).

Under that condition, attribution extends to renames. Every attestation has a
lineage, a chain of requests back to the write that produced its content; a
file placed by a rename is attributed to the rename invocation that moved it,
from its path to its destination, with a lineage ending at a write
(`E30RenameAttribution.rename_placed_lineage`), and if that write was executed
for the authorized write invocation, the renamed file holds exactly the
authorized content (`E30RenameAttribution.rename_placed_content_authorized`).
A runtime test follows a renamed file's attestation back, through the
attestation the rename recorded from its source, to the write.

### 5.6 Beyond the filesystem

To test whether the theory depends on the filesystem, we modeled a remote
service whose state the broker cannot observe. With a service that records the
request's identifier in the state it creates, every such record was produced by
the broker's delivered request under that identifier, whatever other clients
did (`E31RemoteEffects.echoed_record_attributed`). Without one, a request whose
response was lost and a request that was dropped while another client sent the
identical one reach the identical world, so nothing observable attributes the
effect (`E31RemoteEffects.no_attribution_without_echo`); and from the broker's
own record after a timeout, no retry decision is exactly-once
(`E31RemoteEffects.no_exactly_once_from_own_record`). The authorization results
transfer unchanged, since they concern proposals; what breaks is what rested
on observing the target. As Section 3 predicts, attribution and exactly-once
hold precisely when the remote state carries the request's identity.

### 5.7 Channels between stages, and reading what is current

A pipeline in which one stage writes what another reads is attributable as a
whole when four conditions hold: the upstream authorization is sound; what it
may write lands, through the channel between the stages, inside the set of
inputs the downstream authorization was made sound for; the downstream is
sound on that set; and the pipeline's acceptability is determined by its
stages' (`E32cSequentialComposition.seq_sound`). Each is needed, with the
others intact: an upstream that may write outside that set
(`E32cSequentialComposition.rely_necessary`), a channel that rewrites between
the write and the read (`E32cSequentialComposition.channel_necessary`), and a
sequence that is unacceptable although each step is acceptable
(`E32cSequentialComposition.seqSeparability_necessary`). In the running example,
the pinned intent of Section 2 does not make the pipeline attributable if the
file can change between the write and the run
(`E32cSequentialComposition.tamper_breaks_pipeline`).

The channel's integrity need not be assumed. If the channel is faithful (every
read carrying an attestation was produced), the produced values lie inside the
downstream's set, the downstream is sound on that set, and it admits only
attested reads, then every admitted downstream action is acceptable and its
input was produced, whatever else happened to the world
(`E33AttestedChannels.gated_downstream_sound`). Both halves matter: a reader
that does not require attestation consumes a foreign value from a faithful
channel (`E33AttestedChannels.gate_necessary`), and a gate on an unfaithful
channel admits a forged attestation (`E33AttestedChannels.faithfulness_necessary`).
The gate must compare content, not presence: in an attestation-faithful
history, a gate that checks only that an attestation exists admits tampered
content that no write produced
(`E33AttestedChannels.presence_gate_defeated_by_tamper`). Where the channel
carries no identity, as with a remote service that does not echo it
(Section 5.6), the gate admits nothing, and downstream attribution cannot be
discharged this way (`E33AttestedChannels.e31_no_echo_no_attested_read`).
External inputs enter through the principal: in attestation-faithful
histories, a channel that attributes a read either to a broker write or to a
manifest the principal holds is faithful to what was written or vouched for
(`E33bPrincipalVouching.two_source_faithful`); vouching is exact to the content
(`E33bPrincipalVouching.vouch_is_content_exact`), and a manifest the agent can
extend launders foreign content into an attributed read
(`E33bPrincipalVouching.agent_manifest_launders`).

Faithfulness in these models means that the content was produced at some
point, not that it is current. The implementation's gate adds the log: a read
is attributed only if its attestation verifies, names the path, matches the
bytes read, and is the path's latest logged write, so content restored with its
genuine attestation after the broker replaced or deleted it is refused, which
the attestation alone would accept
(`B8pPathBoundAttestation.replay_accepted_by_attestation_caught_by_log`). The
attestation is read from the same open file as the content, and refusal of
unattributed reads is enforced when the deployment asks for it.

Limits of this section: the chain covers pinned writes, and renames under
attestation-faithful renaming; deletes are not attributed, since an absence
carries no attestation; the implementation's agreement with the models is
tested, not proved; unforgeability is assumed; and identity holds at
verification time, so a later foreign change is detected at the next
verification, not prevented.


## 6. Composition with other defenses

A layer backs another up only in a dimension it also checks, from an independent
input (`CompositionLayers.independent_backup`): a fault in another dimension, or
in a shared input, passes the composition (`CompositionLayers.different_dimension_no_backup`,
`CompositionLayers.shared_input_no_backup`).

Experiment: composition with a deployed provenance-tracking defense, with
faults injected into each layer and into a shared input, over 1,000 paired
scenarios and a paired payload variant. [withheld pending disclosure]

## 7. The reference implementation, and the evidence discipline

The system has a reference implementation: a broker and a kernel that enforce
the guarantees of Sections 1 to 5 on a real filesystem. Its central design
choice is that every guarantee it states is tied, mechanically, to its
evidence. The threat model lists 28 guarantees. Each names a claim in an
assurance graph; each of the graph's 30 claims cites the theorems that prove
it, at a pinned commit of the proof corpus, the runtime tests that exercise it,
the implementation that enforces it, and the limit that bounds it. A checker
verifies both directions on every build: a guarantee without a claim, a claim
that no guarantee states, a cited theorem or function that does not exist, or a
cited test that the build does not run, each fails it. Of the 30 claims, 26 have both a theorem and gated runtime evidence; the remaining 4 are named for
what they are, tested but not modelled (signatures, checkpoints, availability
under bursts, and race-free path resolution).

Tests can pass for the wrong reason, so each load-bearing check is shown to be
guarded by removing it. A mutation gate disables one check at a time in a
throwaway copy of the broker and requires the full test suite to fail. Seventeen mutations, covering every dimension of the kernel's decision, intents,
premises, the attestation's path check, the log's freshness checks, the request
link of Section 5.4, the rename's source check of Section 5.5, read freshness,
the normal form of a rename's destination, the handling of a stop signal, the
cross-check of canonicalization, recovery's attestation check, and the binding
of a kernel reply to its request, are all caught. The gate found real gaps: a test
named for credential expiry that never asserted it, a test of deny-by-default
that passed because a different check refused, no test at all of the
credential check, and a runtime check of the attestation's path tested only by
a stale file that the build never ran. Each was fixed by asserting the exact
failure class, and each fix was confirmed by rerunning its mutation.

Every claim also states how its theorems reach the running code, and the build
counts the answers. The decision path is the model itself, compiled: the kernel
executable decides with the definition the proofs are about, and it computes
well-formedness and canonicalization from the raw proposal as well, admitting
exactly the canonical invocation (`K6KernelCanonicalization.k6_admits_canonical`).
What travels between the kernel and the broker is covered by theorems about the
shipped server code: if the broker reads an admission, the line parsed into a
request that the proved kernel admitted, in either request form
(`K5WireContract.admit_only_by_kernel`, `K6DecisionServer.admit_only_by_kernel6`),
and the broker executes the invocation the kernel returned. Each reply also
carries the nonce of the request it answers, and the broker accepts an admission
only for its own request's nonce, so a stale or foreign reply cannot be read as
the answer (`K7DecisionServer.reply_names_its_request`). The trusted base
that remains is named: the Lean compiler and runtime, the JSON parser and the
derived instances, the server's input loop, Python's JSON decoder, and the
broker's decoding of the reply, which is checked against the proved decoder on
every class of reply and by hash on execution, not proved; and that the broker never reuses a
nonce. Everything after the decision rests on models and tests, and the build
reports the ratio: one claim by construction, one proved, twenty-eight tested.
That part is audited rather than proved, but exhaustively: every effect site in
the broker, thirty-seven in all, is classified as executing the kernel's
invocation for its request, continuing a transition the kernel admitted, or
acting outside the governed workspace, none is without authority, and the build
fails if a site appears, changes or goes unclassified. Recovery, the one path
that acts after a crash, rolls a transition forward only on a signed attestation
for that request, so a forged record in the log is rolled back. The claim also survives
change. Each verdict is bound to a fingerprint of everything it depends on that
static analysis of the package can see (the routes into its effect function,
everything called along them, and the module code involved), so a property local
to those cones holds of every version the build accepts
(`E34AssuranceUnderChange.history_preserved`). A cone that missed a dependency
would let a breaking change through (`E34AssuranceUnderChange.locality_necessary`),
and a gate that is sound must sometimes ask for review of a harmless change
(`E34AssuranceUnderChange.gate_incomplete`). That the gate's cones are local is
shown by design and by attack, not proved. Writing these bridges down
exactly found four discrepancies no earlier test had: a decoder that raised
instead of rejecting, a rename destination admitted by the kernel and refused
only at execution, the same gap in the broker model the code had been
certified against (`K6KernelCanonicalization.b3_admits_escaping_destination`),
and a stop signal that could kill the broker without a final record.

The clearest evidence for the method came from the model. Attacking the chain
of Section 5.4 showed that renames in the effect model could mint content;
asking what condition prevents it showed that requiring a rename to move only
what its source holds still launders foreign content. A probe then confirmed
that the implementation did exactly that: a file created outside the broker,
renamed through it, came out attested, and verification reported nothing. The
model's condition became the fix, the refusal is recorded like every other, a
test exercises each way to launder, and a mutation that removes the check is
caught by that test alone.

The same discipline applies to this paper: every theorem it cites is checked to
exist on every build of the proof corpus.

## 8. Limits

Stated, not hidden. The redemption race when premises hold and content is
unpinned (Section 2.3). The faithfulness of generated content, which no intent
can make complete (Section 3.3), and the coverage of an agent's inputs, which
no intent can enforce while inputs are unobserved (Section 3.4). The chain of Section 5.4 covers pinned writes, and renames are attributed through
two requests (Section 5.5); deletes are not attributed, since an absence
carries no attestation. Beyond the filesystem, attribution and exactly-once
require the remote state to carry the request's identity (Section 5.6). The implementation's agreement with the models
is tested, not proved, except on the decision path, where the kernel is the model
compiled and its replies are covered by theorems about the server code, trusting the Lean compiler, the JSON parser, the broker's decoding of the reply,
and the freshness of its nonces. The effect-surface claim survives a change to
the implementation only through a correct review at each acceptance, and only
within what static analysis of the package can see. Cryptographic unforgeability and the
secrecy of the signing key are assumed. Identity holds at verification time:
a later foreign change is detected at the next verification, not prevented.
Availability under bursts larger than the listen backlog is a stated limit,
not a guarantee; hard links lie outside the model; and one effect class, the
filesystem, has been studied in depth.

