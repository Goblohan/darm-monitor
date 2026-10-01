# Framing: formal-methods venue

Target: CAV, ITP, CPP. Sections refer to `core.md`.

## Abstract

We mechanize, in Lean 4, a theory of authorization for a reference monitor that
mediates an agent's tool use. Its central notion, authorization completeness,
comes with a calculus whose safety theorem is proved from no axioms, and with an
exact characterization, also axiom-free: completeness is possible precisely when
acceptance is determined by what the boundary observes. We carry an authorized
payload from proposal to effect through canonicalization and a typed effect
log, derive execution identity in two independent ways, through the log and
through a path-bound attestation whose abstraction is the log model, and
compose the whole chain into one theorem. A reference implementation ties every
guarantee to a theorem at a pinned commit, a runtime test, and a mutation
showing the test guards it.

## Introduction

Reference monitors are old; agents that act through tools are new, and they
change what a monitor must establish. The question is no longer only whether an
action is permitted, but whether the effect that reaches the world is the one
that was authorized, by a principal, for an agent that may be compromised. We
develop that question formally and mechanize the answers.

Contributions:

1. **A calculus of authorization completeness.** A mediated mechanism whose
   authorizations are complete executes only acceptable proposals
   (`CompletenessCalculus.safety`, no axioms); completeness is invariant under
   revocation and consumption, and pinning through an injective digest is
   pinning the value (Section 2).
2. **An exact characterization.** A complete authorization for a target exists
   if and only if every admitted look-alike is acceptable
   (`E24eLineage.complete_intent_exists_iff`, no axioms), with impossibility
   corollaries for hidden acceptance and for unobserved inputs (Section 3).
3. **From authorization to effect.** Canonicalization preserves the payload in
   general; the mediated domain is bounded by what is logged (Section 4).
4. **Execution identity, twice.** Through the log, from the effect model's own
   definitions and in any history (`E27bOperationIdentity.attested_file_was_placed_by_broker`,
   propositional extensionality only); and through a path-bound attestation,
   without the log (`B8pPathBoundAttestation.attested_at_location_was_placed`,
   likewise), whose model refines the log model
   (`B8pPathBoundAttestation.proj_write`) (Section 5).
5. **One composed theorem.** The chain from authorized proposal to attested
   state, for any path and content, with its single broker hypothesis stated
   (`E28AuthorizedEffectIdentity.authorized_effect_to_attested_state`)
   (Section 5.4).
6. **A case study in evidence.** The implementation's guarantees are checked
   against the corpus in both directions on every build, and a mutation gate
   shows each load-bearing check is guarded (Section 7).

## Section order

1. Introduction. 2. The calculus, with its axiom profile (core 2). 3. The
characterization and its limits (core 3). 4. From authorization to effect, and
the refinement between effect models (core 4, 5). 5. Composition, as theorems
(core 6). 6. Case study: the implementation and the evidence discipline
(core 7). 7. Limits (core 8). Related work. Conclusion.
