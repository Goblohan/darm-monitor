# Framing: security venue

Target: IEEE S&P, USENIX Security, ACM CCS. Sections refer to `core.md`.

## Abstract

Agents that act through tools need a boundary that decides, executes and
records each action, and whose guarantees survive a compromised agent. We
present a reference monitor for agent tool use in which every stated guarantee
is tied, mechanically and in both directions, to a machine-checked theorem, a
runtime test, and a stated limit. We show that authorization must constrain the
effect, not only the tool and resource, and characterize exactly when that is
possible: precisely when acceptance is determined by what the boundary
observes. We prove that no redemption rule, even one that sees the world as
well as the proposal, separates a principal's proposal from an attacker's
identical one, so any intent system that leaves content unpinned faces a race.
We establish execution identity by two complementary mechanisms, each catching
an attack the other cannot, and compose the chain from authorized proposal to
attested state into a single theorem. [Results of a composition experiment with
a deployed defense withheld pending disclosure.]

## Introduction

An agent that can call tools can be made to call them for someone else.
Instructions injected into a document, a web page or a tool's output can choose
the agent's next action, so a deployment must assume that some proposals come
from an adversary. The natural defense is a boundary between the agent and its
tools: a reference monitor that decides each proposal, executes what it admits,
and records what happened. This paper asks what such a boundary can actually
guarantee, and answers with proofs, runtime evidence, and stated limits.

The first finding is that the usual unit of authorization is too coarse.
Granting an agent the right to write a particular report admits any write to
that path, including a hijacked agent's write with different content, and it
is redeemed by whichever proposal arrives first (Section 2). We define
authorization completeness, under which every admitted proposal that fits an
authorization is acceptable, and show it holds for intents that pin content,
jointly with the kernel's refusal of unruled arguments, which is necessary.

Contributions:

1. **Completeness, and the race it cannot avoid.** A mediated monitor whose
   authorizations are complete executes only acceptable effects
   (`CompletenessCalculus.safety`). No rule, even one seeing the world,
   separates identical proposals (`E24dRedemption.no_exact_rule`); premises
   withhold redemption until a named state, and the residual race is proved
   (Section 2).
2. **What any boundary can guarantee.** Completeness is possible exactly when
   acceptance is determined by what the boundary observes
   (`E24eLineage.complete_intent_exists_iff`); the faithfulness of generated
   content and the coverage of an agent's inputs lie beyond every such
   mechanism (Section 3).
3. **Execution identity, by two mechanisms.** The audit log and a path-bound
   attestation each identify the operation that produced a file; a foreign move
   defeats the first alone and a replay defeats the second alone, and each is
   caught by the other (Section 5).
4. **The chain as one theorem.** From an authorized proposal to the attested
   state of the world, for any path and content
   (`E28AuthorizedEffectIdentity.authorized_effect_to_attested_state`), with
   its one assumption about the broker checked at runtime (Section 5.4).
5. **Guarantees tied to evidence.** Every guarantee names a claim, every claim
   cites its theorems and tests, both directions are checked on every build,
   and ten mutations show each load-bearing check is guarded; the process
   found checks no test asserted (Section 7).

## Section order

1. Introduction. 2. Threat model and guarantees (core 1, 7). 3. Attacks and what
stops them: the redemption race (core 2), the move and the replay (core 5),
composition faults (core 6). 4. Why the guarantees hold (core 2 to 5).
5. Evaluation: runtime tests, mutation gate (core 7); composition (core 6).
6. Limits (core 8). Related work. Conclusion.
