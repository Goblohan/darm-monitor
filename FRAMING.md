# DARM — A Machine-Checked Formal Boundary Theory for Deterministic Governance

## What DARM is

DARM is not another reference monitor, an AI-safety system, or a capability
framework. It is a machine-checked formal boundary theory for deterministic
governance: a study of how far a mathematically specified authorization boundary
can constrain what an agent is permitted to *do*, without constraining the
intelligence that selects those actions.

## The central question

> Can an arbitrarily capable, potentially adversarial decision-maker be placed
> behind a mathematically specified authorization boundary that constrains the
> governed state transitions it may induce — without constraining the
> intelligence that selects those actions?

This distinction is the whole point. DARM does not attempt to control what an
agent thinks, imagines, plans, or reasons about. The intelligence can scale.
DARM constrains what the agent is authorized to *cause* through a governed
action interface.

**"Cause" is defined operationally, and narrowly:** to cause is to induce a
transition represented by the governance model. DARM makes no claim about
arbitrary downstream physical, social, informational, or side-channel
consequences. This scope is a feature, not a caveat — the boundary is drawn
exactly where the mathematics can hold it, and nowhere further.

## The four layers

The research program has four layers, each corresponding to results already
established in the machine-checked model.

**1. Authorization.** Formally specify capabilities, policies, actors,
suspension, ratification, and permitted transitions. Which transitions can break
which invariants, and under what conditions they are preserved.

**2. Authority.** Model quantitative authority separately, through a continuous
margin / partition-function calculus, and characterize which authority
configurations are mathematically realizable — including where the realizable
set is provably bounded and where a natural bound is reached only in degenerate
cases.

**3. Composition.** Determine which desirable properties survive composition and
which are impossible under explicit assumptions. DARM's negative results are
first-class results, not gaps:
- noninterference is *false* in the modeled channel, and is formally independent
  of core integrity;
- a state-independent algebraic bridge between the discrete and continuous
  strata collapses (an injective update composed with a state map is constant
  only if the map is);
- a rational multiplicative surrogate for the exponential update fails to
  preserve semigroup structure, so history-independence is lost;
- a natural typeclass abstraction removes expressiveness rather than adding it,
  and would be uninhabited if made to carry the false or rejected properties.

**4. Refinement.** Transport the surviving mathematical safety properties from
real-valued specifications into computable fixed-point arithmetic, and eventually
native execution — while explicitly separating proved guarantees from tested
implementation behavior. Rounding is proved fail-closed; the native boundary is
differentially tested, not proved, and the trusted computing base is stated
precisely.

## What authorization integrity is *not*

The crucial conceptual insight: authorization integrity is not the same thing as
alignment, confidentiality, or noninterference. DARM does not claim to solve
those problems. It asks a narrower, sharper question — what deterministic
guarantees remain possible when the agent itself is treated as an arbitrary
action selector, and where those guarantees provably end.

## Relationship to existing systems

- **Capability systems** establish powerful authorization mechanisms.
- **Formal kernels** (e.g. seL4) prove concrete implementation properties.
- **Information-flow systems** address confidentiality and noninterference.

DARM occupies a different research position. It studies the *formal boundary of
deterministic governance itself* — where composition succeeds, where it provably
fails, and where the proof ends. Its distinctive contribution is treating the
limits as results: a map of what deterministic authorization can and cannot
guarantee, with the boundaries proved rather than asserted.

## Current status, stated honestly

The current work establishes machine-checked results for:
- the modeled discrete transition system (authorization integrity, capability
  confinement, suspension, execution blocking);
- authority reachability (the margin calculus, the capacity bound and its sharp
  and design-time forms);
- compositional boundaries (the negative results above, each with a proof or a
  countermodel);
- conservative refinement (fail-closed fixed-point arithmetic, a quantified
  evaluator over 64-bit fixed point, and a running executable).

Native behavior is *separately tested*, not conflated with theorem proving. The
executable runs and passes a differential test against the verified
implementation on tens of thousands of inputs; that is a trust boundary made
testable, not a proof.

**All principal results carry a permanent `#print axioms` declaration.** A green
build is not evidence — a build succeeds on a file full of `sorry`. The axiom
trace is the evidence. No traced result depends on `sorryAx`.

## Phase 2 — proposed, not yet established

The current results concern single governed transitions. The hardest remaining
question, and the direction Phase 2 *would* attack, is trajectory safety:

> Does the authorization boundary remain safe against genuinely adversarial,
> adaptive, multi-step agents whose future actions depend on the history they
> observe?

Coherence is currently proved for a single step, not for folded execution
traces. Extending it to trajectories — proving the boundary holds under an
adaptive agent optimizing against the history it observes — is *open*. It is
named here as the research program's next target, not as an established result.
Turning DARM from a collection of verified mechanisms into a theory of
trajectory safety under scalable intelligence is future work.

## In one sentence

DARM studies how far deterministic governance can constrain what an arbitrarily
intelligent agent is authorized to *cause* through a governed interface —
mathematically, without needing to constrain the intelligence itself — and maps
precisely where that governance holds, where it provably fails, and where the
proof ends.
