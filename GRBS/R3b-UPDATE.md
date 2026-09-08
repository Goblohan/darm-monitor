# R3b Update — Stage I Complete: the Observational Characterization (both directions)

> Supersedes the "2a argued, not yet formalized" caveat in R3b-FINDING.md. Both
> directions are now machine-checked. Adds the Stage II (seL4 correspondence)
> program with correct scoping.

## Stage I — COMPLETE (machine-checked characterization pair)

The relationship of GRBS to assume-guarantee (AG) reasoning is now characterized
in both directions, within the explicitly defined observational model. Neither
result is a biconditional and neither claims AG universally subsumes DARM; each
states exactly what is proved.

### Above-interface reduction (2a) — `GRBS/AGReduction.lean`, axiom trace `[propext]`

The mediation semantics is a PARAMETER `M : (driven) -> (covered) -> Obs`, NOT
baked into the trace semantics. `CoverageSensitive M` (M's observable differs
between covered and uncovered on a driven channel) is an EXPLICIT HYPOTHESIS.

**Theorem `above_interface_reduction`.** For any coverage-sensitive `M`, an
interface action driving channel `d` (so `d` is interface-reachable, the driver
admissible), and coverage differing on `d`, the observable traces differ. Hence
AG-over-admissible distinguishes the two systems. The trace difference is DERIVED
from `CoverageSensitive`, not stipulated.

Scope, stated exactly: this does NOT claim "AG subsumes DARM above the
interface." It claims that a coverage-sensitive mediation effect on an
interface-reachable channel is AG-recoverable. The mediation-sensitivity is a
hypothesis, not a universal fact.

### Below-interface separation (2b) — `GRBS/AGBypass.lean`, ZERO axioms

**Theorem `grbs_isolates_latent_bypass`.** A channel in the physical footprint
but BELOW the interface (unmediated DMA class), a proved live hazard, makes two
systems interface-identical — AG-over-admissible cannot distinguish them — while
GRBS does.

### The characterization (exactly what is proved)

> Within the specified observational model, INTERFACE REACHABILITY characterizes
> whether a coverage difference is behaviorally exposed to assume-guarantee
> reasoning. Above the interface, with a coverage-sensitive mediation, AG
> recovers the distinction. Below the interface (latent physical channels), it
> cannot, and GRBS carries information AG does not.

Distinct predicates kept separate throughout (`ReachI`, `CoverageDiff`,
`CoverageSensitive`, observable difference, AG-distinguishability); no collapse
into a single "iff". The PRIMARY framing is observational: two systems can be
indistinguishable under the software-contract observation boundary while
differing in physical authority structure — the harder-to-attack claim.

## Stage II — seL4 concrete correspondence (PROPOSED, gated)

Not "hardware validation" — a concrete SEMANTIC CORRESPONDENCE / authority-
topology instantiation. Tests whether the abstract interface/footprint boundary
corresponds to REAL authority structure or is a toy-model artifact. Three
progressively harder mappings:

* **A. Abstract capability mapping.** `DARM Authority -> seL4 Capability`.
  Relatively manageable.
* **B. Structural boundary correspondence.** `DARM Cov(B,L,S) -> seL4
  CSpace/CNode topology`. Harder.
* **C. Full system authority correspondence.** `DARM Dep(G,S) -> {CNode, kernel,
  device, DMA, firmware, interrupt, MMIO, ...}`. This is where DARM's ambition
  actually lives.

Mapping only to CNode layouts would show "DARM maps onto capability systems" —
interesting but insufficient. The ambitious result is:

> DARM can distinguish capability confinement from complete system-level coverage
> when non-capability authorities remain capable of affecting the guarantee.

### The ambitious endpoint (preserved, NOT a scope reduction)

> **CNode confinement  ==>/  DARM system-level coverage**
>
> unless the relevant non-CNode authorities are themselves accounted for:
> `CapClosed(R) ∧ DMAClosed(R) ∧ MMIOClosed(R) ∧ FirmwareClosed(R) ∧
>  InterruptClosed(R)` may (depending on the actual system model) be sufficient
> for `GRBS(G,B,L,S)`.

DARM is not shrinking to "a capability-analysis tool." seL4 is one concrete
substrate on which to test the broader theory. Stage II asks: does the abstract
distinction (Stage I) survive contact with an actual high-assurance execution
substrate?

## The two-stage program

* **Stage I (done):** R3 -> 2a -> above-interface reduction + below-interface
  separation -> characterization. *What can AG recover, and where does the
  observational boundary become insufficient?* ANSWERED, machine-checked.
* **Stage II (proposed, gated):** DARM semantics -> seL4 capability semantics ->
  CNode/CSpace topology -> device authority -> DMA/MMIO/firmware -> physical
  authority closure. *Does the abstract distinction survive contact with a real
  substrate?* Requires seL4 semantics actually modeled; a separate research
  effort, not a continuation of Stage I.

## Where the program stands

R0 (Core ported, green, CI honest) · R1 (GRBS kernel, non-circular, non-vacuous)
· R3 (structural-dependence gate -> sensitivity-relative correction) · R3b/2a+2b
(AG characterization, both directions, machine-checked). Five machine-checked
results, each forced by proof, each scoped to exactly what it establishes.
Open next: Stage II (seL4 correspondence) and roadmap R4 (executable checker).
