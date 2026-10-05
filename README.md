# DARM: Deterministic Algebraic Reference Monitor

**A machine-checked theory of bounded causal authority and admissible assurance transfer for autonomous systems.**

<!-- figures:start -->
| | |
| --- | --- |
| Lean modules | 250: 158 in `GRBS/`, every one built by the gate; 92 in `DarmMonitor/`, built or elaborated by CI |
| Theorems and lemmas | 1,629 |
| Lines of Lean | 47,524 |
| `sorry`, declared axioms | 0, 0 |
| Theorems the paper cites, each checked to exist | 83 |
<!-- figures:end -->

[DARM Guard](https://github.com/Goblohan/Darm-Guard) (the runtime) · [Limitations](LIMITATIONS.md) · [Module index](docs/MODULES.md) · [Paper draft](paper/core.md) · [Related work](paper/related.md) · [Cite](CITATION.cff)

**Olusanya Gbolahan V**
**PerceptraAI Lab**

---

## Overview

DARM (Deterministic Algebraic Reference Monitor) is a Lean 4 formalization and boundary theory for reasoning about guarantees in systems containing highly capable, potentially adversarial decision-makers.

Its central concern is not how intelligent an agent is, but **what the agent is mathematically authorized to cause within a specified system boundary**.

The working thesis:

> **DARM is a boundary-indexed assurance representation that makes the scope, authority, enforcement locus, and evidentiary basis of agent-system guarantees explicit, allowing unsupported expansion of a local guarantee into a broader system claim to be detected.**

---

## Core Research Question

> **Can an arbitrarily capable, potentially adversarial decision-maker be placed behind a mathematically specified authorization boundary that constrains the governed state transitions it may induce, without constraining the intelligence that selects those actions?**

DARM does not attempt to make an agent trustworthy. It asks whether a system can make the **consequences available to the agent** subject to explicit, mechanically checkable constraints.

---

## The Boundary Problem

A recurring failure mode in complex assurance arguments is the movement from a guarantee established at one boundary to a stronger claim at another boundary:

```text
Local guarantee
      |
      | unsupported expansion
      v
System guarantee
```

A property may be rigorously established over a local representation while the broader system contains state, actuators, tools, interfaces, environments, or dependencies not represented by that proof.

DARM treats this as a first-class formal problem. The question is not simply "Is the theorem true?" but also:

> **What exactly does the theorem establish, where is it enforced, what evidence supports it, and what larger claim is being made from it?**

---

## Assurance Transfer

The central DARM abstraction is **boundary-indexed assurance**. A guarantee is represented as:

```lean
Boundary → State → Prop
```

rather than merely `State → Prop`. This makes the boundary at which a guarantee is asserted explicit, and allows DARM to distinguish:

- the boundary where a guarantee was established
- the boundary where evidence originated
- the boundary where evidence is being used
- the authority permitting evidence movement
- the locus where enforcement occurs
- the broader boundary at which a final claim is made

### The Central Assurance Condition

DARM's transfer model:

```text
TransferAdmissible  ⟺  DeltaRepresented ∧ DeltaCovered ∧ DeltaDischarged
```

where the relevant boundary delta must be (1) represented by the assurance model, (2) covered by available evidence, and (3) discharged by an adequate guarantee or composition rule.

---

## Research Arc

The project follows a falsification-first methodology: each claim was formally attacked before being accepted, and negative results are reported as first-class findings.

### Phase 1 — Governance Boundary (DarmMonitor/)

Machine-checked authorization integrity, capability confinement against unrestricted adaptive adversaries, authority reachability, fail-closed fixed-point refinement, and adversarial trajectory safety. Negative results include: noninterference is false in the modeled channel; a rational surrogate for the exponential update loses semigroup structure; removing the ratification guard produces a concrete counterexample. See [FRAMING.md](FRAMING.md).

### Phase 2 — Assurance Transfer (GRBS/)

**R1.** The GRBS kernel establishes `Transfer ↔ GRBS` under explicit Exploitability and Dependence seams.

**R3 — Self-attack on the novelty claim.** R3d proved that interface-bounded AG cannot recover latent coverage (separation holds). R3e constructed PhysicalAG — an adversarial model given DARM's composite execution semantics — which recovers the semantic Transfer judgment. This falsified the stronger novelty hypothesis. The contribution shifted from "a new safety logic" to "an explicit assurance-transfer discipline."

**R4 — Dimension isolation.** Five independent attacks, each isolating one dimension:

| Attack | Dimension | Held constant | Obligation discovered | Axioms |
|--------|-----------|---------------|----------------------|--------|
| R4a | Scope | — | New component traces must satisfy G | Zero |
| R4b | Authority | Scope | Newly admitted traces must satisfy G | Zero |
| R4c | Locus | Scope + Authority | Newly passable traces must satisfy G | Zero |
| R4d | Evidence | Scope + Authority + Locus | Evidence gap must be filled (dischargeable) | Zero |
| R4e | Composition | — | Composed boundaries must be jointly adequate | Zero |

All five share the same structure: every new element introduced by a transition must independently satisfy the guarantee. All obligations were discovered from the attacks, not imported from DARM theory.

**R5 — Conservation synthesis.** `SourceAssured + DeltaObligation → TargetAssured`, with a concrete witness showing conservation failure when the obligation is undischarged.

**R6–R20 / DCEE.** Extended transfer theory (dependency monotonicity, non-monotonicity, representation interop, semantic correspondence) and systematic prior-art comparison against contract refinement, SACM, AEB, and compositional contract reasoning.

**Core Calculus.** Three-part transfer admissibility (`DARMCoreCalculus.lean`). Principal theorem: source assurance + DARM admissibility → target assurance.

**Boundary-indexed certificates (v0.14).** Boundaries as first-class indices, composition rules (positive and negative), authorized evidence transport, factorized composition, certificate integration.

### Phase 3 — From model to running code (GRBS/: K, B, E24–E34)

The theory is connected to an implementation, [DARM Guard](https://github.com/Goblohan/Darm-Guard), through three lines of work.

**The decision kernel (K1–K7).** K1 defines the kernel's decision function and proves its admission properties; K3 proves its correspondence to the earlier gate and ODATS results; K4 adds roles, and proves that payload cannot buy authority. K5 to K7 are theorems about the shipped server's own code: a reply decodes as an admission only if the kernel admitted (K5); the kernel canonicalizes the raw proposal and returns the invocation to execute (K6); and every reply carries the nonce of the request it answers (K7). The kernel binary is built by CI from a tagged commit and pinned by checksum in DARM Guard.

**The broker models (B1–B9).** The broker's behaviour, modelled: provenance the agent cannot vouch for (B1), the complete broker (B3), evidence before effect (B4), reconciliation (B5), compare-and-swap writes and tamper detection (B6), at-most-once retries (B7b), the typed audit log (B8), and crash-safe renames (B9).

**Effects and authorization (E24–E34).** Intents and their premises (E24 to E24d); execution identity and lineage (E27 to E30); remote effects (E31); the conditions under which an authorization transfers across a transformation, each shown necessary (E32 to E32d); attested channels (E33); and an assurance claim that survives implementation change (E34).

How DARM Guard's runtime corresponds to these models, claim by claim, and which bridges are proved and which are tested, is in its [assurance graph](https://github.com/Goblohan/Darm-Guard/blob/main/assurance/claims.json).

### Key Negative Results

The following are formalized as counterexamples, not gaps:

- **Boundary alignment does not imply semantic validity.** A rule may be correctly declared against a target boundary while still failing to establish the target guarantee.
- **Source guarantee + evidence + enforcement + authorization do not imply target guarantee.** An explicit composition rule is required.
- **Establishing a basis does not imply basis is adequate for the target.** Factorized composition separates these obligations.
- **Authorization to transport evidence does not imply authorization to transfer a guarantee.** Evidence movement is semantically distinct from assurance transfer.

---

## Axiom Audit

Principal theorems and their verified axiom dependencies:

| Theorem | File | Axioms |
|---------|------|--------|
| `behavioral_AG_cannot_recover_latent_coverage` | R3dBehavioralIsolation | **Zero** |
| `latent_coverage_is_not_behaviorally_visible` | R3dBehavioralIsolation | **Zero** |
| `physicalAG_implies_transfer` | AGCompleteness | **Zero** |
| `unsupported_scope_expansion` | R4aScopeExpansion | **Zero** |
| `assurance_conservation_failure` | R5AssuranceConservation | **Zero** |
| `physicalAG_implies_grbs` | AGCompleteness | propext, Classical.choice, Quot.sound |
| `target_assured_of_source_and_delta` | R5AssuranceConservation | propext, Classical.choice |
| `darm_admissibility_preserves_assurance` | DARMCoreCalculus | propext, Classical.choice |
| Governance core (capInvariant, coherence) | DarmMonitor/Basic | propext, Classical.choice, Quot.sound |

All results depend only on standard Lean 4 foundational axioms. No result depends on `sorryAx`.

---

## Repository Structure

```
darm-monitor/
├── GRBS/               assurance transfer (R), effects and authorization (E), the decision kernel (K),
│                       broker models (B), assume-guarantee (AG), runtime correspondence (IC),
│                       prior-art comparison (DCEE), the core calculus, seL4 authority
├── DarmMonitor/        the governance core: authorization, capability confinement, the fixed-point
│                       tower, boundary-indexed guarantees, composition rules, certificates
├── DarmMonitor.lean    the DarmMonitor library's root
├── Main.lean           darmdemo: the native differential test
├── c/                  the one hand-written native primitive, a fixed-point multiply, tested against Lean
├── camkes/, include/, interfaces/, qemu-run.sh   seL4/CAmkES wiring
├── empirical/          the empirical lab
├── paper/              the paper draft and related work; every theorem it cites is checked
├── archive/            modules set aside, each with its reason (archive/README.md)
├── scripts/            gate.sh, stats.py, modules_index.py, check_built.py, readme_figures.py
└── docs/MODULES.md     every module, described by its own header comment
```

Every module in `GRBS/` is a library root or imported by one, so the gate builds all of them. `DarmMonitor` is the default build target; CI elaborates its remaining modules one by one. `docs/MODULES.md` says how each module is checked.

## Reproducibility

```bash
git clone https://github.com/Goblohan/darm-monitor.git
cd darm-monitor

./scripts/gate.sh               # builds every GRBS module; checks the paper's citations and figures,
                                # the module index, and that no module is unbuilt or uses sorry
lake build                      # the DarmMonitor library's default build
python3 scripts/stats.py        # every figure above, at this commit

lake build darmkernel           # the decision kernel binary that DARM Guard runs
lake env lean DarmMonitor/BoundaryIndexedAssuranceCertificate.lean   # elaborate one module

# the native differential test: the C multiply against the proved Lean definition
"$(dirname "$(which lean)")/leanc" -c c/darm_native.c -o c/darm_native.o -O2
ar rcs c/libdarm_native.a c/darm_native.o
lake exe darmdemo

# C-ABI boundary test
gcc -Iinclude tests/test_darm_shim.c -o tests/test_darm_shim
./tests/test_darm_shim
```

## Continuous Integration

Every push runs these workflows; every step runs with `pipefail`, so a failing command fails its step.

**GRBS library** runs `scripts/gate.sh`: every `GRBS` module built, every theorem the paper cites checked to exist, the paper's figures and this README's checked against the repository, the module index checked against the code, and no module left unbuilt.

**Lean Action CI** builds the default target and fails on `sorryAx` in any axiom trace or on fewer than a floor of axiom traces; elaborates every module outside the default build, file by file; and runs the native differential test, failing on any divergence.

**DARM C-ABI Gate** builds and executes the C-ABI boundary tests. It installs QEMU dependencies but does not currently execute a QEMU test; no QEMU execution claim is made.

**Kernel Release** builds `darmkernel` on a `kernel-v*` tag and publishes it with its SHA-256, which DARM Guard pins.

Until commit `0e14b75`, the workflows ran without `pipefail`, so a module that failed to compile in the complete-corpus step was printed but did not fail the run. One module had been failing that way since it was committed; it is archived with the reason in `archive/README.md`. Every other module compiled.

## Relationship to Existing Work

DARM is a **boundary and assurance-accounting layer**, not a replacement for existing verification, security, or safety mechanisms. It is compatible in principle with reference monitors, access-control systems, capability systems, formal verification, runtime enforcement, microkernels, safety cases, assume-guarantee reasoning, compositional verification, separation kernels, and cryptographic attestation.

Recent related work includes formal containment verification modeling the AI as an unconstrained oracle over typed action spaces ([arXiv:2605.09045](https://arxiv.org/abs/2605.09045)), and runtime contract enforcement for agent safety ([arXiv:2608.11274](https://arxiv.org/abs/2608.11274)). DARM's distinctive question is narrower than containment and broader than contracts:

> **When an assurance claim crosses a system boundary, what exactly licenses that transfer?**

The R3e result is relevant here: DARM's PhysicalAG construction demonstrated that the semantic safety conclusion is recoverable by sufficiently rich assume-guarantee reasoning. The contribution is therefore not a new safety logic but an explicit representation of the transfer conditions — scope, authority, enforcement locus, evidentiary basis — that must be discharged for the conclusion to legitimately cross a boundary.

---

## What DARM Is Not

- a deployed reference monitor
- a complete autonomous-system safety architecture
- a claim that formal verification eliminates all system risk
- a proof of physical-world safety
- a claim that semantic adequacy is automatically obtained from boundary alignment
- a claim that evidence transport implies guarantee transport
- a claim that GRBS is a fundamentally new semantic safety logic (R3e weakened this)
- a claim that no existing framework can represent the same assurance structure

The formal results are conditional on their stated definitions, assumptions, and models.

---

## Version History

| Tag | Milestone |
|-----|-----------|
| `v1.0.0` | Governance core |
| `v0.9`–`v0.13.6` | Empirical lab + formal adequacy |
| `v2.0.0` | Theoretical core complete |
| `v2.1.0` | Runtime correspondence (IC1, R21, R22), TMC refinement (E23), R4e/R19b/R20 interop |
| `kernel-v0.2.0` | Decision kernel with roles (K4), released for DARM Guard |
| `kernel-v0.3.0` | The kernel canonicalizes the raw proposal (K6) |
| `kernel-v0.4.0` | Every reply bound to its request by a nonce (K7) |

Since `v2.1.0`, untagged on `main`: the kernel's wire contract and canonicalization (K5 to K7), the broker models (B4 to B9), effects and authorization (E24 to E34), and the gate's checks on every module, the paper and this README.

## Guiding Principle

> **When a system claims that an assurance established somewhere applies somewhere else, where is the mathematical bridge?**

If that bridge cannot be represented, justified, and checked, the broader claim should not inherit the narrower guarantee merely because the architecture, authority structure, or terminology makes the transfer appear plausible.

---

**Olusanya Gbolahan V**
**PerceptraAI Lab**

[https://github.com/Goblohan/darm-monitor](https://github.com/Goblohan/darm-monitor)

## License

Apache License 2.0: see [LICENSE](LICENSE) and [NOTICE](NOTICE). Contributions are accepted under the
[Developer Certificate of Origin](CONTRIBUTING.md). The names DARM, DARM Guard and PerceptraAI are not
licensed under it (Apache-2.0, section 6).
