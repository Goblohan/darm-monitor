# DARM: Deterministic Algebraic Reference Monitor

**A machine-checked theory of bounded causal authority and admissible assurance transfer for autonomous systems.**

190 Lean 4 modules · 36,000+ lines · 1,141 theorems · zero `sorry` · zero `sorryAx` · CI-green

**Olusanya Gbolahan V**
**PerceptraAI Lab · Lagos**

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
│
├── DarmMonitor/              91 modules — verified governance core
│   ├── Basic.lean                Authorization, capability confinement
│   ├── Fixed64*.lean             Fixed-point proof tower
│   ├── Boundary*.lean            Boundary-indexed guarantee system
│   ├── Composition*.lean         Composition rules (positive + negative)
│   ├── Assurance*.lean           Certificates and transport
│   ├── Reachability*.lean        Authority reachability calculus
│   ├── LLMToolCall.lean          Agent tool-authorization instantiation
│   └── ...                       Minimality, interference, trajectory safety
│
├── GRBS/                     99 modules — assurance-transfer theory
│   ├── GRBS.lean                 R1: Frame, Transfer, GRBS, Exploitability
│   ├── R1bSufficiency.lean       Transfer ↔ GRBS biconditional
│   ├── AGBypass.lean             Below-interface structural isolation
│   ├── AGCompleteness.lean       PhysicalAG semantic recoverability
│   ├── R3dBehavioralIsolation.lean  Behavioral AG limitation
│   ├── R4a–R4f*.lean            Dimension-isolated transfer attacks
│   ├── R5*.lean                  Assurance conservation synthesis
│   ├── R6–R20*.lean              Extended transfer theory
│   ├── DCEE*.lean                Prior-art comparison suite (11 files)
│   ├── DARMCoreCalculus.lean     Assurance-transfer calculus
│   └── SeL4*.lean                seL4 authority model and separation
│
├── c/                        C-ABI boundary layer
├── camkes/                   seL4/CAmkES microkernel wiring
├── empirical/                Empirical lab (v0.1–v0.12)
├── .github/workflows/        Lean CI + C-ABI gate
│   ├── lean_action_ci.yml        Full corpus elaboration + axiom audit
│   └── ci.yml                    C-ABI boundary gate
├── FRAMING.md                Governance boundary framing document
└── lakefile.lean             Build configuration
```

The lakefile registers four GRBS roots (`GRBS`, `SeL4GRBS`, `AGBypass`, `DARMCoreCalculus`). Research modules outside the integrated import closure are elaborated individually by the CI pipeline, which dynamically discovers and checks the complete corpus.

---

## Reproducibility

```bash
# Clone
git clone https://github.com/Goblohan/darm-monitor.git
cd darm-monitor

# Full proof verification
lake build

# Build specific GRBS roots
lake build GRBS
lake build SeL4GRBS
lake build AGBypass
lake build DARMCoreCalculus

# Elaborate a specific module
lake env lean DarmMonitor/BoundaryIndexedAssuranceCertificate.lean

# Run the demonstration
lake exe darmdemo

# C-ABI boundary test
gcc -Iinclude tests/test_darm_shim.c -o tests/test_darm_shim
./tests/test_darm_shim
```

---

## Continuous Integration

Every push triggers two automated gates:

**Lean Action CI** — Integrated build, axiom audit (searches for `sorryAx`), axiom-trace count floor, complete DARM corpus elaboration, complete GRBS corpus elaboration, native library compilation, runtime differential testing.

**DARM C-ABI Gate** — Builds and executes C-ABI boundary tests. Installs QEMU dependencies but does not currently execute a QEMU test; no QEMU execution claim is made.

---

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

---

## Guiding Principle

> **When a system claims that an assurance established somewhere applies somewhere else, where is the mathematical bridge?**

If that bridge cannot be represented, justified, and checked, the broader claim should not inherit the narrower guarantee merely because the architecture, authority structure, or terminology makes the transfer appear plausible.

---

**Olusanya Gbolahan V**
**PerceptraAI Lab · Lagos**

[https://github.com/Goblohan/darm-monitor](https://github.com/Goblohan/darm-monitor)
