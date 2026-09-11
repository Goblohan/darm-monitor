# R3e Finding: Physical Assume-Guarantee Completeness

## Objective

R3e attacks the remaining strong novelty hypothesis for GRBS: whether guarantee-relative boundary coverage constitutes a semantic reasoning capability that cannot be recovered by an assume-guarantee analysis given sufficiently rich composite execution semantics.

## R3e-1: Unrestricted Physical AG

`GRBS/AGCompleteness.lean` defines `PhysicalAG`, which reasons over the same environments, traces, and safety relations used by DARM `Transfer`.

Crucially, `PhysicalAG` contains no `cov` and no `GRBS` parameter.

The machine-checked theorem `physicalAG_implies_transfer` establishes:

```text
PhysicalAG + admissibility of A => Transfer
```

The theorem does not depend on any axioms.

## R3e-2: Recovery of GRBS

The machine-checked theorem `physicalAG_implies_grbs` establishes:

```text
PhysicalAG + admissibility of A + Exploitability + Dependence => GRBS
```

This follows through the existing necessity result `Transfer => GRBS` under the two explicit DARM seam hypotheses.

The theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`, and does not depend on `sorryAx`.

## Finding

R3e defeats the stronger claim that GRBS is a fundamentally new semantic safety logic unavailable to sufficiently strong assume-guarantee reasoning.

Our `PhysicalAG` construction demonstrates that an assume-guarantee analysis given the same composite execution semantics (DARM's `Envs`, `Traces`, and `Safe`) can establish the same semantic `Transfer` judgment. This is recoverability in a constructed model, not a theorem about arbitrary AG frameworks. With the explicit `Exploitability` and `Dependence` conditions used at the DARM seam, the construction can also recover the GRBS conclusion.

Therefore the contribution should not be characterized as: AG cannot express GRBS. That claim is not supported by the formal results.

## Relationship to R3d

R3d established a complementary result. Under the explicitly restricted interface behavioral observation boundary, two systems can be observationally indistinguishable to every admissible AG assumption while their GRBS status differs.

Thus:

```text
Interface-bounded behavioral AG:
cannot recover latent coverage information in the R3d witness.

PhysicalAG given the constructed composite semantics:
can recover the semantic Transfer judgment and, with the DARM seams,
derive the GRBS conclusion in the R3e model.
```

These results are not contradictory. They identify the role of the observation boundary.

R3d therefore establishes an observation-boundary limitation, while R3e establishes semantic recoverability once the behavioral analysis is given sufficiently rich composite execution semantics.

## Revised Novelty Position

The strongest remaining DARM claim is therefore not a new semantic safety logic.

The candidate contribution is an explicit assurance-transfer discipline in which:

1. A guarantee is associated with an explicit dependency set.
2. A boundary and enforcement locus define what dependencies are covered.
3. `Dep(G,S) subset Cov(B,L,S)` is represented explicitly as GRBS.
4. Assurance transfer across a boundary is treated as a separate judgment rather than inferred merely from a local guarantee.
5. Boundary obligations can be inspected, tested, and rejected when required authority lies outside enforcement coverage.
6. Latent authority or physical bypasses can be represented as failures of coverage rather than hidden inside an implicit behavioral assumption.

## Semantic vs Assurance-Structural Equivalence

R3e establishes semantic recoverability, not equivalence of assurance representation.

Our constructed AG model can establish `Transfer` without explicitly naming `Dep`, `Cov`, `Boundary`, or `Locus`.

GRBS instead makes the corresponding coverage condition a first-class object:

```text
GRBS(G,B,L,S) := Dep(G,S) subset Cov(B,L,S)
```

The distinction is therefore between a semantic safety conclusion and an explicit assurance-transfer structure.

R3e does not prove that this structure is absent from all existing assurance, contract, capability, or safety frameworks.

## Scientific Verdict

R3e is a negative result against the strongest version of the DARM novelty hypothesis.

The defensible research question is now:

> Does making guarantee-relative dependency, boundary coverage, enforcement locus, and assurance transfer explicit provide a useful formal discipline for detecting invalid scope expansion across assurance boundaries, beyond what existing behavioral or assurance representations provide implicitly?

That question remains open.

It must be evaluated against prior work in assume-guarantee reasoning, contract refinement, assurance cases, reference monitors and complete mediation, capability confinement, runtime assurance, hardware and execution-boundary assurance, and systems for autonomous-agent action authorization.

## Evidence Status

- `physicalAG_implies_transfer`: machine-checked.
- `physicalAG_implies_grbs`: machine-checked.
- Principal R3e theorems contain no `sorryAx`.
- Local standalone Lean compilation succeeds.
- Full repository build succeeds.
- The finding is a formal research result, not evidence that the remaining assurance-structural contribution is novel.

## Scope Discipline

R3e does not establish:

- that GRBS is universally novel;
- that no existing framework can represent the same assurance structure;
- that existing AG frameworks cannot be extended with explicit coverage;
- that DARM is superior to existing assurance frameworks;
- or that the proposed assurance-transfer discipline has yet been validated on a deployed physical system.

Those questions require separate formal comparison, literature analysis, and empirical evaluation.
