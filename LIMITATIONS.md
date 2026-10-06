# What DARM does not prove

Every result in DARM is conditional on its stated definitions, assumptions and models. This page gathers, in
one place, the limits an evaluator should know before relying on any of them.

## Theorems are about models

Every theorem here is about a Lean model. Whether a model describes running code is a separate claim, and its
strength differs by component:

- **The decision kernel** is the model compiled: the binary DARM Guard runs is built by CI from a tagged commit,
  and K5 to K7 are theorems about the shipped server's own code. What remains trusted is the Lean compiler and
  runtime, the JSON parser and the server's input loop.
- **The broker** is modelled (B1 to B9), and DARM Guard's runtime is **tested** against those models, not proved.
  Its [assurance graph](https://github.com/Goblohan/Darm-Guard/blob/main/assurance/claims.json) states the bridge
  of every claim, and its [LIMITATIONS.md](https://github.com/Goblohan/Darm-Guard/blob/main/LIMITATIONS.md) each
  claim's limit.
- **The native layer** is one hand-written C primitive, a fixed-point multiply, differentially tested against the
  proved Lean definition on every push. Its source names it, the C compiler and the FFI conventions as trusted.
- **No hardware is governed.** `HardwarePort` and the `Fixed64` tower are models of hardware arithmetic, not a
  deployed control layer.

## Negative results that bound the theory

These are formalized as counterexamples, not gaps:

- Boundary alignment does not imply semantic validity.
- Source guarantee, evidence, enforcement and authorization together do not imply the target guarantee; an
  explicit composition rule is required.
- Establishing a basis does not imply the basis is adequate for the target.
- Authorization to transport evidence does not imply authorization to transfer a guarantee.
- Noninterference is false in the modelled channel; a rational surrogate for the exponential update loses
  semigroup structure; removing the ratification guard yields a concrete counterexample.
- R3e: sufficiently rich assume-guarantee reasoning recovers the semantic Transfer judgment. DARM's contribution
  is therefore an explicit representation of transfer conditions, not a new safety logic.

## Assurance under change

E34 proves that a property local to its reviewed cones holds of every version its gate accepts. Its
`gate_incomplete` theorem exhibits a property-preserving change rejected by that equality-based gate;
it does not prove an impossibility theorem for all code-based gates. Applied to DARM Guard, preservation rests on four
assumptions: each acceptance follows a correct review; the analysis sees every dependency that static analysis
of the package can see (not monkeypatching from outside it, nor behaviour below Python); equal fingerprints mean
equal code; and equal code behaves equally in the same environment. That DARM Guard's cones are local is shown by
design and by attack, not proved.

## The trusted base

- The Lean kernel, and the standard axioms `propext`, `Classical.choice` and `Quot.sound`, which most results
  use: the corpus is classical, not purely constructive. Each theorem's axioms are printed in the build log.
- Mathlib, for the `DarmMonitor` library's arithmetic.
- For the kernel binary: the Lean compiler and runtime. For the native primitive: the C compiler and the FFI.

## What the build checks, and what it does not

- Every module is elaborated on every push: the gate builds all of `GRBS/`, CI builds the `DarmMonitor` library and
  elaborates its remaining modules one by one, and fails on `sorryAx` in any axiom trace.
- Until commit `0e14b75`, the workflows ran without `pipefail`, so a module that failed to compile in the
  complete-corpus step was printed but did not fail the run. One module had failed that way since it was
  committed, and is archived with the reason in [archive/README.md](archive/README.md).
- The gate checks that every theorem the paper cites exists in a built module. It does not check that the
  paper's prose describes the theorem correctly; that is the reader's and the reviewer's to judge.
- Theorem counts are declarations written in the source, not the constants Lean generates.

## Out of scope

Physical-world safety; the trustworthiness or intelligence of the agent; information-flow security; the semantic
adequacy of a chosen boundary; complete mediation in a deployment; and anything a stated assumption excludes.
