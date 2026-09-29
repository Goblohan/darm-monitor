# Framing: formal-methods venue

Target: CAV, ITP, CPP.

## Abstract (draft)

We mechanize, in Lean 4, a calculus of authorization completeness for a
reference monitor mediating an agent's tool use. The central safety theorem is
proved from no axioms; an exact characterization shows that completeness is
possible precisely when acceptance is determined by what the boundary observes.
We connect authorization to effect through canonicalization and a typed effect
log, derive execution identity in two independent ways (through the log, and
through a path-bound attestation whose abstraction is the log model), and prove
when layered defenses back each other up. A reference implementation ties every
guarantee to a theorem at a pinned commit, a runtime test, and a mutation that
shows the test guards it.

## Section order

1. Introduction: why authorization needs a completeness notion; contributions.
2. The calculus (core 2), with its axiom profile.
3. The characterization and its limits (core 3).
4. From authorization to effect, and the refinement between effect models
   (core 4, core 5).
5. Composition (core 6), as theorems.
6. Case study: the reference implementation and the evidence discipline
   (core 7).
7. Limits (core 8). Related work. Conclusion.
