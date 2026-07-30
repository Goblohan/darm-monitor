# DARM — Deterministic Algebraic Reference Monitor

A machine-checked formal specification of reference-monitor governance, in Lean 4
against Mathlib (toolchain `leanprover/lean4:v4.32.0`).

DARM is a **specification kernel**, not a runtime. It contains no hardware
abstraction layer, no cryptographic implementation, and no C or Rust drivers. What
it contains is the invariant structure a deployable monitor would have to satisfy,
proved rather than asserted.

## Verification discipline

Every principal result carries a permanent `#print axioms` declaration in the
source. That is deliberate: `lake build` exits 0 on a file full of `sorry`, so a
green build alone is not evidence. The axiom trace is.

```
lake build
```

Census the evidence yourself:

```
findstr /s /n /c:"sorry" DarmMonitor\*.lean          # should return nothing
lake build 2>&1 | findstr /i "axioms sorryAx"        # every trace, in one place
```

Traced results depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Several depend on strictly fewer; a few depend on nothing at all. There are no
custom axioms and no `sorryAx` anywhere.

**A note on why this discipline exists.** During development, `lake build`
reported success on 604 jobs while never compiling the module everyone believed was
verified — the root did not import it, so it sat on disk unchecked, and CI was
green for three commits on that basis. The `#print axioms` lines and the root-import
check are the guards added afterwards. A passing build is not evidence unless the
build target provably includes the artifact under test.

## What is proved

### Discrete authority (`Basic.lean`)

A capability-and-policy state machine with actor-classified events. Capability
confinement, policy monotonicity under agent events, suspension as an absorbing
state, and execution blocking. Capability is **causally live**: `allowedActions`
filters the policy by whether the required capability is held, so
`execution_confined_by_cap_bound` states that an executable action's required
capability lies inside the externally supplied bound.

### Continuous boundary (`BoundaryMargin.lean`)

`safe_signal_equiv` collapses an O(n) family of per-coordinate margin constraints
into a single scalar bound on the partition function `Z`. `transportSupp` is the
corollary: a safe update preserves the active set — as a subset, not an equality,
so resurrection of inactive coordinates is permitted.

### Cross-stratum composition (`StratumComposition.lean`)

Coherence — every permitted action is backed by a weight coordinate above the
margin floor — is preserved by any agent event paired with a Z-safe update. The
bridge is set-theoretic rather than algebraic, deliberately: `policy` is **not**
derived from the weight vector, because deriving it would force the reference
monitor to evaluate real arithmetic to answer "is this action permitted".

An algebraic bridge is not merely inconvenient but degenerate — see Negative
Result 2 below.

### Ratification (`Ratification.lean`, `StrictExpansion.lean`, `NontrivialExpansion.lean`, `Reachability.lean`)

Exactly one transition can break coherence: ratification, which assigns a policy
outright. The results form a complete qualitative picture of that channel.

- Unguarded ratification breaks coherence, with a **valid** token — so the defect
  is in policy semantics, not authentication.
- The guard `newPolicy ⊆ active δ w` is sufficient to preserve coherence.
- Guarding leaves the computable fragment: `Ratifiable` requires `noncomputable`,
  which the compiler establishes rather than the prose.
- A Z-safe update monotonically expands the guard's admissible policy space, and
  the expansion is not vacuous — witnesses exist under pure renormalization
  (`η = 0`) and under genuine multiplicative reweighting (`η = 1`).
- Growth is **capped**: at most `1/δ` coordinates can be active after
  normalization, whatever signal is synthesized. Expansion is possible but bounded.

### Influence and noninterference (`Interference.lean`, `Influence.lean`)

Noninterference is defined over an arbitrary transition system with an
admissibility predicate on actions, and characterized as constancy of the
ratifier's verdict on each admissible image. Both discrete models in this
repository are instances.

Instantiated on the reference monitor itself, noninterference **fails**: two agent
events produce states an observer of the policy can distinguish.

### Assumption registry (`Assumptions.lean`, `Minimality.lean`)

| | Assumption | Status |
|---|---|---|
| A1 | Token unforgeability | Formalized. Proved *independent* of coherence preservation |
| A2 | External capability bound | Behavioural via gating; content is `execution_confined_by_cap_bound` |
| A3 | Single-writer semantics | Not an assumption — encoded in `step` being a function |
| A4 | Causal isolation | Formalized as a condition; satisfiable, and false for the modelled channel |
| A5 | Well-formed weights | Formalized; non-negativity proved necessary, positive mass proved droppable |

Each formalized assumption comes with both a witness and a countermodel. An
assumption true in every model admits no necessity proof; one true in none makes
every theorem conditioned on it vacuous.

**Minimality cells proved so far** — necessity requires a model where the
hypothesis fails and the conclusion fails with it, so an unproved "necessary" is
an assertion:

- A5 non-negativity is necessary for the capacity bound
- The safety certificate is necessary for support transport
- `actor e = Actor.agent` is necessary for coherence preservation
- A5 positive-mass is **not** necessary for the capacity bound
- A1 is independent of coherence preservation
- Capability confinement is independent of noninterference

That last pair matters: bounding what the agent can *do* does not bound what the
agent can cause the ratifier to *see*.

## Negative results

Reported with the same prominence as the positive ones.

**NR1 — noninterference is false.** Not merely unproved. It fails in the modelled
channel, and core integrity does not imply it; the two properties are formally
independent.

**NR2 — no state-independent algebraic bridge.** Mapping discrete states to weight
vectors via `interp`, and demanding `interp (step s a) = reweight … (interp s)`, is
degenerate. `reweight` multiplies coordinatewise by `exp(…) > 0` and is therefore
injective, while the discrete step collapses distinct sources to the same target;
an injective map composed with `interp` is constant only if `interp` is. Allowing
the signal to depend on the source state dissolves the obstruction — so this bounds
*state-independent* synthesis specifically.

**NR3 — ratification is the sole coherence-breaking transition**, and it is the one
whose holder A4 says the agent can influence without bound.

## Deliberate non-claims

- Not a runtime binary. No drivers, no hardware abstraction layer.
- Not a cryptographic implementation. Token validity is an opaque predicate.
- Not a claim about real ratifiers. A4 concerns the modelled observation channel
  only, and says nothing about human cognition or persuadability.
- Not a claim of physical soundness. Sensor and environment behaviour are outside
  the model entirely.

## Open problems

- **R1b** — the exact reachability characterization. Conjectured: a target active
  set `B` is reachable by a Z-safe update iff `δ|B| < 1`. The upper bound is
  proved; the converse needs the ε-construction and `Real.log`.
- Trace-level composition. Coherence is proved for a single step, not for
  `List`-folded execution traces.
- A constrained ratification rule. Whether requiring `newPolicy ⊆ active δ w` at
  ratification time is acceptable, given that it makes human authority contingent
  on a machine-computed bound.
- Most necessity cells. Six are proved; a full matrix over five assumptions and the
  principal theorems needs many more, each with its own countermodel.

## Layout

```
DarmMonitor.lean            root; imports every verified module
DarmMonitor/
  Basic.lean                discrete authority core, capability gating
  BoundaryMargin.lean       O(n) -> O(1) margin collapse, support transport
  StratumComposition.lean   cross-stratum coherence
  Ratification.lean         the coherence-breaking transition and its guard
  StrictExpansion.lean      non-vacuity witness, eta = 0
  NontrivialExpansion.lean  non-vacuity witness, eta =/= 0
  Reachability.lean         capacity bound on the active set
  Influence.lean            minimal observation-channel example
  Interference.lean         general noninterference; A4 on the monitor itself
  SemanticQuotient.lean     semantic equivalence relation
  SemanticExpansion.lean    semantic image expansion
  Assumptions.lean          A1-A5 as predicates, with witnesses and countermodels
  Minimality.lean           necessity and independence cells
```

The root imports every module, so a green build covers all of them. This was not
always true, and the correction is in the commit history.
