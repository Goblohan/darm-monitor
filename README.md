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

Three tiers, in increasing strength:

```
# 1. placeholder search — necessary, not sufficient
findstr /s /n /c:"sorry" /c:"admit" DarmMonitor\*.lean

# 2. axiom audit — this is the actual evidence
lake build 2>&1 | findstr /c:"depends on axioms"

# 3. build audit — reproducibility on a clean machine, every commit via CI
lake build
```

Tier 1 catches typed placeholders in this repository's own source. Tier 2 catches
anything reaching a theorem *through its dependencies*, which a text search
structurally cannot. Tier 2 is the claim worth making.

Traced results depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Several depend on strictly fewer; a few depend on nothing at all. No traced result
depends on `sorryAx`, and none introduces a custom axiom. Occurrences of the string
`sorryAx` in the source are module-header discipline notes, not proof obligations.

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
- The reweighting channel is **surjective** onto positive vectors — any positive
  target is hit exactly by some `loss`, with no finiteness hypothesis. So the cap is
  not a limitation of the update rule; it is a property of the margin floor under
  normalization, and no choice of signal evades it.
- The cap is **strict** for proper subsets: `δ * |B| = 1` is unreachable unless `B`
  is the whole index space.

### Influence and noninterference (`Interference.lean`, `Influence.lean`)

Noninterference is defined over an arbitrary transition system with an
admissibility predicate on actions, and characterized as constancy of the
ratifier's verdict on each admissible image. Both discrete models in this
repository are instances.

Instantiated on the reference monitor itself, noninterference **fails**: two agent
events produce states an observer of the policy can distinguish.

### Instantiations (`LLMToolCall.lean`, `CIRunner.lean`)

Two independent instantiations of the discrete stratum. An LLM tool-caller granted
filesystem-read and network access provably cannot execute shell or email; a CI
pull-request runner provably cannot deploy or roll back. The inherited theorems
apply with no new proof content — that is what makes them evidence the abstraction
is reusable rather than retrofitted.

`CIRunner`'s permission map is deliberately many-to-one, which shows gating does not
depend on injectivity, and surfaces an expressiveness limit.
`deploy_rollback_inseparable` proves that actions sharing a permission are
capability-indistinguishable, so a posture like "allow rollback but not deploy"
cannot be expressed through capabilities at all. It can only be expressed through the
policy channel — which agent events may shrink but only ratification may widen, and
ratification is the sole coherence-breaking transition.

**Both instantiations reject the continuous stratum.** Neither domain has a
conserved, multiplicatively-updated authority measure, so the margin floor, the
O(n) to O(1) collapse, and the capacity bound have no interpretation for either.
Candidate weight semantics and why each fails are recorded in `LLMToolCall.lean`.
The discrete stratum is a general-purpose reference monitor; the continuous stratum
is domain-specific. A claim that DARM as a whole applies to LLM tool-calling would be
false.

### Reuse without abstraction (`Deployment.lean`)

Both instantiations hand-wrote the same unreachability argument — four proofs
differing only in constants. `never_executable_of_ungranted` replaces all four: an
action whose permission was never granted can never execute in any
capability-confined state, whatever the policy says. A third instantiation would
need no bespoke proofs.

**This settles the typeclass question, negatively.** A `ReferenceMonitor` class
keyed on `(CapId, ActionId, Token)` admits one instance per type triple, so it
cannot quantify over two deployments sharing an action space.
`unreachable_antitone` does exactly that — tightening a grant can only enlarge what
is permanently unreachable — and would become unstatable. The abstraction would
remove expressiveness rather than add it. A class field carrying noninterference or
the Z-bound would be worse still: the first is false in the base model, the second
is rejected by both instantiations, so the class would be uninhabited.

### Execution (`Runtime.lean`, `FixedPoint.lean`, `ActiveSurrogate.lean`)

The discrete monitor **runs**. `Basic.step` is total and computable, and both
instantiations are finite enumerations, so Lean emits C for the whole fragment.
`canRun_iff_canExecute` ties the emitted `Bool` to the proved `Prop`, which is what
makes `bash_canRun_false` a statement about the running program rather than about a
separate mathematical object. The demo prints:

```
grant: fsRead, network
readFile: ALLOWED
writeFile: BLOCKED
bashExec: BLOCKED
httpGet: ALLOWED
sendEmail: BLOCKED
```

The continuous stratum **does not extract**. `reweight`, `normalize`, `active`, and
`Ratifiable` are all `noncomputable`, because `Real` in Lean is a quotient of Cauchy
sequences with no code generation. Re-implementing the certificate in C would put
unverified arithmetic between the proofs and the binary.

The resolution is not to extract ℝ but to refine it. `FixedPoint.lean` defines a
computable fixed-point model with an embedding `γ` into the reals, and
`refinement_coord` proves the computable check **fail-closed**: passing it implies
the real inequality `δ * Z ≤ w'`. Rounding can make the check reject a state that is
safe in ℝ — a false negative — but cannot make it accept a state that is unsafe.
`ActiveSurrogate.refinement_quantified` lifts this to the quantified certificate via
a computable over-approximation of the active set.

Three findings from building it, each against the initial design:

- **Truncation error is eliminated, not bounded.** The fixed-point product lands on
  the *requirement* side of `δ * Z ≤ w'`, so rounding it up means truncation can
  never help an unsafe state pass. A first draft used floor division, reintroducing
  the fail-open error one level below where it had just been corrected.
- **Summation contributes no arithmetic error.** `Fixed.add` is exact, so the `|ι|`
  factor in a sum over the index type lives entirely in the input representations —
  not, as floating-point intuition suggests, in the accumulation.
- **Every real quantity needs two fixed-point bounds, not one.** `δ` must be rounded
  *down* for active-set membership and *up* for the requirement; the post-update
  weights must be rounded *up* for `Z` and *down* for the coordinate check. The
  architecture is therefore interval arithmetic over integers, arrived at as a
  consequence of the inequality directions rather than chosen.

**`ExpEvaluator.lean` closes the loop.** `refinement_quantified` takes conservative
bounds on the post-update weights as hypotheses; the evaluator supplies them.
Both brackets come from a single Mathlib fact, `Real.add_one_le_exp`:

```
1 - a ≤ exp (-a)                    for all a
exp (-a) ≤ 1 / (1 + a)              for a > -1
```

The upper bound needs no series expansion and no case split on the sign of `a`:
`exp (-a) * (1 + a) ≤ exp (-a) * exp a = exp 0 = 1`, then divide. So
`evaluator_sound` reduces `is_safe_signal_Z` — a statement over ℝ — to a
computable check plus brackets the caller can compute. Every remaining hypothesis
is either such a bracket or a domain condition that can be checked.

**Two limits bounded that claim, and both are now dials.** The upper bound requires
`η * loss i > -1` for every coordinate, and the bracket is loose — about ±14% at
`a = 0.5`. `BracketTightening.lean` resolves both. Since `exp (-2b) = exp (-b)^2`, a
bracket squares into a bracket at twice the argument, so bracketing `a / 2^n` and
squaring back up costs `2n` multiplications, roughly halves the width each time
(measured 166 → 78 → 38 thousandths at `a = 0.5` for `n = 0, 1, 2`), and moves the
domain condition from `a > -1` to `a > -2^n`. Soundness holds for every `n`, making
it a precision dial rather than a correctness parameter.

`EvaluatorTower.lean` packages this: `evaluator_sound_tower` takes `n` as an
ordinary argument, so a caller supplies brackets on the halved exponent and gets the
real certificate back. `n = 0` recovers `evaluator_sound` exactly.

**The cost of soundness is measured.** `Benchmark.lean` runs the pipeline against
`Float` ground truth on genuinely-safe states and counts rejections: 17.8% at
`n = 0`, 9.3% at `n = 1`, 3.1% at `n = 2`, and none at `n = 3` over 129 samples.
Three squarings — six extra multiplications per coordinate — bought a monitor that
rejected nothing safe while remaining provably fail-closed.

**The sweep found two things the proofs could not.** First, `n` must scale with `η`:
the bracket is taken at `η * loss / 2^n`, so at `η = 2` the baseline `n = 3` rejects
47% of safe states and needs `n = 6` to recover. Second, and more consequentially,
`active_card_mul_delta_le_one` proves `|active| * δ ≤ 1` — and at `dim * δ = 1`, the
proved limit, *no safe state exists at all*. Safe states thin out around `0.6` and
have vanished by `0.8`. The bound is obtained by summing, so it is tight only when
every coordinate sits exactly at `δ * Z`; with any weight spread the smallest
coordinate binds first. The theorem is correct, and would mislead anyone reading it
as an operating envelope.

Ground truth throughout is `Float` standing in for ℝ, over small samples at a few
parameter points. These numbers locate boundaries; they do not characterize them.

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

- Not a deployed system. The discrete monitor compiles and runs; the boundary
  certificate has a computable, proved-sound path via `ExpEvaluator` and
  `EvaluatorTower`, and its rejection rate is measured at one parameter point.
  Nothing has run against a real workload, and no binary has been produced.
- Not a zero-TCB extraction. Lean's emitted C uses its own runtime, boxing and
  reference counting, so any host program needs marshalling glue that is
  hand-written and unverified. The honest TCB is: Lean kernel + Lean C emitter +
  C compiler + that glue. Smaller than a hand-written monitor; not zero.
- No drivers, no hardware abstraction layer.
- Not a cryptographic implementation. Token validity is an opaque predicate.
- Not a claim about real ratifiers. A4 concerns the modelled observation channel
  only, and says nothing about human cognition or persuadability.
- Not a claim of physical soundness. Sensor and environment behaviour are outside
  the model entirely.

## Open problems

- **R1b** — sufficiency, unconditionally. Necessity is closed sharply
  (`ReachabilityExact.lean`) and a witness construction exists given two margin
  obligations (`ReachabilitySufficiency.lean`), the first of which the `ε` choice
  always discharges. The second, `ε < δ * Z`, is **not** implied by `δ * |B| < 1`.
  The conjecture may in fact be false at the small-`δ|B|` end: with `B` a singleton
  and `δ` near `1/n`, the off-target coordinates can clear the floor and the active
  set overshoots `B`. Closing this needs either a sharper `ε` depending on `δ|B|`
  rather than on `n`, or the counterexample that withdraws the conjecture.
- Characterizing the feasibility boundary. The sweep locates it — safe states thin
  out near `dim * δ ≈ 0.6` and vanish by `0.8`, well inside the proved `≤ 1` — but
  does not explain it. A bound in terms of the spread between the smallest and mean
  coordinate would be the useful statement, and is not proved. Until it is, the
  operating envelope has to be found empirically for each weight distribution.
- Realistic loss distributions. The sweep uses uniform losses, `Float` ground truth,
  and small samples at a few parameter points. Enough to locate boundaries, not
  enough to characterize them.
- Trace-level composition. Coherence is proved for a single step, not for
  `List`-folded execution traces.
- A constrained ratification rule. Whether requiring `newPolicy ⊆ active δ w` at
  ratification time is acceptable, given that it makes human authority contingent
  on a machine-computed bound.
- Most necessity cells. Six are proved; a full matrix over five assumptions and the
  principal theorems needs many more, each with its own countermodel.
- The `Int64` port. `Int` is arbitrary-precision, which keeps the refinement algebra
  clean but boxes into `lean_object*`. Porting to `Int64` is what makes `@[export]`
  emit primitive C types and keeps the FFI layer thin — at the cost of threading
  no-overflow hypotheses through every lemma, including sums over the index type.
- Product composition. The product of two monitors is **not** a monitor: `cap` and
  `policy` compose via sum types, but `opState` and `lastExecuted` are scalar fields
  that cannot carry a pair. A product on the `(cap, policy, opState)` fragment, with
  `opState` combining by a meet, is well-defined but unbuilt.
- Whether a bundling **structure** (not class) would cut instantiation boilerplate
  enough to be worth it. Structures allow many values per type triple, so they do
  not break `unreachable_antitone`. This is an ergonomics question, settled by
  writing a third instantiation and counting lines rather than by argument.
- `execution_confined_by_cap_bound` carries an unused `[DecidableEq ActionId]`
  inherited from the shared `variable` block. Harmless, but it means capability
  confinement is stated with a stronger hypothesis than it needs: actions need
  not be distinguishable, only capabilities.

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
  ReachabilityExact.lean    R1b: channel surjectivity, sharp capacity bound
  ReachabilitySufficiency.lean  R1b: witness construction
  Influence.lean            minimal observation-channel example
  Interference.lean         general noninterference; A4 on the monitor itself
  SemanticQuotient.lean     semantic equivalence relation
  SemanticExpansion.lean    semantic image expansion
  Assumptions.lean          A1-A5 as predicates, with witnesses and countermodels
  Minimality.lean           necessity and independence cells
  Deployment.lean           general unreachability, deployment comparison
  Runtime.lean              executable discrete monitor, Bool/Prop bridge
  FixedPoint.lean           fixed-point model, fail-closed refinement
  ActiveSurrogate.lean      computable active set, quantified refinement
  ExpEvaluator.lean         computable exp brackets, end-to-end soundness
  BracketTightening.lean    argument doubling; arbitrarily sharp brackets
  EvaluatorTower.lean       tower packaged; n as a precision parameter
  Benchmark.lean            false-rejection measurement (no theorems)
  LLMToolCall.lean          instantiation: LLM tool-calling
  CIRunner.lean             instantiation: CI runner, non-injective permissions
```

The root imports every module, so a green build covers all of them. This was not
always true, and the correction is in the commit history.
