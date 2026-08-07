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

### The update rule is a parameter (`BoundaryCore.lean`, `RationalInstance.lean`)

None of the four boundary theorems unfolds `reweight`. `safe_signal_equiv` is
`δ * Z ≤ w'ᵢ ↔ δ ≤ w'ᵢ / Z` — algebra over a positive scalar. `transportSupp`
cites it. The update appears only as an opaque term.

`BoundaryCore.lean` states them accordingly, over a pre-update vector `w` fixing
the active set and a post-update vector `w'` that must clear the floor, with no
relation assumed between them. The originals are recovered as instances:
`safe_signal_equiv_from_core` has no proof body, so it is definitionally the
general theorem with `w' := reweight η loss w`. The exponential was never
load-bearing.

`RationalInstance.lean` exercises a second update, `w / (1 + η * loss)`. The
boundary results apply with **zero new proof content**, and the fixed-point
evaluation is exact — two directed divisions, no bracket, no tower, no `n`. At
`a = 0.5` the bounds are `666` and `666` in thousandths, one quantum apart.

**But this is a different update, not a better approximation.** `1/(1+a) = 0.667`
where `exp(-a) = 0.6065`. Choosing between the instances is choosing a rule, and
what the rational one costs is proved rather than argued:

- **It does not compose.** `exp_semigroup` proves `exp(-a) · exp(-b) = exp(-(a+b))`,
  so a loss stream may be batched or streamed to the same state.
  `rational_not_semigroup` proves the surrogate fails this — `1/4 ≠ 1/3` at
  `a = b = 1`. Under it, a monitor's boundary would depend on how telemetry
  happened to be chunked across clock cycles.
- **It is not globally positive.** `ratUpdate_neg_below` proves it goes negative
  past `-1`, breaking the non-negativity every capacity bound needs.

Over ℝ this trade is forced, not an engineering gap: `exp` is the unique
continuous solution of `f(a) · f(b) = f(a + b)`, so no exactly-computable update
composes. `exp` remains primary; the surrogate is admissible where losses are
bounded below and history independence is not required.

A third objection sometimes raised — that changing the update degrades the
`O(√(T ln N))` regret bound of multiplicative weights — does not apply. This
development contains no regret, no comparator, no loss sequence and no horizon.
`reweight` is a single-step function. That is precisely why the abstraction goes
through.

### Feasibility (`Feasibility.lean`)

`Reachability.active_card_mul_delta_le_one` proves `|active| * δ ≤ 1`, which
invites reading `δ = 1/dim` as admissible. The benchmark sweep found no safe
state at all at `dim * δ = 1`, and they were already scarce by `0.6`.

The explanation is that safety requires `δ * Z ≤ v i` for every active `i` —
that is, `δ * Z ≤ inf` — and the proved bound is obtained by *summing* that
family, replacing the infimum with something mean-like. So

```
|S| * δ  ≤  |S| * (inf over S) / Z  ≤  1
```

The middle term is the sharp ceiling. `uniform_attains` shows the coarse bound is
reached only when the weights are flat, and `spread_loses` gives a case:
weights `(1,4,4,4)` cap `δ` at `4/13`, not `1`.

**Practical reading:** compute the envelope as `inf / Z` from the weights in
hand, which is checkable at runtime. Do not compute it as `1/δ` coordinates —
that is a correct bound no real distribution approaches.

`FeasibilityRange.lean` adds the third statement, the one a deployment actually
needs. If every weight lies in `[lo, hi]` then `dim * δ ≤ lo / hi` is
**sufficient** — evaluable before any weights exist. The correction factor against
`dim * δ ≤ 1` is exactly the dynamic range of the weights, and
`not_sufficient_witness` proves the coarse bound really is not a design rule:
`dim = 2`, `δ = 1/2`, weights `(1,3)` meets it at its exact limit and is unsafe.

Three statements, three questions:

| Form | Answers |
|---|---|
| `\|S\| * δ ≤ 1`, necessary | what cannot happen |
| `inf / Z`, exact | is *this* state feasible, at runtime |
| `dim * δ ≤ lo / hi`, sufficient | what `δ` to choose, at design time |

Only the first existed before the benchmark; the third exists because the sweep
showed the first was being read as it.

**The 64-bit port reaches a quantified evaluator.** `FixedPoint.Fixed` wraps `Int`, which is arbitrary-precision and boxes into `lean_object*`. A callable library wants
`int64_t`. `HardwarePort.lean` proves the overflow envelope: on 64-bit
hardware, fixed-point multiplication computes through a widening 128-bit
intermediate before shifting back down, so the binding constraint is the
*output* fitting in `Int64`, not the intermediate. At `k = 32` that permits raw
magnitude `2^47` — value 32768 — comfortably above any weight.

`Fixed64.lean` builds the type and proves it refines `FixedPoint.Fixed` for
every operation: the bridge (`Int64.ofInt` round-trips exactly inside
`[-2^63, 2^63)`, via balanced modulus), addition, multiplication, and **both**
directed divisions. Eleven theorems, no `sorryAx`. Getting `divUp` right took
four attempts — the first three each patched the previous boundary failure and
exposed the next one, because two's complement is asymmetric: negating the
minimum representable value overflows the top by one. What worked was deriving
the bound before writing any Lean: excluding that one input makes the
*product* bound symmetric with `2^32` of slack, which makes the quotient
strict at both ends.

**`Fixed64Refinement.lean` connects the type to the certificate.** An external
review (2026-08-04) made a sharper point than the port's own notes had:
proving `F64` refines `Fixed` is not the same as proving anything in this
repository *uses* `F64` — every evaluator ran on `Int`. `checkSafeCoord64` runs
the safety check on genuine `Int64` values via the proven native multiply, and
`refinement_coord64` proves it agrees with the `Int`-based evaluator inside the
envelope, for one coordinate.



**The port runs.** `c/darm_native.c` supplies the widening multiply — 64×64→128,
shift back down — which `Fixed64Native.lean` binds with `@[extern]`. `Main.lean`
is a `lean_exe` target linking it. `lake exe darmdemo` prints the discrete
monitor's ALLOWED/BLOCKED table from compiled code and then the differential
results.

**The binding is deliberately not on the proved function.** `@[extern]` on
`F64.mulUp` would replace its implementation everywhere, including inside every
simulation theorem — those theorems would stay true about the Lean definition
while the running code was something else, and nothing would check the gap. So
`mulUpNative` is a separate definition, and the two are compared on **50,012
deterministic pairs**, all agreeing in both rounding directions. That is not
proof; it is a trust boundary made testable rather than merely asserted.

**A bug this caught before shipping.** The first C used `/`, which truncates
toward zero, where Lean's `Int.ediv` floors. They diverge on negative numerators,
so `mulUp` would have been wrong on every *positive* product — at `3 × 3` the
specification gives 1 and truncation gives 0. Arithmetic right shift is floor
division for a positive power of two and is what the C now uses. No proof in this
repository would have found that; the differential tests would.

**The trusted computing base, precisely.** Before the binding: the Lean kernel.
After it: the kernel, the Lean C emitter, Clang, the Lean FFI conventions, and
`darm_native.c`. That is a real widening and it is the price of leaving the
interpreter.

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

**NR4 — no exactly-computable update composes.** `exp` is the unique continuous
solution of `f(a) * f(b) = f(a + b)`, so any update that evaluates exactly in
fixed point loses path-independence. `rational_not_semigroup` exhibits the
failure concretely. This bounds what "extracting the continuous stratum" could
ever mean: the bracket is not an implementation shortfall but the price of a
property no computable rule has.

## Deliberate non-claims

- Not a deployed system. The discrete monitor compiles and runs; the boundary
  certificate has a computable, proved-sound path via `ExpEvaluator` and
  `EvaluatorTower`, and its rejection rate is measured at one parameter point.
  Nothing has run against a real workload. The demo binary builds and runs, but
  it exercises the differential tests, not a deployment.
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

## Open problems, and one recently closed

- **R1b is closed.** `ReachabilityClosed.lean` supplies
  `ε = min((1 - δm)/(2δk), δm/2)`, which discharges both margin obligations for
  every admissible input; `ReachabilityFinset.realizable_of_card_lt` states it
  over actual `Finset`s — give it a nonempty proper subset with `δ * |B| < 1`
  and it returns a weight vector whose active set is exactly `B`.

  
  This entry previously said the conjecture might be FALSE. That was an error of
  inference: `eps_choice_bounds`' particular `ε` does violate the second
  obligation at small `δ|B|` — true then and now — but nothing followed about
  other choices of `ε`. It crossed from "this construction fails" to "the
  statement may be false", a gap of one existential quantifier.

  
  Only sufficiency is packaged as a single theorem. Necessity exists
  (`active_card_strict_lt_of_ne_univ`) but is stated over an arbitrary vector's
  active set, so the two do not compose into one biconditional without more
  work. A draft that took necessity as an unused hypothesis was deleted — the
  linter caught that its signature advertised more than the proof delivered.
- Migrating `BoundaryMargin.lean` onto `BoundaryCore`. The general theorems exist
  and the originals are proved to be instances, but `BoundaryMargin` still carries
  its own copies. Deleting them is mechanical and cascades through every
  downstream module, re-earning their axiom traces. Deferred, not blocked.
- The end-to-end `refinement_quantified` instantiation for the rational update.
  `RationalInstance` supplies the coordinate bounds; assembling them mirrors
  `evaluator_sound` and is mechanical. Left until a caller wants that instance.
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
- Most necessity cells. Seven are proved; a full matrix over five assumptions and the
  principal theorems needs many more, each with its own countermodel.
- Bulk FFI. The extern binding is called once per multiply, and at that
  granularity the call and the `Int` boxing cost far more than the arithmetic —
  500,120 multiplies took 472 ms, roughly 944 ns each, for what is one hardware
  instruction. Correctness is unaffected; throughput would need the C to take a
  whole vector rather than a pair.
- Lake does not build the C. `c/libdarm_native.a` is compiled by hand with
  `leanc` and `llvm-ar`; the executable links it via `moreLinkArgs`. A fresh
  clone must run those two commands before `lake exe darmdemo` will link.
  An `extern_lib` build rule would automate it.
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
  ReachabilityClosed.lean   R1b: both obligations jointly satisfiable
  ReachabilityFinset.lean   R1b: realizability over Finsets
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
  HardwarePort.lean         64-bit overflow envelope
  Fixed64.lean              type refining Fixed; bridge, add, mul, both div
  Fixed64Refinement.lean    F64 connected to the certificate (one coordinate)
  Fixed64SumOver.lean       Fintype-indexed sum over F64
  Fixed64MulDown.lean       downward multiply over F64
  Fixed64Sub.lean           subtraction over F64
  Fixed64Tower.lean         doubling tower; unit invariant stable under squaring
  Fixed64Bracket.lean       expBracket over F64
  Fixed64ZhiN.lean          partition-function bound over F64
  Fixed64Evaluator.lean     the quantified evaluator over F64
  Fixed64Native.lean        C bindings; differential tests vs the proved version
  Main.lean                 demo executable
  c/darm_native.c           widening multiply (NOT verified - see below)
  Fixed64Sum.lean           list summation (superseded by Fixed64SumOver)
  Feasibility.lean          sharp capacity bound; why the coarse one misleads
  FeasibilityRange.lean     design-time envelope from weight dynamic range
  BoundaryCore.lean         boundary theorems over an arbitrary update
  RationalInstance.lean     second instance; exact, but does not compose
  LLMToolCall.lean          instantiation: LLM tool-calling
  CIRunner.lean             instantiation: CI runner, non-injective permissions
```

The root imports every module, so a green build covers all of them. This was not
always true, and the correction is in the commit history.
