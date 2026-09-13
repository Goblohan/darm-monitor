# DARM Empirical Lab v0.7
## Dependency Expansion and Boundary Coverage

### Objective

v0.7 tests whether an assurance boundary that is sufficient for a finite system remains sufficient after the system's guarantee-relevant dependency surface expands.

The experiment distinguishes dependency expansion, boundary coverage, DARM transfer admissibility, and actual adversarial reachability of the violating region.

Incomplete coverage must not be treated as an automatic violation condition.

### Frozen v0.6 Baseline

The initial state, state variables, local authorization semantics, existing transfer semantics, safety invariant, deterministic transition semantics, reachable-graph construction, adversarial winning-region algorithm, and rank/witness calculation are preserved from v0.6.

v0.7 is an extension of v0.6, not a redefinition.

### Dependency Model

Two guarantee-relevant dependency identifiers are introduced:

- authA
- authB

The original transfer path depends on authA.

A newly introduced alternative transfer path is guarantee-relevant, reachable from the initial state, depends on authB, and induces the same governed cumulative effect as the original transfer path.

Dependency requirements and boundary coverage are modeled independently. Boundary coverage determines whether a transition path is actually mediated by the represented boundary and enforcement locus.

Both paths must induce the same governed cumulative effect:

    transferred' = transferred + 50

The alternative path must therefore be genuinely reachable and guarantee-relevant.

The guarantee-relevant dependency surface must be justified from the modeled transition semantics: a dependency qualifies as guarantee-relevant only when a transition relying on that dependency can affect the state variable occurring in the guarantee.

### Configurations

#### A — Original / Covered

    Dep(G, S_A) = {authA}
    Cov(B_A, L_A, S_A) = {authA}

Therefore:

    GRBS_A = True

#### B — Expanded / Uncovered

The dependency surface is expanded:

    Dep(G, S_B) = {authA, authB}

while the original boundary remains:

    Cov(B_A, L_A, S_B) = {authA}

Therefore:

    GRBS_B = False

#### C — Expanded / Covered

The expanded dependency surface is retained while the boundary is expanded:

    Dep(G, S_C) = {authA, authB}
    Cov(B_C, L_C, S_C) = {authA, authB}

Therefore:

    GRBS_C = True

### Independence Requirement

GRBS and adversarial winning-region membership must be calculated independently.

Incomplete coverage must not automatically create a violating state or winning region.

The experiment must discover whether an adversarial route exists.

A transition whose dependency is outside the represented boundary coverage must not receive the boundary's cumulative execution constraint. A transition whose dependency is covered must receive that constraint. This mediation distinction must be implemented explicitly rather than inferred from whether a violation occurs.

### Hypotheses

H1. The original complete-coverage configuration satisfies the DARM structural transfer condition.

H2. Dependency expansion without boundary expansion makes transfer inadmissible. Whether an actual violating strategy exists is an empirical result and must not be assumed.

H3. Extending boundary coverage restores GRBS.

### Ideal Outcome

A strong correspondence would be:

    A: GRBS=True,  winning region empty
    B: GRBS=False, winning region non-empty
    C: GRBS=True,  winning region empty

However, this outcome must not be hard-coded.

A possible outcome is:

    A: GRBS=True,  winning region empty
    B: GRBS=False, winning region empty
    C: GRBS=True,  winning region empty

Such an outcome would demonstrate that structural assurance-transfer admissibility is distinct from observed safety in the finite model.

### Required Outputs

Each configuration must record:

- configuration
- dependency_surface
- boundary_coverage
- grbs
- reachable_states
- authorized_transitions
- blocked_transitions
- violating_states
- adversarial_winning_states
- initial_state_winning
- winning_strategy

The comparison must expose:

- dependency_expanded
- coverage_expanded
- grbs_changed
- winning_region_changed

### Falsification Conditions

The experiment is invalid if:

1. transfer_alt cannot reach the protected cumulative effect;
2. authB does not materially participate in the alternative path;
3. configurations B and C have identical effective transition mediation;
4. GRBS is inferred from the winning-region result;
5. the implementation declares an uncovered path unsafe rather than allowing the analysis to discover the result;
6. changing boundary coverage has no actual effect on transition mediation when it is intended to;
7. unrelated v0.6 semantics are changed without explicit documentation.

### Research Scope

v0.7 is a finite executable experiment. It does not establish physical enforcement, unrestricted adversarial security, semantic correctness of external systems, or general AI safety.

Its purpose is to provide an empirical test of the structural relationship between dependency expansion, boundary coverage, assurance-transfer admissibility, and adversarial reachability.
