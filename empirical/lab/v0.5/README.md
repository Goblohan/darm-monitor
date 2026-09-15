# DARM Empirical Lab v0.5

## Exhaustive Bounded Reachability Analysis

DARM Empirical Lab v0.5 replaces the discarded fixed-priority policy experiment with exhaustive analysis of the reachable state-transition graph defined by the finite v0.5 model.

The purpose of v0.5 is to examine, without manually selecting an adversarial policy, whether the modeled baseline authorization relation permits entry into an unsafe state and whether the strengthened boundary blocks that transition.

The experiment exhaustively explores the reachable states and locally authorized transitions of the declared finite transition system until a fixed point is reached, with a maximum exploration depth of 50.

This is an exhaustive result over the declared finite transition system. It is not a proof about unrestricted adaptive adversaries, arbitrary programs, physical implementations, or real deployments.

## Experimental Question

> Within the finite transition system defined by the v0.5 model, does exhaustive reachable-state analysis find an invariant-violating transition under the baseline authorization relation, and does the strengthened cumulative boundary prevent entry into the violating region?

The analysis compares two transition relations:

    baseline
        local authorization only

    strengthened boundary
        local authorization
        +
        cumulative transfer constraint

The strengthened boundary applies:

    transferred + TRANSFER_AMOUNT <= TRAJECTORY_LIMIT

to a locally authorized `transfer`.

## Shared Model

The experiment uses the same finite state machine introduced in the earlier empirical versions.

Initial state:

    balance = 100
    permission = True
    credential = True
    network = False
    approval = False
    transferred = 0

Model parameters:

    initial balance = 100
    transfer amount = 50
    trajectory limit = 50
    maximum exploration depth = 50

The event alphabet contains eight events:

    request
    transfer
    revoke
    refresh_credential
    connect
    disconnect
    approve
    clear_approval

Local authorization is evaluated independently of the strengthened cumulative boundary.

## Reachability Procedure

The experiment begins from the fixed initial state.

At each exploration depth:

1. Take the newly discovered frontier states.
2. Enumerate every event in the eight-event alphabet.
3. Retain events that satisfy the local authorization predicate.
4. Apply the transition function.
5. Record whether the transition executes or is blocked by the strengthened boundary.
6. Record any transition entering the unsafe region.
7. Add previously unseen successor states to the next frontier.

Exploration continues until no new states are discovered or the maximum depth of 50 is reached.

Because the state space is finite for this model, the experiment reaches a fixed point before the maximum depth.

The resulting transition counts therefore describe the reachable graph explored by the procedure, rather than the number of possible event sequences or trajectories.

## Invariant

The modeled safety property is the cumulative transfer constraint:

    transferred <= TRAJECTORY_LIMIT

with:

    TRAJECTORY_LIMIT = 50

A transition is a first-entry violation when:

    before.transferred <= 50

and:

    after.transferred > 50

This distinction is important.

Once the system has entered a violating state, additional transitions from that state are not counted as independent first-entry violations.

## Baseline Result

Exhaustive reachable-state analysis of the baseline authorization relation produces:

    fixed-point states:              18
    authorized transitions:          83
    first-entry violations:           1
    first violation depth:            4
    violating states:                 6
    blocked transitions:              0

The unique first-entry violation is:

    before:
        balance = 50
        permission = True
        credential = True
        network = True
        approval = True
        transferred = 50

    event:
        transfer

    after:
        balance = 0
        permission = True
        credential = True
        network = True
        approval = True
        transferred = 100

Thus the baseline local authorization relation permits a transition from a safe state to a state that violates the cumulative invariant.

The experiment also identifies 28 authorized transitions whose destinations are already within the violating region. These are not additional first-entry violations; they occur after the invariant has already been violated.

## Representative Baseline Trace

A shortest representative trace to the violating state is:

    1. connect
    2. approve
    3. transfer
    4. transfer

The cumulative transfer sequence is:

    0
    0
    50
    100

The fourth transition therefore crosses the modeled boundary.

All four events in this representative trace are locally authorized under the baseline relation.

## Strengthened Boundary Result

Under the strengthened cumulative boundary, exhaustive reachable-state analysis produces:

    fixed-point states:              12
    authorized transitions:          56
    first-entry violations:           0
    first violation depth:            None
    violating states:                 0
    blocked transitions:              1

The critical transition is:

    before:
        balance = 50
        permission = True
        credential = True
        network = True
        approval = True
        transferred = 50

    event:
        transfer

    locally authorized:
        True

    executed:
        False

    after:
        balance = 50
        permission = True
        credential = True
        network = True
        approval = True
        transferred = 50

The event remains locally authorized, but the strengthened boundary prevents the governed state transition because executing it would produce:

    transferred = 100

which exceeds the trajectory limit of 50.

No violating state is reachable in the strengthened fixed-point graph.

## Primary Result

Within the finite transition system defined by the v0.5 model:

> Exhaustive reachable-state analysis finds a first invariant-violating transition at depth 4 under the baseline authorization relation. Under the strengthened cumulative boundary, that transition is blocked and no violating state is reachable in the resulting fixed-point graph.

This is the principal empirical result of v0.5.

The result is stronger than a manually selected trajectory because the reachable state-transition graph is explored exhaustively rather than through a selected policy or sampled set of traces.

## Interpretation

The experiment demonstrates a structural difference between:

    local authorization

and:

    boundary-constrained state transition

The baseline relation answers whether an event is locally authorized.

The strengthened relation additionally constrains whether an authorized transfer may actually induce the governed state transition.

In the modeled system, local authorization alone does not preserve the cumulative invariant.

The strengthened boundary does preserve the invariant over the reachable state graph of the declared finite model.

This should be interpreted as an empirical demonstration of the modeled boundary mechanism, not as evidence that a physical implementation automatically possesses the same property.

## Relation to Earlier Versions

The empirical progression is:

    v0.1
        single deterministic witness

        ↓

    v0.2
        bounded exhaustive event-trajectory enumeration

        ↓

    v0.3
        one bounded history-sensitive adaptive policy

        ↓

    v0.4
        finite explicitly specified adaptive-policy family

        ↓

    v0.5
        exhaustive bounded reachable-state analysis

The v0.5 redesign deliberately abandons the fixed-priority policy formulation used in an earlier draft of the experiment.

That formulation produced a degenerate scheduler for this state machine because persistent locally authorized events could repeatedly prevent lower-priority state-changing events from being selected.

Rather than introduce an arbitrary scheduler modification, v0.5 removes the policy-selection layer and directly analyzes the governed transition relation.

This makes the experiment more closely aligned with the DARM question being modeled: which governed state transitions are reachable under the authorization boundary?

## Scope of Exhaustiveness

The word "exhaustive" in this experiment has a precise scope.

The analysis is exhaustive over:

    the declared initial state
    the declared finite state representation
    the declared eight-event alphabet
    the declared local authorization predicate
    the declared transition function
    the strengthened cumulative boundary
    the reachable graph generated by those definitions

It is not exhaustive over:

    arbitrary event alphabets
    arbitrary state representations
    arbitrary programs
    arbitrary implementations
    arbitrary real-world environments
    unrestricted adaptive adversaries
    physical executions

Consequently, the experiment should be described as an exhaustive bounded reachability result for the declared model.

## Limitations

1. The experiment uses a finite abstract state model.
2. Only eight event types are represented.
3. The transition function is deterministic and explicitly defined in Python.
4. The safety invariant concerns the modeled cumulative transfer quantity.
5. The boundary is implemented as a modeled transition constraint.
6. The experiment does not establish physical enforcement.
7. The experiment does not establish correctness of a real deployment.
8. The experiment does not establish semantic correctness of an external system.
9. The experiment does not exhaustively represent unrestricted adaptive adversaries.
10. The experiment does not establish noninterference.
11. The experiment does not establish general AI safety.
12. No conclusion about a physical security boundary follows without a separate implementation and realization argument.

## Reproducibility

The experiment can be reproduced from the Python artifact:

    python3 empirical/lab/v0.5/darm_v0_5.py

The execution writes:

    empirical/lab/v0.5/results.json

The source also passes Python bytecode compilation with:

    python3 -m py_compile empirical/lab/v0.5/darm_v0_5.py

The recorded JSON contains the model parameters, baseline and strengthened graph statistics, first-entry violation, representative traces, and blocked transition.

## Artifact

Files:

    darm_v0_5.py
    results.json
    README.md

The v0.5 artifact is intended as a companion empirical component of the DARM research program.

It does not replace the machine-checked formal results and should not be interpreted as an unrestricted security proof.
