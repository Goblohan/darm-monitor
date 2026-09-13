# DARM Empirical Lab v0.6

## Finite Adversarial Winning-Region Analysis

DARM Empirical Lab v0.6 extends the exhaustive reachable-state analysis of v0.5 by treating event selection as adversarial choice over the complete finite transition graph.

The purpose of v0.6 is to determine, within the declared finite model, which reachable states admit an adversarial strategy for reaching the invariant-violating region, and whether the strengthened cumulative boundary eliminates that winning region.

The experiment does not enumerate hand-selected adversarial policies. Instead, it computes the finite adversarial winning region as a backward fixed point over the reachable transition graph.

This is an exhaustive result over the declared finite transition system. It is not a proof about unrestricted adaptive adversaries, arbitrary programs, physical implementations, or real deployments.

## Experimental Question

> Within the finite transition system defined by the v0.6 model, does an adversary controlling event selection have a strategy for reaching the invariant-violating region under the baseline authorization relation, and does the strengthened boundary eliminate that winning region?

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

The v0.6 experiment preserves the finite state machine used in v0.5.

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

## Transition Semantics

For every event, the model first evaluates:

    authorized = locally_authorized(state, event)

Under the baseline relation:

    executed = authorized

Under the strengthened relation, a locally authorized `transfer` is blocked when:

    state.transferred + TRANSFER_AMOUNT > TRAJECTORY_LIMIT

In that case:

    authorized = True
    executed = False

and the governed state remains unchanged.

This preserves the distinction between local authorization and boundary-constrained execution.

## Reachable Transition Graph

The experiment first constructs the reachable graph from the initial state.

At each state:

1. Enumerate every event in the finite event alphabet.
2. Retain locally authorized events.
3. Apply the deterministic transition function.
4. Record the resulting transition.
5. Continue until no new states are discovered or the maximum depth is reached.

For this model, the reachable graph reaches a fixed point before the maximum depth.

The baseline graph contains:

    reachable states:       18
    authorized transitions: 83

The strengthened graph contains:

    reachable states:       12
    authorized transitions: 56

Transition counts describe graph edges, not the number of possible trajectories.

## Safety Invariant

The modeled safety property is:

    transferred <= TRAJECTORY_LIMIT

with:

    TRAJECTORY_LIMIT = 50

A state is violating when:

    transferred > 50

The violating region is therefore:

    V = { s | s.transferred > 50 }

## Adversarial Winning Region

The adversary controls the selection of locally authorized events.

Because the transition system is deterministic after event selection, a non-violating state is adversarially winning when there exists an executed authorized transition into an already winning state.

The computation begins with the violating states:

    W_0 = V

It then repeatedly adds states satisfying:

    exists e:
        authorized(s, e)
        and executed(s, e)
        and step(s, e) in W

until a fixed point is reached.

The resulting set W is the finite adversarial winning region.

Thus:

    s in W

means that, within the declared finite model, an adversary has an event-selection strategy that can reach a violating state from s.

This is an existential reachability characterization. It does not model an external environment with competing objectives or stochastic behavior.

## Rank Certificate

v0.6 additionally assigns a finite rank to each winning state.

Violating states receive:

    rank = 0

A non-violating winning state receives a rank one greater than the rank of its selected witness successor.

The implementation computes these ranks through backward fixed-point propagation.

For every non-violating winning state, the recorded witness transition satisfies:

    rank(successor) = rank(state) - 1

This produces a finite certificate that the witness strategy reaches the violating region rather than merely remaining within the winning set.

The initial state therefore has a finite rank whenever an adversarial strategy exists from the initial state.

## Baseline Result

The complete finite baseline analysis produces:

    reachable states:          18
    authorized transitions:    83
    violating states:           6
    adversarial winning states: 14
    initial state winning:     True
    winning witnesses:          8

Thus 14 of the 18 reachable baseline states belong to the adversarial winning region.

The six rank-0 states are the violating states.

The remaining eight winning states are non-violating states from which a witness transition leads toward the violating region.

The initial state has:

    rank = 4

A canonical witness strategy from the initial state is:

    1. approve
    2. connect
    3. transfer
    4. transfer

The cumulative transfer sequence is:

    0
    0
    50
    100

The final transition therefore enters the violating region.

All four selected events are locally authorized and execute under the baseline relation.

## Critical Baseline Transition

Immediately before the violating transition:

    balance = 50
    permission = True
    credential = True
    network = True
    approval = True
    transferred = 50

The adversary selects:

    transfer

Under the baseline relation:

    locally authorized = True
    executed = True

The resulting state has:

    transferred = 100

and therefore violates:

    transferred <= 50

## Strengthened Boundary Result

Under the strengthened boundary:

    reachable states:          12
    authorized transitions:    56
    violating states:            0
    adversarial winning states: 0
    initial state winning:     False
    blocked transitions:        1

The critical second transfer remains locally authorized but is not executed.

Immediately before the attempted transfer:

    balance = 50
    permission = True
    credential = True
    network = True
    approval = True
    transferred = 50

The adversary selects:

    transfer

The result is:

    locally authorized = True
    executed = False

The state remains:

    transferred = 50

No violating state is reachable in the strengthened fixed-point graph.

Because the strengthened graph contains no violating states, its adversarial winning region is empty.

## Primary Result

Within the finite transition system defined by the v0.6 model:

> The baseline authorization relation has a non-empty adversarial winning region containing the initial state, while the strengthened cumulative boundary has an empty adversarial winning region and no reachable violating state.

The result therefore extends the v0.5 reachability finding from existence of a violating transition to a complete finite characterization of states from which an adversary can reach the violating region.

## Interpretation

The experiment demonstrates a structural distinction between:

    adversarial action selection

and:

    boundary-constrained state transition

The adversary is not prevented from selecting the second `transfer` in the strengthened model.

Instead, the event remains locally authorized while the strengthened boundary prevents its execution.

The relevant sequence is therefore:

    adversary selects transfer
            |
            v
    local authorization = True
            |
            v
    boundary check
            |
            v
    execution = False

This is the empirical behavior the experiment is intended to expose.

The result should not be interpreted as evidence that an arbitrary real-world system will possess the same enforcement property. The experiment operates entirely within the declared finite transition model.

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

        ↓

    v0.6
        finite adversarial winning-region analysis

v0.5 established that the complete reachable baseline graph contains an invariant-violating transition and that the strengthened graph contains no violating state.

v0.6 adds adversarial fixed-point analysis over that graph. Rather than selecting several example policies, it characterizes the complete set of reachable states from which an adversary can reach the violating region under the finite transition relation.

## Scope of Exhaustiveness

The word "exhaustive" has a precise scope.

The analysis is exhaustive over:

    the declared initial state
    the declared finite state representation
    the declared eight-event alphabet
    the declared local authorization predicate
    the declared deterministic transition function
    the strengthened cumulative boundary
    the reachable transition graph
    the finite adversarial reachability fixed point

It is not exhaustive over:

    arbitrary event alphabets
    arbitrary state representations
    arbitrary programs
    arbitrary implementations
    arbitrary real-world environments
    unrestricted adaptive adversaries
    physical executions

Consequently, v0.6 should be described as a finite adversarial reachability result for the declared model.

## Relationship to the Formal DARM Result

The v0.6 experiment is intended as an empirical analogue of the structural distinction represented in the formal DARM work.

It does not reproduce the unrestricted mathematical adversary theorem.

In particular, v0.6 uses:

    a finite state space
    a fixed event alphabet
    deterministic transitions
    a particular cumulative invariant
    an explicitly modeled boundary

The formal DARM result concerns a more general transition-system model and an unrestricted history-dependent adversary.

The appropriate claim is therefore correspondence of experimental structure, not equivalence of the Python artifact and the machine-checked theorem.

## Limitations

1. The experiment uses a finite abstract state model.
2. Only eight event types are represented.
3. The transition function is deterministic and explicitly defined in Python.
4. The safety invariant concerns the modeled cumulative transfer quantity.
5. The boundary is implemented as a modeled transition constraint.
6. The adversarial analysis is existential finite-state reachability.
7. The winning-region calculation does not represent arbitrary external programs.
8. The experiment does not establish physical enforcement.
9. The experiment does not establish correctness of a real deployment.
10. The experiment does not establish semantic correctness of an external system.
11. The experiment does not reproduce the unrestricted adaptive-adversary theorem.
12. The experiment does not establish noninterference.
13. The experiment does not establish general AI safety.
14. No conclusion about a physical security boundary follows without a separate implementation and realization argument.

## Reproducibility

Run:

    python3 empirical/lab/v0.6/darm_v0_6.py

The execution writes:

    empirical/lab/v0.6/results.json

The source also passes Python bytecode compilation with:

    python3 -m py_compile empirical/lab/v0.6/darm_v0_6.py

The recorded JSON contains:

    model parameters
    baseline graph statistics
    strengthened graph statistics
    adversarial winning-region statistics
    rank certificates
    witness transitions
    baseline strategy trace
    strengthened blocked-transition details

The v0.6 experiment is deterministic at the analysis level. Witness selection is explicitly ordered so that the recorded rank certificate does not depend on arbitrary Python set iteration order.

## Artifact

Files:

    darm_v0_6.py
    results.json
    README.md

The v0.6 artifact is intended as a companion empirical component of the DARM research program.

It does not replace the machine-checked formal results and should not be interpreted as an unrestricted security proof.
