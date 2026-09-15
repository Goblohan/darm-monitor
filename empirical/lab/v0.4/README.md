# DARM Empirical Lab v0.4

## Bounded Adaptive Policy Family

DARM Empirical Lab v0.4 extends the bounded empirical model from v0.3 by evaluating a finite, explicitly specified family of deterministic policies against the same modeled authorization boundary.

The state machine, local authorization predicate, cumulative boundary, initial state, event alphabet, and 10-step horizon are retained from v0.3. The experimental variable is the policy used to select events.

The purpose is to strengthen the empirical question from one bounded adaptive policy to a declared finite family of policies, while preserving the distinction between bounded empirical evaluation and the unrestricted history-dependent adversary used in the formal DARM development.

## Experimental Question

> For every policy in the explicitly specified v0.4 policy family, does the strengthened cumulative boundary preserve the trajectory invariant over the 10-step horizon?

The quantifier is therefore over the declared finite policy family only:

    for every policy in Pi_v0.4

It is not a claim over the unrestricted adaptive-adversary class.

## Shared Model

The experiment retains the v0.3 model:

- initial balance = 100
- transfer amount = 50
- trajectory limit = 50
- maximum steps = 10
- event alphabet size = 8

Events:

    request
    transfer
    revoke
    refresh_credential
    connect
    disconnect
    approve
    clear_approval

Local authorization remains the same as v0.3.

The strengthened boundary applies the same cumulative condition:

    transferred + TRANSFER_AMOUNT <= TRAJECTORY_LIMIT

for a locally authorized `transfer`.

No policy is permitted to modify the boundary.

## Policy Family

The v0.4 policy family contains five deterministic policies.

### 1. direct_pursuit

A non-adaptive policy.

Decision rule:

1. Compute locally authorized events.
2. If `transfer` is locally authorized, choose `transfer`.
3. Otherwise choose the first locally authorized event according to this fixed priority:

    approve
    refresh_credential
    connect
    request
    clear_approval
    revoke
    disconnect

The policy does not inspect execution history.

### 2. authorization_rebuilder

A deterministic prerequisite-rebuilding policy.

The policy prioritizes restoration of authorization prerequisites before pursuing the protected transfer.

Its fixed priority is:

    connect
    refresh_credential
    approve
    request
    transfer
    clear_approval
    revoke
    disconnect

Only locally authorized events may be selected.

The policy does not treat a blocked transition as evidence of a different security state; the boundary rejection is simply reflected in execution history.

### 3. rejection_recovery

A history-sensitive recovery policy derived from the v0.3 adaptive strategy.

Before a blocked transfer has been observed, it pursues transfer and establishes prerequisites when necessary.

After observing a blocked transfer, it:

1. clears approval once if possible;
2. re-establishes approval;
3. retries transfer.

The policy therefore explicitly reacts to observed boundary rejection.

### 4. state_cycler

A deterministic policy that deliberately cycles authorization-relevant state before pursuing transfer.

Its behavior is based on a fixed event priority and execution history. It may use `clear_approval`, `approve`, `revoke`, `refresh_credential`, `connect`, and `disconnect` to alter the authorization state before attempting the protected effect.

The policy remains restricted to the modeled event alphabet and may select only locally authorized events.

### 5. mixed_adaptive

A history-sensitive policy combining prerequisite rebuilding and rejection recovery.

Before rejection, it prioritizes establishment of the conditions required for transfer.

After observing a blocked transfer, it switches to a recovery sequence involving approval reset and re-establishment before retrying transfer.

Its decision order is deterministic and specified in the implementation.

## Experimental Procedure

Each policy is run twice from the same initial state:

1. baseline mode, in which locally authorized transitions execute without the strengthened cumulative boundary;
2. strengthened-boundary mode, in which the cumulative transfer constraint is enforced.

For every run, the artifact records:

- policy name
- mode
- steps executed
- final state
- total transferred
- trajectory limit
- whether the invariant holds
- first violation step, if any
- blocked events
- complete execution history

The aggregate experiment reports:

- number of policies evaluated
- number of baseline violations
- number of strengthened-boundary violations
- number of policies experiencing blocked transfers
- per-policy results
- representative traces

## Interpretation

The principal empirical result is restricted to the explicitly implemented finite policy family.

A result of zero strengthened-boundary violations means:

> No policy in the declared v0.4 family violated the modeled cumulative invariant during the specified 10-step execution.

It does not mean that all adaptive policies, all possible policies, or the unrestricted history-dependent adversary have been exhausted.

## Relation to Earlier Versions

The empirical progression is:

    v0.1
        single deterministic witness

        ↓

    v0.2
        bounded exhaustive enumeration of event trajectories

        ↓

    v0.3
        one bounded history-sensitive adaptive policy

        ↓

    v0.4
        finite explicitly specified policy family

v0.4 therefore changes the empirical quantification over policies while retaining the modeled state machine and boundary semantics.

## Limitations

1. The experiment uses a finite state model.
2. The execution horizon is limited to 10 steps.
3. The policy family is finite and explicitly specified.
4. The family does not represent the unrestricted adaptive-adversary class.
5. Policy behavior is restricted to the modeled event alphabet.
6. The strengthened boundary is a modeled transition constraint rather than a claim about physical or deployed enforcement.
7. The experiment does not establish semantic correctness of a real deployment.
8. No conclusion about physical security or general AI safety follows from this experiment alone.

## Artifact

Files:

    darm_v0_4.py
    results.json
    README.md

The experiment is intended as a companion empirical artifact for the DARM formal work, not as a replacement for the machine-checked results.
