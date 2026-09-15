# DARM Empirical Lab v0.3

## Deterministic Adaptive Adversary

DARM Empirical Lab v0.3 extends the bounded empirical model from v0.2 by introducing a deterministic adaptive policy whose subsequent actions depend on its observed execution history.

The experiment asks a narrower empirical question:

> Can a deterministic adaptive policy observe rejection of a protected transition, modify the authorization state, re-establish local authorization, and retry the protected transition without violating a strengthened cumulative boundary?

The experiment is deliberately bounded and does not claim to empirically exhaust the unrestricted history-dependent adversary class used in the formal DARM model.

## Model

The experiment uses the same finite state and event model as v0.1 and v0.2.

### State

The state contains:

- balance
- permission
- credential
- network
- approval
- transferred

Initial values:

- balance = 100
- permission = true
- credential = true
- network = true
- approval = false
- transferred = 0

### Events

The event alphabet contains eight events:

1. request
2. transfer
3. revoke
4. refresh_credential
5. connect
6. disconnect
7. approve
8. clear_approval

A transfer requires local authorization through permission, credential, network connectivity, approval, and sufficient balance.

## Boundary

The strengthened boundary adds the cumulative condition:

    transferred + TRANSFER_AMOUNT <= TRAJECTORY_LIMIT

with:

    TRANSFER_AMOUNT = 50
    TRAJECTORY_LIMIT = 50

The baseline does not enforce this cumulative constraint.

## Adaptive Policy

The adversary is deterministic and observes the execution history.

Before a boundary rejection it attempts the protected effect directly.

After observing a rejected transfer, it changes strategy:

    clear_approval -> approve -> transfer

This provides an explicit adaptive recovery sequence rather than repeatedly submitting the same rejected event.

The policy is a single bounded deterministic strategy. It is not intended to represent the entire class of unrestricted adaptive, history-dependent adversaries in the formal theory.

## Experimental Configuration

- Maximum trajectory length: 10 steps
- Event alphabet: 8 events
- Adversary: adaptive_recovery_search
- Initial balance: 100
- Transfer amount: 50
- Trajectory limit: 50

## Observed Result

### Baseline

The adaptive policy produces:

    Step 1: approve
    Step 2: transfer       -> transferred = 50
    Step 3: transfer       -> transferred = 100

The cumulative limit is violated at step 3.

Result:

    total_transferred = 100
    trajectory_limit = 50
    guarantee_holds = false
    violation_step = 3

### Strengthened Boundary

The same policy produces:

    Step 1: approve
    Step 2: transfer       -> transferred = 50
    Step 3: transfer       -> BLOCKED
    Step 4: clear_approval
    Step 5: approve
    Step 6: transfer       -> BLOCKED

Further transfer attempts remain blocked through the 10-step horizon.

Result:

    total_transferred = 50
    trajectory_limit = 50
    guarantee_holds = true
    violation_step = null

There are six blocked transfer attempts during the 10-step run.

The important adaptive sequence is:

    transfer
        |
        v
    boundary rejection
        |
        v
    clear_approval
        |
        v
    approve
        |
        v
    transfer
        |
        v
    boundary rejection

Thus the policy can modify and reconstruct the locally authorized state, but the strengthened cumulative boundary continues to reject the invariant-violating transition.

## Relation to Earlier Empirical Versions

### v0.1 - Explicit Witness

Demonstrated a concrete trajectory in which locally authorized transitions could violate the cumulative invariant, while a strengthened boundary prevented the violation.

### v0.2 - Exhaustive Bounded Enumeration

Enumerated all 8^5 = 32,768 trajectories of length five.

The baseline contained 8,756 locally authorized trajectories, of which 229 violated the cumulative limit. The strengthened boundary produced zero violations in the enumerated trajectory set.

v0.2 was exhaustive only within its finite five-step model.

### v0.3 - Adaptive Interaction

Introduces a deterministic policy that observes execution history and changes strategy after boundary rejection.

The empirical progression is therefore:

    explicit witness
        ->
    bounded exhaustive search
        ->
    bounded adaptive interaction

## Reproducibility

From this directory:

    python3 -m py_compile darm_v0_3.py
    python3 darm_v0_3.py

The executable script regenerates:

    results.json

The JSON file contains the complete baseline and strengthened traces used for the reported result.

## Interpretation

The v0.3 result supports the following bounded empirical observation:

> For the modeled state machine, cumulative boundary, 10-step horizon, and adaptive_recovery_search policy, rejection of the protected transition does not prevent the policy from modifying and reconstructing local authorization, but the strengthened boundary continues to prevent the cumulative invariant from being violated.

This is an empirical observation about the implemented model and policy.

It is not evidence that all possible adaptive adversaries have been tested, nor is it an independent proof of the unrestricted adaptive-adversary theorem in the formal DARM development.

## Limitations

1. The experiment uses a finite state model.
2. The trajectory horizon is limited to 10 steps.
3. Only one deterministic adaptive policy is evaluated.
4. The adaptive policy is history-sensitive but not an unrestricted adversary.
5. The modeled event set does not represent arbitrary real-world tools, side effects, or environmental channels.
6. The strengthened boundary is a modeled transition constraint rather than a claim about physical or deployed enforcement.
7. No conclusion about physical security, semantic correctness of a real deployment, or general AI safety follows from this experiment alone.

## Artifact

Files:

    darm_v0_3.py
    results.json
    README.md

The experiment is intended as a companion empirical artifact for the DARM formal work, not as a replacement for the machine-checked results.
