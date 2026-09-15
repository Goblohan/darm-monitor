# DARM Empirical Lab v0.2

## Purpose

v0.2 extends the DARM empirical laboratory from a single hand-constructed witness to exhaustive enumeration of a finite trajectory space.

The experiment tests whether locally authorized transitions can nevertheless produce a trajectory-level violation of a cumulative guarantee, and whether an explicitly strengthened boundary prevents that violation within the same finite model.

## Experimental Model

The system state contains:

- balance
- permission
- credential
- network status
- approval status
- cumulative amount transferred

The event alphabet contains eight events:

request, transfer, revoke, refresh_credential, connect, disconnect, approve, clear_approval

Trajectories have length five.

The resulting finite trajectory space is:

8^5 = 32,768 trajectories.

## Baseline Experiment

The baseline authorization predicate checks local conditions for each transition but does not impose the cumulative transfer limit as an authorization condition.

A trajectory is considered globally safe when cumulative transferred amount remains at or below:

50

The exhaustive enumeration found:

- Total trajectories: 32,768
- Locally authorized trajectories: 8,756
- Locally authorized trajectories violating the guarantee: 229

Thus, within this finite model, locally authorized trajectories can violate the trajectory-level guarantee.

The first counterexample recorded by the enumeration is:

request -> request -> approve -> transfer -> transfer

The cumulative transferred amount reaches:

0 -> 50 -> 100

while the guarantee limit is 50.

## Strengthened Boundary

The strengthened boundary adds the cumulative constraint to transfer execution:

transferred + transfer_amount <= trajectory_limit

Across the complete 32,768-trajectory space:

- Strengthened-boundary violations: 0
- Trajectories containing a locally authorized but boundary-blocked event: 287

Thus, within the explicitly defined finite model, the strengthened boundary eliminated all observed guarantee violations.

## Interpretation

The experiment provides empirical evidence for the following bounded observation:

Local transition authorization does not by itself establish a trajectory-level guarantee when the guarantee depends on cumulative state.

Preservation requires the relevant dependency to be represented in the enforcement condition.

This is an empirical demonstration of the failure mode studied by the DARM assurance-transfer work. It is not a proof of the general DARM calculus.

## Scope and Limitations

This experiment is exhaustive only over the explicitly defined finite trajectory space:

- eight event types
- trajectory length five
- deterministic transition model
- fixed initial state
- fixed transfer amount
- fixed cumulative limit

It does not establish results for arbitrary trajectories, real systems, or arbitrary agents.

In particular, v0.2 is exhaustive trajectory enumeration rather than an adaptive-adversary experiment. The action sequence is enumerated independently of observed history rather than selected by an adaptive policy.

The strengthened-boundary result therefore means zero violations within this finite enumerated model, not a general physical or system-level safety guarantee.

## Reproducibility

Run:

python3 darm_v0_2.py

The experiment writes its machine-readable results to:

results.json

Syntax can be checked with:

python3 -m py_compile darm_v0_2.py

## Files

- darm_v0_2.py — experiment implementation
- results.json — machine-readable experimental result
- README.md — experiment description and scope

## Relation to DARM Assurance Transfer

The experiment operationalizes one narrow empirical question underlying the formal work:

whether assurance based only on local transition authorization remains valid when the target guarantee has a cumulative dependency that is not enforced at the same boundary.

The experiment should therefore be interpreted as a bounded empirical analogue of the formal distinction between local authorization and guarantee-relative dependency coverage.

## Version

v0.2

Perceptra AI Lab
Olusanya Gbolahan V
