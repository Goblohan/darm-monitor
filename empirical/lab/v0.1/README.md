# DARM Empirical Lab v0.1

## Purpose

DARM Empirical Lab v0.1 is a minimal deterministic finite-state experiment examining the distinction between local transition authorization and a trajectory-level guarantee.

The experiment provides an executable companion to the DARM formal assurance-transfer work. It makes one structural phenomenon observable in a small, reproducible state-transition system:

> Local authorization of each individual transition does not necessarily establish preservation of a guarantee defined over the resulting trajectory.

This experiment is not itself a security monitor, verifier, formal proof of DARM, or claim of physical-system safety.
## Experimental Model

The system state is:

(balance, permission, credential, network, approval, transferred)

The experiment includes these events:

request, approve, transfer, revoke, refresh_credential, connect, disconnect, clear_approval.

A transfer is locally authorized when permission, credential, network, approval, and sufficient balance are all present.

The trajectory-level guarantee is:

transferred <= 50

The baseline boundary does not encode this cumulative trajectory constraint.

## Principal Witness

The principal trajectory is:

request -> approve -> transfer -> approve -> transfer

Starting from a balance of 100 and zero cumulative transfer, each individual transition is locally authorized.

The two transfers produce:

balance: 100 -> 50 -> 0

transferred: 0 -> 50 -> 100

Therefore the baseline result is:

- all transitions locally authorized: True
- trajectory guarantee: False
- counterexample: True

The cumulative transfer reaches 100, exceeding the trajectory limit of 50.
## Strengthened Boundary

A second experiment adds the trajectory-level constraint to transfer authorization.

Before executing a transfer, the strengthened boundary checks:

current transferred + transfer amount <= trajectory limit

Under the same witness trajectory, the first transfer is permitted and the second transfer is blocked.

The resulting state has:

- balance: 50
- transferred: 50
- trajectory guarantee: True
- blocked event: transfer

## Observed Result

| Regime | Individual transitions | Trajectory guarantee |
|---|---|---|
| Baseline | All authorized | Violated |
| Strengthened boundary | Second transfer blocked | Preserved |

The experiment demonstrates that a boundary which authorizes transitions using only local conditions can admit a trajectory that violates a guarantee whose dependency is cumulative across transitions.

Conversely, representing the relevant trajectory constraint at the authorization boundary allows the boundary to reject the violating transition in this model.
## Relation to DARM Assurance Transfer

This experiment is an empirical companion to the formal assurance-transfer work.

It illustrates, in executable form, the distinction between:

1. an authorization condition attached to an individual transition; and
2. a guarantee whose validity depends on the history or cumulative state of the system.

The experiment does not establish the general DARM transfer calculus by itself.

In particular, it does not prove that every real-world dependency can be represented, that a physical enforcement boundary is complete, or that an implementation faithfully realizes the modeled transition system.

The formal DARM work addresses assurance-transfer conditions more generally, including dependency representation, boundary coverage, discharge, semantic realization, and the limits of transferring assurance across changed contexts.

## Reproducibility

The experiment requires Python 3 and uses only the Python standard library.

Run the experiment:

python3 darm_v0_1.py

Syntax-check the implementation:

python3 -m py_compile darm_v0_1.py

Regenerate machine-readable results:

python3 -c 'import json; import darm_v0_1 as d; b=d.run_baseline_experiment(); s=d.run_strengthened_boundary_experiment(); json.dump({\"version\":\"v0.1\",\"baseline\":b,\"strengthened_boundary\":s}, open(\"results.json\",\"w\"), indent=2, default=lambda o:o.__dict__)'

The resulting results.json records the trajectory, authorization outcomes, final states, guarantee evaluation, and transition traces.
## Files

- darm_v0_1.py — executable experiment
- results.json — machine-readable experimental results
- README.md — experimental description and reproducibility record

## Scope and Limitations

This is deliberately a small laboratory experiment.

It does not claim:

- deployment readiness;
- cryptographic security;
- physical enforcement;
- complete mediation in an arbitrary implementation;
- semantic correctness of an external system;
- resistance to arbitrary real-world attackers;
- formal verification of the Python implementation;
- proof of the DARM theory.

Its purpose is narrower: to provide a deterministic executable witness for the difference between local transition authorization and trajectory-level guarantee preservation.

## Version

**DARM Empirical Lab v0.1**

Author: **Olusanya Gbolahan V**

**Perceptra AI Lab**
