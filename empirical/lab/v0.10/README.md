# DARM Empirical Lab v0.10
## Representation Adequacy Under History-Dependent Effective Capability

### Purpose

v0.10 extends the v0.9 history-divergence experiment with a bounded representation-adequacy test.

The central question is whether a candidate representation preserves guarantee-relevant future behavior when different execution histories are mapped to the same representation.

The experiment distinguishes two questions:
1. whether a representation captures the effective internal state of the modeled world; and
2. whether the representation preserves guarantee-relevant behavior reachable from that state.

A hidden effective-state difference is not treated as a representation failure unless it produces a difference in measured guarantee-relevant future behavior.

### Representation relation

For an execution history H, let `Rep_R(H)` denote the representation produced by candidate representation R.

Two histories are representation-equivalent when:

```text
H_A ~_R H_B  iff  Rep_R(H_A) = Rep_R(H_B)
```

Representation adequacy is tested against the bounded future behavioral signature:

```text
Rep_R(H_A) = Rep_R(H_B)  =>  B_d(H_A) = B_d(H_B)
```

where `B_d(H)` records guarantee-relevant behavior reachable within future depth `d`.

The behavioral signature deliberately hides the `latent_route` implementation state. It records only guarantee-changing future transitions as:

```text
(event_name, resulting_transferred, violation_status)
```

### Candidate representations

- **R0:** represented DARM `State` only.
- **R1:** `State` plus approval. This is intentionally redundant because approval is already represented in `State`.
- **R2:** `State` plus the hidden `latent_route` capability.
- **R3:** `State` plus the current effective transfer capability.

R0 tests the adequacy of the existing represented state.

R1 tests whether adding an already-represented field changes the result.

R2 is an implementation-level repair that explicitly represents the hidden history-induced capability.

R3 tests whether current effective capability is sufficient to preserve future guarantee-relevant behavior.

### v0.9 baseline witness

The v0.9 experiment established that two histories can converge to the same represented state while retaining different effective capabilities:

```text
History A:
approve -> connect -> transfer -> revoke

History B:
approve -> connect -> activate_latent_route -> transfer -> revoke
```

The v0.10 experiment asks the stronger question: does the candidate representation preserve the future guarantee-relevant behavior of those histories?

### Results

The bounded experiment uses history depth 5 and future depth 3.

| Representation | Equivalent pairs | Divergent pairs | Result |
|---|---:|---:|---|
| R0 State | 18 | 4 | FAIL |
| R1 State + approval | 18 | 4 | FAIL |
| R2 State + latent_route | 0 | 0 | ADEQUATE within tested bounds |
| R3 State + effective capability | 15 | 1 | FAIL |

The stronger finding is that the R3 semantic snapshot can still alias histories whose future guarantee-relevant behavior differs.

### R3 counterexample

```text
History A:
approve -> revoke

History B:
approve -> revoke -> connect -> activate_latent_route -> disconnect
```

At the comparison point, both histories have:

```text
permission = false
credential = true
network = false
approval = true
balance = 100
transferred = 0
```

Both also have no currently effective transfer capability.

Nevertheless, their future behavioral signatures differ. History A cannot reach a guarantee-changing transfer under the modeled future semantics. History B can reconnect and exploit its retained latent capability. Within the bounded future depth, it can reach a transfer outcome that exceeds the represented trajectory limit, producing a violation.

Thus:

```text
Rep_R3(H_A) = Rep_R3(H_B)
B_3(H_A) != B_3(H_B)
```

This is a behavioral divergence, not merely a difference in hidden implementation state.

### Interpretation

The v0.10 result separates:

**Snapshot capability adequacy:** a representation captures what the system can effectively do at the current state.

**Future behavioral adequacy:** a representation preserves the guarantee-relevant behavior that remains reachable from that state.

R3 passes the first intuition but fails the second in the bounded counterexample. Current inability to act does not imply equality of future guarantee-relevant behavior when latent capability can become effective after a future transition.

This suggests that assurance representations for history-dependent systems may need to preserve not merely present capability, but information required to determine future guarantee-relevant behavior.

### Relation to DARM

A boundary claim is not fully characterized merely by the state currently visible to the monitor. If distinct histories can map to the same monitored representation while inducing different future guarantee-relevant behavior, then a local assurance claim based on that representation may fail to characterize the effective boundary.

The empirical lab does not claim that this toy model establishes the result for all DARM systems. It provides a bounded counterexample to candidate representations under the specified transition system.

### Scope and non-claims

This experiment does not establish:
- universal inadequacy of state-based representations;
- universal impossibility of semantic capability representations;
- minimality of R2;
- correctness of the toy model as a representation of deployed agent systems;
- physical or cryptographic security;
- completeness of the modeled event set;
- unrestricted reachability beyond the tested depths.

R2 is reported only as adequate within the tested bounds.

R3 is reported as falsified by one bounded behavioral counterexample.

### Reproducibility

```text
python3 -m py_compile empirical/lab/v0.10/darm_v0_10.py
python3 empirical/lab/v0.10/darm_v0_10.py
```

The experiment writes:

```text
empirical/lab/v0.10/results.json
```

### Artifact discipline

The intended v0.10 artifact set is:

```text
empirical/lab/v0.10/darm_v0_10.py
empirical/lab/v0.10/README.md
empirical/lab/v0.10/SPEC.md
empirical/lab/v0.10/results.json
```

No unrelated repository files are part of the v0.10 change.
