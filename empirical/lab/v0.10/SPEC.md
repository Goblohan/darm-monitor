# DARM Empirical Lab v0.10 Specification
## Representation Adequacy Under History-Dependent Effective Capability

### Status

Version: v0.10

Purpose: bounded empirical evaluation of candidate representations for
history-dependent effective capability.

This specification extends the v0.9 history-divergence experiment. The
v0.9 model and factorial experiment are retained. v0.10 adds a bounded test
of whether representation-equivalent execution histories preserve
guarantee-relevant future behavior.

### 1. Research question

The central question is:

> When two execution histories are mapped to the same candidate
> representation, does that representation preserve their bounded
> guarantee-relevant future behavior?

For a representation R and history H, define:

```text
Rep_R(H)
```

as the representation extracted from H at the comparison point.

Define representation equivalence:

```text
H_A ~_R H_B  iff  Rep_R(H_A) = Rep_R(H_B)
```

The primary adequacy condition is:

```text
Rep_R(H_A) = Rep_R(H_B)  =>  B_d(H_A) = B_d(H_B)
```

where `B_d(H)` is the bounded future behavioral signature at future depth d.

A representation therefore fails the tested adequacy condition when there
exists a pair of histories that are representation-equivalent but have
different guarantee-relevant future behavior within the specified bound.

### 2. Behavioral signature

v0.10 distinguishes effective internal-state divergence from behavioral
divergence.

A hidden state difference alone is not sufficient to classify a candidate
representation as behaviorally inadequate.

The measured future signature records only guarantee-changing transitions:

```text
(event_name, resulting_transferred, violation_status)
```

The hidden `latent_route` variable is deliberately excluded from this
signature.

This makes the test behavioral rather than a direct comparison of hidden
implementation state.

### 3. Frozen model

The v0.10 experiment retains the v0.8/v0.9 toy transition model.

The represented state contains:

```text
balance
permission
credential
network
approval
transferred
audit_count
```

The effective history state additionally contains:

```text
latent_route
```

The guarantee-changing events are:

```text
transfer
transfer_alt
transfer_aux
```

The represented trajectory limit is:

```text
TRAJECTORY_LIMIT = 50
```

A represented violation occurs when:

```text
transferred > TRAJECTORY_LIMIT
```

A guarantee-changing event is locally authorized when the represented state
satisfies the required permission, credential, network, approval, and balance
conditions.

### 4. History-dependent effective semantics

v0.10 permits the history-only event:

```text
activate_latent_route
```

when approval and network are present.

This event sets:

```text
latent_route = true
```

The ordinary future event set remains the original `EVENTS` set. Thus the
history-generation mechanism can create a latent capability, while future
reachability evaluates the resulting effective state using the modeled
ordinary event transitions.

When `latent_route` is active, a guarantee-changing event can be effectively
authorized using the modeled latent-route conditions rather than the
represented permission field.

This creates the history-dependent distinction under test.

### 5. v0.9 baseline witness

The v0.9 experiment established the following history-divergence witness:

```text
History A:
approve -> connect -> transfer -> revoke

History B:
approve -> connect -> activate_latent_route -> transfer -> revoke
```

The two histories converge to the same represented state while retaining
different latent effective capabilities.

The v0.9 result therefore established history-induced boundary divergence
under the toy model.

v0.10 asks whether that divergence is also relevant to future
guarantee-relevant behavior after applying candidate representations.

### 6. Candidate representations

Four candidate representations are evaluated.

#### R0: represented State

```text
R0(H) = represented State
```

This is the baseline representation used by the monitor model.

#### R1: State plus approval

```text
R1(H) = represented State + approval
```

Approval is already a field of `State`. R1 is therefore intentionally
redundant and tests whether adding an already-represented value changes the
adequacy result.

#### R2: State plus latent_route

```text
R2(H) = represented State + latent_route
```

R2 explicitly exposes the hidden history-induced capability.

This is an implementation-level repair, not a claim that `latent_route`
is the correct representation for deployed systems.

#### R3: State plus current effective transfer capability

```text
R3(H) = represented State + effective_transfer_capability
```

R3 tests a stronger semantic abstraction. It asks whether knowing what the
system can effectively do at the current comparison point is sufficient to
preserve its future guarantee-relevant behavior.

### 7. Bounds

The experiment uses:

```text
history depth = 5
future depth  = 3
```

The bounded history enumeration produces:

```text
effective history states = 63
```

These bounds are part of the experiment definition and do not imply
unbounded properties.

### 8. Adequacy test

For each candidate representation:

1. Enumerate effective histories up to the history-depth bound.
2. Compute the candidate representation of each resulting history.
3. Partition histories by representation equivalence.
4. For each equivalence class containing multiple histories, compute the
   bounded guarantee-relevant future behavioral signature.
5. Search for pairs with identical representations and different signatures.
6. Report the candidate as adequate only when no divergent equivalent pair
   is found within the tested set.

Formally, the bounded test searches for:

```text
exists H_A, H_B:
    Rep_R(H_A) = Rep_R(H_B)
    and
    B_d(H_A) != B_d(H_B)
```

If such a pair exists, the candidate fails the bounded behavioral adequacy
test.

### 9. Results

The persisted v0.10 results are:

| Representation | Equivalent pairs | Divergent pairs | Adequacy |
|---|---:|---:|---|
| R0 | 18 | 4 | FAIL |
| R1 | 18 | 4 | FAIL |
| R2 | 0 | 0 | ADEQUATE within tested set |
| R3 | 15 | 1 | FAIL |

The experiment therefore produces:

```text
R0 fails: true
R1 fails: true
R2 repairs: true
R3 repairs: false
```

### 10. R2 qualification

The R2 result requires an important qualification.

R2 has zero representation-equivalent history pairs in the tested history
set because the additional `latent_route` field distinguishes the histories
that otherwise alias under R0.

Consequently, the implication tested by the experiment has no nontrivial
equivalent pair on which to produce a counterexample.

R2 is therefore reported as:

> adequate within the tested set, with no representation-equivalent pairs
> remaining.

This is not a proof of universal sufficiency, and it is not a minimality
result.

In particular, the experiment does not establish that `latent_route` is the
smallest sufficient representation or that the same result holds for a
different transition system.

### 11. R3 behavioral counterexample

The R3 failure is witnessed by:

```text
History A:
approve -> revoke

History B:
approve -> revoke -> connect -> activate_latent_route -> disconnect
```

At the comparison point, both histories have the same represented state:

```text
balance = 100
permission = false
credential = true
network = false
approval = true
transferred = 0
audit_count = 0
```

Both have:

```text
effective_transfer_capability = false
```

Thus:

```text
Rep_R3(H_A) = Rep_R3(H_B)
```

Nevertheless, the bounded future signatures differ.

History A has no guarantee-changing future transition in the measured
signature.

History B can reconnect and then use its retained latent route. Within the
future-depth bound, it can reach:

```text
transfer       -> transferred = 100, violation = true
transfer       -> transferred = 50,  violation = false
transfer_alt   -> transferred = 100, violation = true
transfer_alt   -> transferred = 50,  violation = false
transfer_aux   -> transferred = 100, violation = true
transfer_aux   -> transferred = 50,  violation = false
```

Therefore:

```text
B_3(H_A) != B_3(H_B)
```

while:

```text
Rep_R3(H_A) = Rep_R3(H_B)
```

This is a behavioral counterexample to R3 within the specified bounds.

### 12. Interpretation

The result separates two notions of adequacy.

**Snapshot capability adequacy** asks whether a representation captures what
the system can effectively do at the current state.

**Future behavioral adequacy** asks whether the representation preserves the
guarantee-relevant behavior that remains reachable from that state.

The R3 counterexample shows that the second property is strictly stronger
in this model.

Two histories can have identical current effective transfer capability,
yet differ in latent structure that becomes relevant after a future
transition. Therefore current capability alone does not preserve future
guarantee-relevant behavior in this bounded experiment.

### 13. Relation to DARM

The experiment gives an empirical characterization of one representation
problem relevant to DARM.

A monitor-side representation can be insufficient for an assurance claim
if distinct effective histories collapse to the same representation while
retaining different guarantee-relevant future behavior.

This does not mean that every hidden state variable must be exposed.
The measured criterion is behavioral. Hidden differences matter when they
change the future behavior relevant to the guarantee being evaluated.

The result therefore motivates treating representation adequacy as a
property of the boundary model itself rather than assuming that a chosen
state representation is automatically sufficient.

### 14. Non-claims

This experiment does not establish:

- universal inadequacy of state-based representations;
- universal impossibility of semantic capability representations;
- minimality of R2;
- universal sufficiency of R2;
- correctness of the toy model as a model of deployed agent systems;
- physical security;
- cryptographic security;
- completeness of the modeled event set;
- unrestricted reachability beyond the tested history and future depths.

The result is empirical and bounded.

### 15. Reproducibility

From the repository root:

```text
python3 -m py_compile empirical/lab/v0.10/darm_v0_10.py
python3 empirical/lab/v0.10/darm_v0_10.py
```

The second command regenerates:

```text
empirical/lab/v0.10/results.json
```

The JSON artifact contains the factorial results, history-divergence
results, representation-adequacy results, and bounded witnesses.

### 16. Artifact set

The intended v0.10 artifact set is:

```text
empirical/lab/v0.10/darm_v0_10.py
empirical/lab/v0.10/README.md
empirical/lab/v0.10/SPEC.md
empirical/lab/v0.10/results.json
```

No unrelated repository files are part of the v0.10 change.

### 17. Research status

v0.10 establishes a bounded empirical distinction between current
capability representation and future behavioral adequacy.

The strongest current result is the R3 counterexample:

```text
same represented state
+
same current effective capability
+
different bounded future guarantee behavior
```

This provides evidence that, for history-dependent effective capability,
future behavioral adequacy can require more information than a snapshot of
current capability.
