# DARM Empirical Lab v0.9
## History-Induced Boundary Divergence

### Purpose

v0.9 extends the v0.8 dependency/coverage stress test with a distinct
representation-adequacy experiment.

The central question is whether two execution histories can converge to the same
represented DARM state while retaining different effective capabilities, such
that their future effective reachability differs.

### What is new

v0.9 retains the complete v0.8 factorial experiment and adds a bounded
history-divergence witness.

- two explicit execution histories;
- a hidden history-induced latent capability;
- convergence to the same represented `State`;
- independent effective-history reachability;
- represented-state reachability under the DARM boundary;
- a violation-reachability comparison;
- an explicit state-aliasing test.

### Important interpretation

`GRBS=False` is not treated as equivalent to exploitability.

The experiment explicitly tests for configurations that are structurally
inadmissible while no violating state is reachable. No such configuration was
observed in this factorial model.

The critical finite-model contradiction is:

```text
GRBS=True
+
initial_state_winning=True
```

If that occurs, the dependency/coverage abstraction is insufficient for the
modeled transition system and must be investigated rather than explained away.

### Non-circularity

The semantic dependency surface is derived from executed transitions that
actually change the guarantee state. It is not inferred from whether a
transition is violating.

GRBS is computed from:

```text
semantic dependency surface ⊆ boundary coverage
```

independently of the winning-region computation.

### Mediation

For guarantee-changing transitions:

```text
covered dependency
    -> cumulative boundary applies

uncovered dependency
    -> cumulative boundary does not apply
```

The recorded transition audit exposes this distinction directly.

### Scope

The experiment is exhaustive only over its declared finite factorial model.
It does not establish unrestricted adaptive-adversary security, physical
enforcement, semantic correctness of external systems, or general AI safety.

It is an empirical stress test of the structural relationship represented by
DARM.

### Reproducibility

Run:

```bash
python3 empirical/lab/v0.9/darm_v0_9.py
```

Then inspect:

```text
empirical/lab/v0.9/results.json
```

Also run:

```bash
python3 -m py_compile empirical/lab/v0.9/darm_v0_9.py
```

and:

```bash
git diff --check -- empirical/lab/v0.9
```

### Artifact discipline

v0.1-v0.8 are frozen. Do not modify them as part of v0.9.
Do not use `git add .`; stage only the intended v0.9 experiment files.
