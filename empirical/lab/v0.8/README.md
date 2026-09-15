# DARM Empirical Lab v0.8
## Causal Stress Test of Dependency Coverage

### Purpose

v0.8 stress-tests the v0.7 dependency/coverage result rather than simply
repeating it. It independently varies declared dependency surfaces and
boundary coverage across a finite factorial family, introduces multiple
alternative guarantee-changing routes, and adds an irrelevant dependency as
a negative control.

The central question is whether the observed relationship between dependency
coverage and adversarial reachability survives these perturbations.

### What is new

v0.8 adds:

- three independent routes to the same cumulative protected effect;
- an irrelevant `authD` dependency attached to an audit transition;
- independent variation of dependency declarations and boundary coverage;
- reachable and structurally inadmissible cases;
- explicit mediation audits;
- a negative-control analysis;
- a search for the critical contradiction `GRBS=True` with a winning region.

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
python3 empirical/lab/v0.8/darm_v0_8.py
```

Then inspect:

```text
empirical/lab/v0.8/results.json
```

Also run:

```bash
python3 -m py_compile empirical/lab/v0.8/darm_v0_8.py
```

and:

```bash
git diff --check -- empirical/lab/v0.8
```

### Artifact discipline

v0.1-v0.7 are frozen. Do not modify them as part of v0.8.
Do not use `git add .`; stage only the four v0.8 files.
