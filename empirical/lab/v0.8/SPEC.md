# DARM Empirical Lab v0.8 Specification
## Causal Stress Test of Dependency Coverage

### Status

v0.8 is a new experiment derived from the frozen v0.7 state-machine semantics.
The v0.7 artifact is not modified.

### Research question

Does the structural relationship between guarantee-relevant dependency coverage and
adversarial reachability survive systematic perturbation involving:

1. multiple alternative guarantee-changing routes;
2. irrelevant dependencies;
3. irrelevant boundary coverage;
4. reachable and unreachable dependencies;
5. independent expansion/restoration of boundary coverage?

### Frozen semantics

The following are preserved from v0.7:

- State variables: balance, permission, credential, network, approval, transferred.
- Initial state: balance=100, permission=True, credential=True,
  network=False, approval=False, transferred=0.
- Transfer amount: 50.
- Trajectory limit: 50.
- Maximum reachability depth: 50.
- Local authorization semantics for the original transfer routes.
- Deterministic state-transition semantics.
- Reachable-state graph construction.
- Violating predicate: transferred > trajectory limit.
- Finite adversarial winning-region fixed point.

### New v0.8 model

Four authority/dependency identifiers are used:

- authA
- authB
- authC
- authD

Guarantee-changing routes:

- transfer      -> authA
- transfer_alt  -> authB
- transfer_aux  -> authC

Non-guarantee-changing route:

- audit -> authD

The audit transition changes only an audit counter represented outside the
guarantee state. authD must therefore not appear in the semantic dependency
surface for the transfer guarantee.

### Configuration generation

The experiment constructs a factorial family over:

- dependency declarations;
- boundary coverage sets;
- route reachability.

The structural dependency surface used for GRBS is the semantically derived
guarantee-relevant surface, not the declared surface.

### Critical non-circularity rule

GRBS must be calculated independently of the winning-region analysis.

A path is not classified as guarantee-relevant because it is violating.
A transition is guarantee-relevant because it changes the modeled guarantee
state (`transferred`), after which its declared transition dependency is
collected.

### Mediation rule

For a locally authorized guarantee-changing transition:

- if all required dependencies are covered by the boundary, the cumulative
  transfer constraint is applied;
- if required dependencies are not covered, the cumulative transfer constraint
  is not applied.

The experiment must record this explicitly for every guarantee-changing
transition considered in the graph.

### Falsification conditions

The experiment is invalid if:

1. an intended alternative route cannot produce the protected cumulative effect
   when its prerequisites and dependency are available;
2. relevant uncovered routes receive the cumulative boundary constraint;
3. relevant covered routes fail to receive the cumulative boundary constraint;
4. irrelevant dependencies enter the guarantee-relative semantic dependency
   surface;
5. adding coverage for an irrelevant dependency changes guarantee-relevant
   mediation;
6. GRBS is inferred from winning-region results;
7. dependency expansion/coverage variation is encoded by directly assigning
   safety outcomes rather than by changing transition semantics;
8. any configuration with GRBS=True has a winning region;
9. the results are nondeterministic.

### Interpretation

The experiment does not assume that GRBS failure implies exploitability.
A configuration may be structurally inadmissible while having no reachable
winning route. Such a case is a conservative structural rejection and is
scientifically useful.

The strongest contradiction would be:

GRBS=True AND initial_state_winning=True.

That would indicate that the current dependency/coverage abstraction is
insufficient for the finite model.

### Scope

v0.8 is a finite executable model experiment. It does not establish physical
enforcement, unrestricted adversarial security, semantic correctness of
external systems, or general AI safety.
