# DARM Empirical Lab v0.9 Specification
## History-Induced Boundary Divergence

### Status

v0.9 is an extension of the frozen v0.8 dependency/coverage stress test.
The v0.8 artifact and its state-machine semantics are not modified.

v0.9 retains the complete v0.8 factorial experiment and adds a bounded
history-divergence experiment targeting representation adequacy.

### Research questions

v0.9 evaluates two related questions.

1. Does the structural relationship between guarantee-relevant dependency
   coverage and adversarial reachability survive the v0.8 factorial stress test?

2. Can two execution histories converge to the same represented DARM state
   while retaining different effective capabilities, such that their future
   effective reachability differs?

The second question targets a limitation that is distinct from dependency
coverage failure. It asks whether the represented state is sufficient to
characterize effective future reachability when execution history can induce
capability not represented in that state.

### Frozen v0.8 semantics

The following are preserved from v0.8:

- State variables: balance, permission, credential, network, approval,
  transferred, audit_count.
- Initial represented state: balance=100, permission=True, credential=True,
  network=False, approval=False, transferred=0, audit_count=0.
- Transfer amount: 50.
- Trajectory limit: 50.
- Maximum reachability depth: 50.
- Local authorization semantics for the modeled transfer routes.
- Deterministic state-transition semantics.
- Reachable-state graph construction.
- Violating predicate: transferred > trajectory limit.
- Finite adversarial winning-region fixed point.
- Dependency/coverage factorial experiment.

### v0.8 dependency and coverage model

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

### v0.8 configuration generation

The factorial experiment constructs configurations over:

- dependency declarations;
- boundary coverage sets;
- route reachability.

The structural dependency surface used for GRBS is the semantically derived
guarantee-relevant surface, not the declared surface.

### Critical non-circularity rule

GRBS must be calculated independently of winning-region analysis.

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

The experiment records this explicitly for every guarantee-changing transition
considered in the graph.

### v0.9 history-divergence model

The history-divergence experiment introduces a bounded hidden capability that
is induced by one execution history but absent from another.

Two histories are constructed:

History A:

    approve -> connect -> transfer -> revoke

History B:

    approve -> connect -> activate_latent_route -> transfer -> revoke

The histories converge to the same represented DARM state:

    balance       = 50
    permission    = False
    credential    = True
    network       = True
    approval      = True
    transferred   = 50
    audit_count   = 0

The effective latent capability differs:

    latent_route_A = False
    latent_route_B = True

The latent route is intentionally outside the represented DARM state and
provides an effective guarantee-changing route that bypasses the represented
permission condition.

The effective-world transition system does not apply the represented
TRAJECTORY_LIMIT constraint to this latent route.

### State-aliasing condition

The history experiment explicitly tests the following representation relation:

    H_A != H_B
    Rep(H_A) = Rep(H_B)
    Capability(H_A) != Capability(H_B)

A stronger positive witness is obtained when:

    Rep(H_A) = Rep(H_B)

    not ViolationReachable_E(H_A)

    ViolationReachable_E(H_B)

where `E` denotes the effective history-dependent transition system.

This demonstrates that represented-state equality does not, by itself, imply
effective future reachability equivalence in the modeled system.

### Represented versus effective reachability

The experiment maintains a distinction between:

1. represented reachability, computed using the DARM represented state and its
   boundary-mediated transition semantics; and

2. effective-history reachability, computed using the history-dependent
   effective capability of the modeled world.

The history-divergence finding is therefore not a claim that the represented
DARM transition system violates its own trajectory constraint.

The expected positive witness is instead:

    represented violation reachable = False
    effective A violation reachable = False
    effective B violation reachable = True

### Falsification conditions

The v0.8 factorial experiment is invalid if:

1. an intended alternative route cannot produce the protected cumulative effect
   when its prerequisites and dependency are available;
2. relevant uncovered routes receive the cumulative boundary constraint;
3. relevant covered routes fail to receive the cumulative boundary constraint;
4. irrelevant dependencies enter the guarantee-relative semantic dependency
   surface;
5. adding coverage for an irrelevant dependency changes guarantee-relevant
   mediation;
6. GRBS is inferred from winning-region results;
7. dependency expansion or coverage variation is encoded by directly assigning
   safety outcomes rather than by changing transition semantics;
8. any configuration with GRBS=True has a winning region;
9. the results are nondeterministic.

The v0.9 history experiment is invalid if:

10. the two witness histories do not converge to the same represented state;
11. the latent capability is not different between the two histories;
12. the effective transition system does not permit the latent capability to
    influence future reachability;
13. the effective violation result is obtained by directly assigning the
    violation outcome rather than through the modeled transitions;
14. represented-state reachability and effective-history reachability are
    conflated;
15. the positive witness depends on nondeterministic execution.

### Interpretation

GRBS failure is not treated as equivalent to exploitability.

A configuration may be structurally inadmissible while having no reachable
winning route. Such a case is a conservative structural rejection and is
scientifically useful.

The strongest contradiction for the v0.8 factorial experiment remains:

    GRBS=True AND initial_state_winning=True

Such a result would indicate that the dependency/coverage abstraction is
insufficient for the finite model.

The v0.9 history-divergence result addresses a different issue.

A positive history-divergence witness means that the current represented-state
abstraction is insufficient to characterize effective future reachability for
the modeled history-dependent system.

It does not establish that real deployed systems contain the modeled latent
route. It does not invalidate the v0.8 GRBS result. It identifies a
representation-adequacy limitation under the stated finite model.

### Formal characterization

The history-divergence result can be summarized as:

    H_A != H_B
    Rep(H_A) = Rep(H_B)
    Capability(H_A) != Capability(H_B)

with the stronger reachability witness:

    not ViolationReachable_E(H_A)
    and
    ViolationReachable_E(H_B)

while:

    Rep(H_A) = Rep(H_B)

The finding therefore concerns the adequacy of `Rep` as an abstraction of the
effective state relevant to future guarantee reachability.

### Scope

v0.9 is a finite executable model experiment.

It does not establish physical enforcement, unrestricted adversarial security,
semantic correctness of external systems, or general AI safety.

The history-divergence experiment is a controlled counterexample within the
specified finite model. Its purpose is to identify a class of representation
failure that can arise when effective capability depends on execution history
not represented in the assurance state.

### Reproducibility

The primary executable artifact is:

    empirical/lab/v0.9/darm_v0_9.py

The primary result artifact is:

    empirical/lab/v0.9/results.json

The experiment must be reproducible by compiling and executing the v0.9
artifact without modification.

### Artifact discipline

v0.1-v0.8 are frozen. Do not modify them as part of v0.9.

Do not use `git add .`. Stage only the intended v0.9 experiment files.
