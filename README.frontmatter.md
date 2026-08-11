# DARM



## Deterministic Algebraic Reference Monitor



**A machine-checked investigation of how safety-relevant authority constraints survive the transition from formal specification to executable enforcement.**



DARM is a Lean 4 formalization of a reference-monitor model combining discrete authority constraints with a continuous safety boundary.



The project asks a narrower question than "can a monitor be proved safe?":



> **Which guarantees survive as the model moves from mathematics to computation, finite-width representation, native execution, and empirical validation?**



DARM treats every transition between those layers as a potential trust boundary.



```text

Formal specification

&#x20;       |

&#x20;       v

Machine-checked proof

&#x20;       |

&#x20;       v

Computable refinement

&#x20;       |

&#x20;       v

Fixed-point / finite representation

&#x20;       |

&#x20;       v

64-bit arithmetic

&#x20;       |

&#x20;       v

Native implementation

&#x20;       |

&#x20;       v

Differential validation

```



The development is deliberately adversarial. Claims are generalized, instantiated, tested for necessity, exposed to countermodels, refined when necessary, and carried toward executable implementations.



**Status:** active research prototype. Not a deployed safety system.



\---



## The research program



DARM currently develops three connected research threads.



### 1. Formal authority and control



The discrete stratum models capabilities, policies, execution, ratification, and active-set behavior.



Capability gating is causally connected to execution: under the modeled confinement conditions, actions outside the permitted capability set become unreachable.



The model has also been instantiated on tool-calling, where the discrete layer establishes that specified actions such as bash and email are unreachable under scope confinement.



The continuous stratum is intentionally not claimed to be instantiated by that example.



### 2. Specification-to-execution refinement



The mathematical boundary certificate is progressively refined into executable representations:



```text

Real-valued certificate

&#x20;       |

&#x20;       v

Computable exponential bounds

&#x20;       |

&#x20;       v

Fixed-point evaluator

&#x20;       |

&#x20;       v

Int64 refinement

&#x20;       |

&#x20;       v

Native C implementation

```



The goal is not to assume that an abstract proof automatically transfers to executable code.



The transfer itself is part of the research.



### 3. Assumption minimality



DARM maintains an explicit assumption registry and tests assumptions for:



* necessity

* independence

* redundancy

* satisfiability

* deployment relevance



The project distinguishes an assumption that is necessary for a theorem from one that is actually load-bearing for a proposed deployment.



As the formalization grows, these distinctions are themselves machine-checked.



\---



## What the current development establishes



| Area                    | Current evidence                                         |

| ----------------------- | -------------------------------------------------------- |

| Discrete authority      | Machine-checked monitor properties                       |

| Capability confinement  | Machine-checked behavioral confinement                   |

| Cross-stratum coherence | Machine-checked single-step preservation                 |

| Ratification            | Machine-checked guarded transition properties            |

| Reachability            | Necessary and sufficient results under stated conditions |

| Continuous certificate  | Machine-checked formal model                             |

| Computable evaluation   | Machine-checked exponential refinement                   |

| Fixed-point evaluation  | Executable, fail-closed refinement                       |

| 64-bit arithmetic       | Machine-checked refinement inside stated envelopes       |

| Native implementation   | Differentially validated against the Lean implementation |

| Verification workflow   | Build, axiom-trace, and runtime gates                    |

| Assumption minimality   | Explicit countermodels and redundancy proofs             |



\---



## Results that changed the model



DARM deliberately preserves results that contradicted or refined initial expectations.



### Capability confinement does not imply noninterference



The modeled capability-confinement property and noninterference are formally independent.



This prevents the project from treating authority restriction as a substitute for information-flow guarantees.



### The coarse capacity bound is not an operating envelope



The capacity bound is a necessary condition, but empirical evaluation showed that interpreting it as a practical operating envelope is misleading.



The development subsequently derives a sharper feasibility characterization and separates:



1\. necessary conditions

2\. exact runtime conditions

3\. sufficient design-time conditions



### Exact computation has structural costs



The rational boundary-update instance admits exact fixed-point evaluation but loses properties retained by the exponential update, including composition and global positivity.



The choice of update rule is therefore a formal tradeoff, not merely an implementation preference.



### Native arithmetic exposed a real semantic boundary



Differential testing uncovered a discrepancy between C's division semantics and Lean's integer division semantics.



The native implementation was corrected before the differential result was accepted.



### The benchmark itself was wrong



The first native benchmark contained loop-invariant work that the compiler could hoist away.



The benchmark was corrected and rerun before its result was used.



The corrected differential run reported **50,012 agreeing pairs**.



\---



## Verification philosophy



A successful build is not treated as sufficient evidence.



DARM uses multiple checks:



1\. source-level placeholder detection

2\. axiom auditing

3\. axiom-trace coverage

4\. clean-build verification

5\. native differential testing

6\. CI runtime gating



This discipline was strengthened when the project identified gaps between what the verification workflow claimed to enforce and what it actually checked.



The verification process is therefore itself treated as part of the trusted boundary.



\---



## 5-minute evaluation



If you are evaluating the project for the first time, start here:



### 1. Formal core



Read the discrete monitor and boundary modules.



### 2. Negative results



Read the noninterference, feasibility, and rational-update results.



### 3. Refinement



Follow:



`FixedPoint -> ExpEvaluator -> EvaluatorTower -> Fixed64Evaluator`



### 4. Native boundary



Follow:



`Fixed64Refinement -> Fixed64Native -> C implementation -> differential tests`



### 5. Assumption analysis



Read the minimality modules and compare theorem-necessary assumptions with deployment-relevant assumptions.



\---



## Current frontier



The formal-to-executable chain is substantially developed.



The major remaining research question is further upstream:



> **Do the formally specified authority properties capture the behavior that matters when the controlled system is an actual AI model?**



That requires an empirical bridge between AI behavior and the formal authority state.



DARM does not currently claim to have established that bridge.



That is the next research frontier.




