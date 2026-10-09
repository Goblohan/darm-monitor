# E38 Evidence Freeze v0.1

**Research status:** experimental evidence inventory, not an end-to-end assurance certificate.
**Evidence cut:** 2026-10-09, based on the author's reported WSL execution logs.
**Parent research:** DARM, HDB-1E, E37 heterogeneous warrants, E38 conditional reliance non-laundering.
**DARM Core revision:** `7f8661f` on `research/e38-nonlaundering` (local commit).
**DARM Guard revision:** `8e4a045` on `hardening/agent-socket-readonly` (local checkout matching its remote tracking branch).
**Experiment:** `experiments/hdb1e_e37_nonlaundering/` (untracked at inventory; freeze is not a recorded commit until explicitly committed).

## 1. Research question and boundary

Can a downstream reliance gate reject target claims lacking appropriate warrants even when an upstream broker has authorized or executed an action, and can it refuse stale or conflicting execution evidence without treating authentic evidence as evidence of broader semantic truth?

The critical distinction is **authorized action ≠ current attested artifact ≠ warranted downstream claim ≠ external-world truth**. These are separately checked or separately assumed. An `ADMIT` verdict is justified *relative to the supplied trusted policy, attestations, audit history, witness, source receipts and interpretation*. It is not certification of the truth of an arbitrary report.

## 2. Proved / tested / assumed ledger

| Evidence category | Scope of result | Important limit |
|---|---|---|
| **Lean-proved, conditional** | `GRBS/E38RelianceNonLaundering.lean` compiled; `DARM.E38.admitted_implies_warranted` and `DARM.E38.asserted_does_not_suffice` were axiom-audited. The first used standard `propext`, and the second reported no axioms. | The admission implication assumes soundness of the modeled Boolean checks. It does not show that the Python checks implement those predicates or that the physical world makes the modeled facts true. |
| **Full Lean repository build** | `lake build GRBS`: 9,014 jobs completed; `scripts/gate.sh`: `GATE PASSED`, 162/162 GRBS roots, 1,301 theorems in built GRBS modules, documentation and cited theorem existence checks passed. | Repository build and indexing are not a refinement proof of the Python runtime. |
| **Python behavioral tests** | 123/123 tests reported passing across six suites on WSL with the local DARM Guard checkout. | Selected functional/adversarial cases; no coverage-completeness claim. |
| **Live broker experiment** | A disposable Guard broker, actual kernel, socket, real local writes, file attestations, audit log and checkpoints exercised. A superseded attestation was refused under a later snapshot. | The test used `/tmp` resources, synthetic HDB warrants, and a checkpoint sink on the same host; it did not establish externally hosted freshness or general complete mediation. |
| **Rollback and witness testing** | Signed witness and persisted monotonic pin tests detect older snapshots and forks **relative to the stored, independently trusted pin**. | Protecting the pin, obtaining fresh witnesses, and resisting full trusted-state rollback remain environmental assumptions. |
| **External semantic truth** | Not established by this experiment. | Verified signatures authenticate assertions or recorded effects; they do not establish that the issuer's semantic assertions are truthful or observationally adequate. |

`0 declared axioms / 0 sorry` in the repository source inventory does **not** mean all theorems depend on no axioms: Lean's standard axioms may still appear in `#print axioms` results.

## 3. Test register

| Test module | Reported result | Principal tested boundary |
|---|---:|---|
| `tests` | 29/29 | HDB-1E mapping, issuer scope, source/target evidence, expiry, request and subject binding, target obligations |
| `test_guard_bridge` | 23/23 | Guard Ed25519 artifact attestation; mismatch, tamper and semantic non-laundering |
| `test_guard_audit_bridge` | 24/24 | Signed audit snapshot, prior preparation, outcome correspondence, supersession, checkpoints |
| `test_live_guard_broker` | 1/1 | Actual broker/kernel/socket/write/attestation/audit integration; old-snapshot negative control |
| `test_guard_witness_bridge` | 20/20 | Separate witness signatures, forks, older-than-trusted-pin rollback |
| `test_guard_monotonic_bridge` | 26/26 | Protected persistent high-water pin, restart, rollback and fork refusal under stated assumptions |
| **Total** | **123/123** | Behavioral evidence, not a mathematical or production assurance certificate |

Observed warnings: DARM Guard's `BrokerConfig.load` reported two unclosed file handles (`config.json` and `registry.txt`). The test harness's kernel-subprocess cleanup warning was separately corrected. The remaining file-handle warnings did not fail the tests. They should be fixed in a separate Guard maintenance change, not silently mixed into this research freeze.

The file `EXPERIMENT_RESULTS.json` is the **original nine-case synthetic baseline**: 9/9 matched predicted outcomes, 3 supported and 6 unsupported cases, 0 observed false admissions/refusals in that small fixture set. **It is not a 123-test run report.** Keep the file but do not relabel its metrics or imply they cover the later bridge stages.

## 4. Known counterexamples and negative controls

1. A valid Guard attestation cannot alone grant missing source or target semantic warrants.
2. A valid local write attestation cannot prove remote acceptance, financial advice validity, or outside-world truth.
3. A previously signed artifact is not current if a later trusted audit snapshot records a different successful write or deletion at the target.
4. An authentic *older* audit snapshot can still satisfy historical checks if no newer external checkpoint/pin is supplied. This was deliberately exhibited in the live-broker experiment.
5. An authentic older witness cannot lower a *protected* stored high-water pin, but an attacker able to roll back or rewrite all trusted pin storage is outside the demonstrated boundary.
6. Different signed histories with incompatible heads are rejected relative to the enrolled genesis and verified prefix, even if a competing branch has a larger event count.
7. Neither a local witness key nor a locally stored checkpoint constitutes an independently operated external witness service.

## 5. Trust and threat assumptions

- The verifier executes untampered Python source and uses the intended version of `cryptography` and DARM Guard dependencies.
- Guard's cryptographic private signing key, public-key trust configuration and witness signing key are appropriately protected and **logically distinct**; the demonstration uses generated keys, not production trust anchors.
- Source- and target-level HDB evidence uses **synthetic test fixtures**. The policy, issuer permissions, mapping, claim requirements and any external receipts must come from a separately trusted principal or configuration channel.
- The provided audit snapshot must be checked against trusted, authenticated checkpoints. To claim currency beyond the snapshot's extent, the verifier must obtain and retain a new independently delivered freshness witness.
- The persisted pin must resist unauthorized rewriting, symlink/path replacement, lost-update races and **rollback of trusted state itself**. The prototype tests some local hazards but assumes its storage cannot be arbitrarily restored by a privileged adversary.
- Compromise of an issuer's private key, its measurement/observation process, the broker's isolation boundary, the external checkpoint service, the target consumer or a privileged host may invalidate broader claims. These are not discharged by a passing test suite.
- Complete mediation and execution-to-formal-model correspondence are *not* proved by these experiments.

## 6. Reproduction commands

Prerequisites: Linux/WSL, `~/darm-monitor`, `~/darm-guard` at the revisions noted above, installed runnable DARM kernel, user xattrs on `/tmp`, `cryptography>=42,<47`, and the six test modules listed above.

```bash
cd ~/darm-monitor/experiments/hdb1e_e37_nonlaundering
PYTHONPATH="$HOME/darm-guard:." python3 -m unittest -q \
  tests test_guard_bridge test_guard_audit_bridge \
  test_live_guard_broker test_guard_witness_bridge test_guard_monotonic_bridge
python3 mutation_gate.py
python3 run_experiment.py
```

The full Lean repository gate can be reproduced separately:

```bash
cd ~/darm-monitor
LEAN_NUM_THREADS=1 bash scripts/gate.sh
```

The experiment has not yet been given an immutable archived run log or signed release manifest. The counts above are reported from the terminal output, not independently re-executed during documentation authoring. Record exact environment versions, artifact hashes and new run output before external publication.

## 7. Mutation gate: bounded interpretation

The original `mutation_gate.py` defines **nine** targeted edits to `verifier.py`. In the prior run, eight were detected through an erroneous admission and **one through an uncaught exception** after removal of an unknown-target-claim check. The script treats both outcomes as a caught mutation. This is a *mutation-detection result*, **not** evidence that a mutated verifier continues to fail closed or return a safe refusal. This gate also does not exercise the newly added audit, witness, monotonic, or live-broker code unless separately extended.

Rerun the mutation gate at freeze time and record its exact printed reasons. Do not use a “9/9 fail-closed” claim.

## 8. Repository packaging and publication controls

At inventory, the experiment directory was untracked and contained 18 visible files including `test_live_guard_broker.py.bak` and `EXPERIMENT_RESULTS.json`. Do **not** indiscriminately `git add experiments/hdb1e_e37_nonlaundering/`. Exclude the `.bak` backup, `__pycache__`, `.pyc`, private keys, temporary runtime state and any unexpected fixture secrets; inspect the fixed fixture test keys and label them nonproduction.

Update the top of the experiment's existing `README.md` to state that it is a *historical baseline* whose integration sequence is now partially implemented, and point to this freeze. In particular, the README's statements that no privileged tool action is exercised and that the conditional proposition is "not yet proved in Lean" do **not** describe the complete expanded E38 experiment. Do not erase the earlier methodology; mark its scope and date.

Before external release: rerun the complete suites, archive the logs, verify dependency versions, inspect any generated data or credentials, check repository status, and review every file to be staged. Commit and push only after those checks.

## 9. Publication wording

> In a scoped, local research implementation, E38's conditional Lean model compiled and the DARM repository's full gate passed. A six-suite Python experiment reported 123 passing tests, including a genuine broker-mediated filesystem write, attestation and signed audit-log integration. The tests exhibited and detected evidence laundering across selected authority, semantic-warrant and freshness boundaries. They do not constitute a refinement proof or establish live freshness, complete mediation, compromised-host rollback resistance, issuer honesty, or external-world correctness.

## 10. Research and AI assistance disclosure

The core conceptual architecture and research direction of this work originated with the author. AI systems were used as technical assistants for formalization, coding, proof-checking, error discovery, literature exploration, and editorial refinement. The author directed the process, selected and revised the outputs, and remains responsible for the final claims, limitations, originality, and presentation of the work.
