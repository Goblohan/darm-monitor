# HDB-1E × E37: Heterogeneous Warrant Non-Laundering, prototype v0.1

## E38 integration status (2026-10-09)

This directory now contains the original HDB-1E x E37 prototype
and the subsequent E38 experimental integration with DARM Guard.

Verified development baseline:
- DARM Core: 7f8661f, research/e38-nonlaundering
- DARM Guard: 8e4a045, hardening/agent-socket-readonly
- Full GRBS repository gate: PASSED (9,014 build jobs)
- Python regression: 123/123 tests passed
- Mutation gate: 9/9 detected, comprising eight false admissions
  and one uncaught KeyError in deliberately mutated code

Experimental coverage:
- Signed source/target reliance evidence
- Actual DARM Guard v2 attestation verification
- Signed audit-snapshot verification
- Disposable live broker execution
- Independently signed checkpoint witnesses
- Persistent monotonic witness state under protected-storage assumptions

Limitations:
- EXPERIMENT_RESULTS.json records only the original nine mock cases.
- Independent production witness infrastructure is not implemented.
- Protected local state is vulnerable to sufficiently privileged rollback.
- Real-world semantic truth and complete downstream mediation remain assumptions.
- The Python implementation is tested, not formally proved equivalent
  to the E38 Lean model.
- Existing ResourceWarnings in DARM Guard configuration loading remain.

See EVIDENCE_FREEZE_v0.1.md for the consolidated research record.

---

**Purpose:** Test whether a *downstream reliance gate* refuses target claims that are not justified by authenticated, appropriately scoped and context-bound evidence, even where the original tool action was authorized and the source/target use different claim vocabularies.

This is a standalone Python research experiment. It **does not modify either DARM repository**, execute any privileged tool action, prove an external system safe, or claim end-to-end equivalence with DARM Guard or E37's Lean model.

## Exact research question

> Does a completely mediated target reliance gate refuse unsupported confidence transfer when an adversary can supply convincing labels, authentic-but-irrelevant receipts, and different representation vocabularies?

The prototype checks a *declared, trusted target policy* instead of accepting the agent's statement of which warrants are needed.

### Two independent decisions

- `action_authorized` records an *external* Boolean fact for the mock scenario; it does not imply the target claim is warranted and **is not verified by this program**.
- `reliance=ADMIT` is calculated from signed evidence, trusted mappings, exact artifact/request/policy/target bindings, validity interval and target obligations. It means **justified relative to the supplied trusted policy and model**, not certified truth of the report's contents.

## Architecture

```text
source validation.v1        representation mapping       target decision.v2
  signed evidence       -->  trusted mapping policy  --> reliance verdict
       |                    (not agent-supplied)             |
  claim scope           -->  target claim obligations --> ADMIT / REFUSE
  subject/request/time       newly introduced delta        + reasons
```

The `Policy` chooses:

1. A trustworthy *target claim ID* and its required propositions (`claim_requirements`). This is not supplied by the agent.
2. A *heterogeneous mapping* that links target propositions to all required source or target predicates.
3. Any *new obligations* introduced at the target boundary.
4. Allowed issuers, Ed25519 public keys, claim authority, schema and trust boundary.

The verifier rejects evidence if a signature fails, an issuer exceeds its registered claim authority, a receipt is stale, or any request/subject/audience/policy identity does not match. A genuinely signed remote receipt can support a target-level remote acknowledgement, but source-side `json_shape` validation cannot substitute for it.

## Run

Python 3.10+ and `cryptography>=42` required. Test fixture keys are fixed and **must never be deployed**.

```bash
python -m pip install 'cryptography>=42,<47'
python -m unittest -v tests
python mutation_gate.py
python run_experiment.py
```

`run_experiment.py` produces `EXPERIMENT_RESULTS.json`. The two comparison metrics are false admissions among unsupported mock claims and false refusals among supported mock claims. These are **sample statistics for synthetic cases**, not performance guarantees.

## HDB-1E baseline and new attacks

The original `HDB_1E.md` includes four cases A–D, which evaluate whether the required target warrant is a subset of the source scope. We retain those distinctions, then add controls for:

- valid signature but wrong artifact, request or audience
- signed evidence outside its lifetime or against a different policy
- issuer asserting a claim outside its registered authority
- mapped vocabulary changing without a trusted mapping identity
- target claim that adds semantics not represented by any valid source warrant
- remote state asserted without a separate trusted target receipt
- the source action being authorized while target reliance must be refused
- a malicious attempt to shrink the target contract's required warrants
- false refusal for evidence that is valid even without a reassuring natural-language label

`mutation_gate.py` disables 9 load-bearing protections individually. Eight produce erroneous admissions under the targeted case; the ninth surfaces an uncaught claim-lookup exception if the unknown-claim guard is removed. The gate treats both as detectable failures. It is **not** a proof of complete adversarial coverage.

## Conditional safety proposition (not yet proved in Lean)

Let `C` be a claim ID assigned by a trusted target policy, `E` be signed evidence, `M` be a trusted heterogeneous mapping, and `Delta` be target-introduced obligations.

```
Admit(C,E,M,Delta)
  -> all Required(C) and Delta are discharged by
     authentic, fresh, identity-bound evidence
     interpreted only under permitted issuer claims and trusted mapping rules.
```

This is a claim about the verifier's model and implementation, **not about the truth of every external-world assertion**. A signer's honesty, actual-world observation coverage, truthful semantic mapping, correct key ownership, uncompromised runtime and complete mediation of the target consumer are assumptions, not results.

### What this prototype cannot establish

- It does not establish that the principal really authorized the mocked action. DARM Guard should supply that independently.
- It does not verify the originator actually checked the data it claims to have checked.
- It does not cryptographically certify the mapping policy. The mapping and public keys are trusted local configuration.
- It does not prove a real downstream system honors `REFUSE` or that all effects are mediated.
- It does not establish production replay prevention. `request_id` binding only stops reuse for a *different* request ID.
- The source and target signatures authenticate receipt assertions, not external-world truth. Even a correct source signature could be based on a dishonest issuer or a faulty observation mechanism.
- The JSON signing format is a local deterministic fixture. Do not treat it as a generic interoperable canonicalization standard.
- No formal refinement connects this Python implementation to E37's Lean semantics yet.

## Integration sequence

1. Integrate a named, canonical DARM Guard attestation adapter **after confirming its actual signed schema and trust conditions**.
2. Define E37 mapping semantics for specific source/target domain pairs and formalize a reliance-gate soundness theorem with distinct `Asserted`, `Entitled`, and `WorldTrue` predicates.
3. Build a separately trusted receiving verifier and mandate refusal at the consumption point, with a target-owned `claim_requirements` policy.
4. Run adversarial end-to-end tests, including compromised receipt producers, semantic collisions, intermediate rewriting, policy rotation, replays and incomplete mediation.
5. Label each verified property as proved, tested, or assumed. Do not expand the result to an untested production boundary.

## Upstream research

- DARM Core: https://github.com/Goblohan/darm-monitor
- DARM Guard: https://github.com/Goblohan/Darm-Guard
- HDB-1E baseline: https://github.com/Goblohan/darm-monitor/blob/d1af704/HDB_1E.md
- Heterogeneous warrant calculus: https://github.com/Goblohan/darm-monitor/blob/research/e37-heterogeneous-warrant/GRBS/E37HeterogeneousWarrant.lean
