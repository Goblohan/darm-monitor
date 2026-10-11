# E38 Stage 2: Native DARM Guard v2 evidence bridge

**Scope:** verifies an existing DARM Guard `user.darm` v2 signature over `darm-attest-v2|rid|target|digest`, content bytes read from the same file descriptor as the attestation, the internally consistent broker audit log, its latest effect for the logical target, and a v1 Ed25519-signed `darm-checkpoint-v1` checkpoint covering the **entire inspected audit snapshot**.

**Only admitted claim:** `broker_attested_file_content_at_observation`. An admission means the inspected bytes match the attributed signed file and the anchored audit snapshot, **under independently trusted key-ring and checkpoint provenance**. It is not authority for the content's truth, validity, confidentiality, downstream use, or current real-world state beyond that observed read. A whole log and checkpoint can be replayed if there is no independent freshness guarantee. The adapter does not currently verify policy-version or audience binding because Guard v2 attestations contain neither. It does not establish non-bypassable reliance enforcement. The `admitted_implies_warranted` Lean theorem does not prove this Python adapter.

**Current model-to-code status:** tested, not proved. The synthetic suite uses native Guard v2 wire-format fixtures. An additional interoperability script uses your actual local `darm_guard.attest.KeyRing` implementation, still without a running broker. No changes are made to DARM Guard.

## Install into E38 prototype (non-overwriting)

The ZIP contains this directory under `e38_guard_v2_bridge_stage2/`. On WSL, after downloading the ZIP to Windows Downloads, copy its contents into a **new** `experiments/e38_guard_v2_bridge_stage2/` subdirectory. Do not overwrite the existing E38 Lean source or HDB-1E experiment. The archive contains no executable installer and performs no Git operations.

```
cd ~/darm-monitor/experiments/e38_guard_v2_bridge_stage2
python3 -m unittest -v test_guard_v2_bridge.py
python3 test_against_guard.py
```

## Optional read-only check against a real broker workspace

A runnable broker integration requires independently available artifacts:

- principal-trusted `audit.jsonl.pub.json` (Guard's public-key ring)
- `audit.jsonl` produced by the broker
- an externally preserved `<genesis>.checkpoints.jsonl` published by Guard
- the physical workspace directory, logical target and externally identified expected request ID

```
python3 guard_v2_bridge.py \
  --workspace /path/to/broker/workspace \
  --target /workspace/reports/report.txt \
  --rid <trusted-request-id> \
  --audit /path/to/audit.jsonl \
  --public-ring /path/to/audit.jsonl.pub.json \
  --checkpoints /outside-broker-control/abcd.checkpoints.jsonl
```

This emits a JSON decision and returns exit code 0 only for the narrow admitted claim. No broker writes or effectful operations are performed.

**Fail-closed by design:** if Guard checkpoint publishing is not configured, the adapter refuses to admit the evidence, even if the file signature and local audit hash chain verify. This does not imply the file is malicious. It means an independently anchored audit snapshot is missing.

## Deliberate exclusions

A valid Ed25519 signature authenticates only the signed message, conditional on the provenance and protection of the trusted keys. A signed checkpoint anchors a *snapshot* but does not prove that snapshot is the latest possible one. The adapter does not independently establish physical workspace confinement, operational complete mediation, Guard's kernel authorization, intent correctness, policy-version consistency or target-system truth. All must remain separate obligations. It does not transform Guard signatures into the HDB-1E custom envelope or mint fictitious warrants.
