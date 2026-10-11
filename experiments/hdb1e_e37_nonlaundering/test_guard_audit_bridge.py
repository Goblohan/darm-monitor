"""E38 signed-snapshot test suite. Run with real Guard module on PYTHONPATH."""
from __future__ import annotations

import copy
import hashlib
import json
import unittest

from darm_guard.attest import KeyRing
from fixtures import NOW, POLICY, make_request
from guard_bridge import TrustedArtifact
from guard_audit_bridge import decide_with_guard_audit, verify_snapshot

CONTENT = b"benign report v1"
TARGET = "/workspace/reports/benign_report.txt"
RID = "req-0001"


def _jsonl(entries):
    return ("\n".join(json.dumps(e, sort_keys=True) for e in entries) + "\n").encode()


def chain(entries):
    prev = "0" * 64
    rows = []
    for source in entries:
        e = dict(source, prev_hash=prev)
        digest = hashlib.sha256(json.dumps(e, sort_keys=True).encode()).hexdigest()
        e["entry_hash"] = digest
        rows.append(e)
        prev = digest
    return rows


class SignedSnapshotTests(unittest.TestCase):
    def setUp(self):
        self.signer = KeyRing.generate()
        self.public = self.signer.public_only()
        self.trusted = TrustedArtifact(RID, TARGET)
        self.digest = hashlib.sha256(CONTENT).hexdigest()
        self.att = self.signer.sign(RID, TARGET, self.digest)
        self.invhash = "a" * 64
        self.prepared = {
            "event": "prepared", "request_id": RID, "tool": "write_file",
            "target": TARGET, "decision": "admit", "effect": None,
            "invocation_hash": self.invhash,
            "intended_state": ["present", self.digest],
        }
        self.outcome = {
            "event": "outcome", "request_id": RID, "tool": "write_file",
            "target": TARGET, "decision": "admit", "effect": "succeeded",
            "executed": True, "reconciliation": "confirmedSuccess",
            "invocation_hash": self.invhash,
            "intended_state": ["present", self.digest],
            "observed_state": ["present", self.digest],
        }
        self.events = [self.prepared, self.outcome]

    def snapshot(self, entries=None, checkpoint_count=None, cp_mutation=None):
        rows = chain(entries if entries is not None else self.events)
        count = len(rows) if checkpoint_count is None else checkpoint_count
        cp = self.signer.sign_checkpoint(rows[0]["entry_hash"], count, rows[count-1]["entry_hash"])
        if cp_mutation is not None:
            cp = cp_mutation(cp)
        return _jsonl(rows), _jsonl([cp])

    def audit(self, entries=None, *, audit=None, checkpoints=None):
        if audit is None and checkpoints is None:
            audit, checkpoints = self.snapshot(entries)
        return verify_snapshot(audit, checkpoints, self.public, self.trusted, self.digest)

    def decision(self, entries=None, *, audit=None, checkpoints=None, request=None):
        if audit is None and checkpoints is None:
            audit, checkpoints = self.snapshot(entries)
        return decide_with_guard_audit(
            make_request() if request is None else request, POLICY, NOW,
            self.att, CONTENT, self.trusted, self.public, audit, checkpoints
        )

    def test_real_guard_auditlog_append_format(self):
        # In the user's WSL checkout, this imports the actual DARM Guard
        # AuditLog. The offline smoke-test stub lacks that runtime module.
        try:
            from darm_guard.broker import AuditLog
        except ModuleNotFoundError:
            self.skipTest("full DARM Guard broker not present in offline fixture")
        from pathlib import Path
        from tempfile import TemporaryDirectory
        with TemporaryDirectory() as d:
            log_file = Path(d) / "audit.jsonl"
            logger = AuditLog(str(log_file))
            logger.append(dict(self.prepared))
            logger.append(dict(self.outcome))
            raw = log_file.read_bytes()
            rows = [json.loads(line) for line in raw.splitlines()]
            cp = self.signer.sign_checkpoint(rows[0]["entry_hash"], len(rows), rows[-1]["entry_hash"])
            verdict = self.audit(audit=raw, checkpoints=_jsonl([cp]))
            self.assertTrue(verdict.verified, verdict.reason)

    def test_admits_valid_write_in_full_signed_snapshot(self):
        self.assertTrue(self.audit().verified)
        self.assertTrue(self.decision().admit)

    def test_allows_unrelated_later_operation_with_full_checkpoint(self):
        other = dict(self.outcome, request_id="req-other",
                     target="/workspace/reports/other.txt")
        self.assertTrue(self.audit(self.events + [other]).verified)
        self.assertTrue(self.decision(self.events + [other]).admit)

    def test_rejects_genuine_signature_without_any_checkpoint(self):
        log, _ = self.snapshot()
        self.assertEqual(self.audit(audit=log, checkpoints=b"").reason,
                         "malformed-audit-or-checkpoint")

    def test_rejects_audit_tail_not_externally_checkpointed(self):
        log, cp = self.snapshot(checkpoint_count=1)
        self.assertEqual(self.audit(audit=log, checkpoints=cp).reason,
                         "no-full-snapshot-checkpoint")

    def test_rejects_wrong_checkpoint_signature(self):
        log, cp = self.snapshot(cp_mutation=lambda c: dict(c, head="f"*64))
        self.assertEqual(self.audit(audit=log, checkpoints=cp).reason,
                         "checkpoint-signature-invalid")

    def test_rejects_changed_audit_record_even_with_original_checkpoint(self):
        log, cp = self.snapshot()
        records = [json.loads(x) for x in log.splitlines()]
        records[0]["decision"] = "reject"
        self.assertEqual(self.audit(audit=_jsonl(records), checkpoints=cp).reason,
                         "broken-audit-chain")

    def test_rejects_recomputed_chain_if_checkpoint_not_updated(self):
        log, cp = self.snapshot()
        records = [json.loads(x) for x in log.splitlines()]
        bodies = [{k:v for k,v in e.items() if k not in ("prev_hash", "entry_hash")}
                  for e in records]
        bodies[0]["decision"] = "reject"
        recalc = _jsonl(chain(bodies))
        self.assertEqual(self.audit(audit=recalc, checkpoints=cp).reason,
                         "checkpoint-off-audit-history")

    def test_rejects_truncated_log(self):
        log, cp = self.snapshot()
        shortened = log.splitlines()[0] + b"\n"
        self.assertEqual(self.audit(audit=shortened, checkpoints=cp).reason,
                         "invalid-checkpoint-schema")

    def test_rejects_missing_preparation(self):
        self.assertEqual(self.audit([self.outcome]).reason,
                         "missing-or-duplicate-preparation")

    def test_rejects_missing_outcome(self):
        self.assertEqual(self.audit([self.prepared]).reason,
                         "missing-or-duplicate-outcome")

    def test_rejects_prepared_without_kernel_admission_record(self):
        altered = dict(self.prepared, decision="reject")
        self.assertEqual(self.audit([altered, self.outcome]).reason,
                         "admission-or-intended-state-mismatch")

    def test_rejects_wrong_invocation_hash_in_outcome(self):
        altered = dict(self.outcome, invocation_hash="b"*64)
        self.assertEqual(self.audit([self.prepared, altered]).reason,
                         "effect-not-confirmed-or-not-matched")

    def test_rejects_effect_unknown(self):
        altered = dict(self.outcome, effect="unknown", executed=False,
                       reconciliation="unresolved")
        self.assertEqual(self.audit([self.prepared, altered]).reason,
                         "effect-not-confirmed-or-not-matched")

    def test_rejects_reconciliation_without_successful_effect(self):
        altered = dict(self.outcome, effect="failed", executed=False)
        self.assertEqual(self.audit([self.prepared, altered]).reason,
                         "effect-not-confirmed-or-not-matched")

    def test_rejects_successful_log_but_wrong_observed_digest(self):
        altered = dict(self.outcome, observed_state=["present", "b"*64])
        self.assertEqual(self.audit([self.prepared, altered]).reason,
                         "effect-not-confirmed-or-not-matched")

    def test_rejects_later_successful_write(self):
        later = dict(self.outcome, request_id="req-9999")
        self.assertEqual(self.audit(self.events + [later]).reason,
                         "later-operation-supersedes")

    def test_rejects_later_delete(self):
        later = dict(self.outcome, request_id="req-delete", tool="delete_file",
                     observed_state=["absent", None])
        self.assertEqual(self.audit(self.events + [later]).reason,
                         "later-operation-supersedes")

    def test_rejects_later_rename_from_target(self):
        later = dict(self.outcome, request_id="req-move", tool="rename_file",
                     target="/workspace/reports/destination.txt", source=TARGET)
        self.assertEqual(self.audit(self.events + [later]).reason,
                         "later-operation-supersedes")

    def test_rejects_later_pending_operation(self):
        later = dict(self.prepared, request_id="req-next")
        self.assertEqual(self.audit(self.events + [later]).reason,
                         "later-operation-possibly-supersedes")

    def test_rejects_semantic_claim_even_with_valid_full_snapshot(self):
        req = make_request(claim_id="financial_advice_verified")
        verdict = self.decision(request=req)
        self.assertFalse(verdict.admit)
        self.assertIn("undischarged-target-warrant", verdict.reasons)

    def test_rejects_unsupported_remote_state_despite_valid_local_write(self):
        req = make_request(claim_id="remote_acceptance_confirmed")
        self.assertFalse(self.decision(request=req).admit)

    def test_rejects_duplicate_json_fields(self):
        log, cp = self.snapshot()
        records = log.splitlines()
        records[0] = records[0][:-1] + b',"event":"prepared"}'
        self.assertEqual(self.audit(audit=b"\n".join(records)+b"\n", checkpoints=cp).reason,
                         "malformed-audit-or-checkpoint")

    def test_rejects_intentional_signature_tampering(self):
        obj = json.loads(self.att)
        obj["digest"] = "b"*64
        log, cp = self.snapshot()
        v = decide_with_guard_audit(make_request(), POLICY, NOW,
                                    json.dumps(obj).encode(), CONTENT,
                                    self.trusted, self.public, log, cp)
        self.assertFalse(v.admit)
        self.assertIn("guard:guard-signature-untrusted-or-invalid", v.reasons)


if __name__ == '__main__':
    unittest.main()
