"""Stage 5: persisted trusted high-water pin with adversarial rollback tests."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import tempfile
import threading
import unittest

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from darm_guard.attest import KeyRing
from fixtures import NOW, POLICY, make_request
from guard_bridge import TrustedArtifact
from guard_witness_bridge import WITNESS_DOMAIN, _canonical
from guard_monotonic_bridge import MonotonicWitnessStore
from test_guard_audit_bridge import chain, _jsonl

RID = "req-0001"
TARGET = "/workspace/reports/benign_report.txt"
CONTENT = b"benign report v1"
DIGEST = hashlib.sha256(CONTENT).hexdigest()


class MonotonicWitnessStoreTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="e38-pin-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.key = KeyRing.generate()
        self.public = self.key.public_only()
        self.witness_private = Ed25519PrivateKey.generate()
        self.witness_public = self.witness_private.public_key()
        self.store = self.new_store()
        self.trusted = TrustedArtifact(RID, TARGET)
        self.att = self.key.sign(RID, TARGET, DIGEST)
        prep = {
            "event": "prepared", "request_id": RID, "tool": "write_file",
            "target": TARGET, "decision": "admit", "effect": None,
            "invocation_hash": "a" * 64, "intended_state": ["present", DIGEST],
        }
        out = {
            "event": "outcome", "request_id": RID, "tool": "write_file",
            "target": TARGET, "decision": "admit", "effect": "succeeded",
            "executed": True, "reconciliation": "confirmedSuccess",
            "invocation_hash": "a" * 64, "intended_state": ["present", DIGEST],
            "observed_state": ["present", DIGEST],
        }
        self.rows1 = chain([prep, out])
        self.rows2 = chain([prep, out, {"event": "start", "audit_note": "unrelated append"}])
        self.cp1 = self.cp(self.rows1)
        self.cp2 = self.cp(self.rows2)
        self.audit1, self.cps1 = _jsonl(self.rows1), _jsonl([self.cp1])
        self.audit2, self.cps2 = _jsonl(self.rows2), _jsonl([self.cp1, self.cp2])
        self.w1, self.w2 = self.witness(self.cp1), self.witness(self.cp2)

    def new_store(self, *, witness_public=None):
        return MonotonicWitnessStore(self.root,
            self.witness_public if witness_public is None else witness_public, self.public)

    def cp(self, rows):
        return self.key.sign_checkpoint(rows[0]["entry_hash"], len(rows), rows[-1]["entry_hash"])

    def witness(self, cp, *, signer=None):
        body = {"v": 1, "checkpoint": cp}
        signature = (self.witness_private if signer is None else signer).sign(
            WITNESS_DOMAIN + _canonical(body)).hex()
        return json.dumps({**body, "signature": signature}, sort_keys=True).encode()

    def enroll(self):
        r = self.store.advance(self.audit1, self.cps1, self.w1, enroll=True)
        self.assertEqual((r.ok, r.reason, r.count), (True, "enrolled", len(self.rows1)), r)

    def advance2(self):
        return self.store.advance(self.audit2, self.cps2, self.w2)

    def decide(self, *, store=None, audit=None, cps=None, request=None):
        return (self.store if store is None else store).decide(
            make_request(claim_id="document_integrity") if request is None else request,
            POLICY, NOW, self.att, CONTENT, self.trusted,
            self.audit1 if audit is None else audit,
            self.cps1 if cps is None else cps)

    def test_default_refuses_without_enrollment(self):
        self.assertEqual(self.store.observe().reason, "not-enrolled")
        self.assertEqual(self.store.advance(self.audit1, self.cps1, self.w1).reason, "enrollment-required")
        self.assertFalse(self.decide().admit)

    def test_explicit_enrollment_and_reliance(self):
        self.enroll()
        self.assertTrue(self.decide().admit)

    def test_pin_persists_across_new_verifier_object(self):
        self.enroll()
        fresh_instance = self.new_store()
        self.assertTrue(self.decide(store=fresh_instance).admit)
        self.assertEqual(fresh_instance.observe().count, len(self.rows1))

    def test_newer_signed_witness_advances_store(self):
        self.enroll()
        self.assertEqual(self.advance2().reason, "advanced")
        self.assertEqual(self.store.observe().count, len(self.rows2))
        self.assertTrue(self.decide(audit=self.audit2, cps=self.cps2).admit)

    def test_old_signed_witness_cannot_lower_pin(self):
        self.enroll()
        self.assertTrue(self.advance2().ok)
        r = self.store.advance(self.audit1, self.cps1, self.w1)
        self.assertEqual(r.reason, "rollback-below-pinned-count")
        self.assertEqual(self.store.observe().count, len(self.rows2))

    def test_old_snapshot_refused_after_newer_pin(self):
        self.enroll()
        self.assertTrue(self.advance2().ok)
        v = self.decide()
        self.assertFalse(v.admit)
        self.assertIn("witness:audit-behind-trusted-witness", v.reasons)

    def test_repeated_equal_pin_does_not_replace_state(self):
        self.enroll()
        before = self.store.state.read_bytes()
        r = self.store.advance(self.audit1, self.cps1, self.w1)
        self.assertEqual(r.reason, "unchanged")
        self.assertEqual(self.store.state.read_bytes(), before)

    def test_enroll_does_not_reset_existing_pin(self):
        self.enroll()
        self.assertTrue(self.advance2().ok)
        r = self.store.advance(self.audit1, self.cps1, self.w1, enroll=True)
        self.assertFalse(r.ok)
        self.assertEqual(r.reason, "rollback-below-pinned-count")

    @staticmethod
    def body(row):
        return {k: v for k, v in row.items() if k not in ("prev_hash", "entry_hash")}

    def test_fork_same_count_rejected(self):
        self.enroll()
        fork = chain([self.body(self.rows1[0]), {**self.body(self.rows1[1]), "extra": "fork"}])
        cp = self.cp(fork)
        r = self.store.advance(_jsonl(fork), _jsonl([cp]), self.witness(cp))
        self.assertEqual(r.reason, "fork-does-not-extend-stored-pin")

    def test_fork_higher_count_rejected(self):
        self.enroll()
        fork = chain([self.body(self.rows1[0]), {**self.body(self.rows1[1]), "extra": "fork"}, {"event": "start"}])
        cp = self.cp(fork)
        r = self.store.advance(_jsonl(fork), _jsonl([cp]), self.witness(cp))
        self.assertEqual(r.reason, "fork-does-not-extend-stored-pin")

    def test_different_genesis_rejected(self):
        self.enroll()
        fork = chain([{**self.body(self.rows1[0]), "extra": "fork"}, self.body(self.rows1[1]), {"event": "start"}])
        cp = self.cp(fork)
        r = self.store.advance(_jsonl(fork), _jsonl([cp]), self.witness(cp))
        self.assertEqual(r.reason, "different-genesis")

    def test_forged_witness_rejected_and_state_unchanged(self):
        self.enroll()
        bad = self.witness(self.cp2, signer=Ed25519PrivateKey.generate())
        r = self.store.advance(self.audit2, self.cps2, bad)
        self.assertIn("witness-signature-invalid", r.reason)
        self.assertEqual(self.store.observe().count, 2)

    def test_checkpoint_signature_forgery_rejected(self):
        self.enroll()
        fake = dict(self.cp2, sig="0" * 128)
        r = self.store.advance(self.audit2, _jsonl([fake]), self.witness(fake))
        self.assertFalse(r.ok)
        self.assertEqual(self.store.observe().count, 2)

    def test_modified_log_rejected(self):
        self.enroll()
        rows = [dict(x) for x in self.rows2]
        rows[2]["event"] = "tamper"
        r = self.store.advance(_jsonl(rows), self.cps2, self.w2)
        self.assertIn(r.reason, ("broken-log-hash", "broken-log-chain"))

    def test_off_branch_signed_checkpoint_refused(self):
        self.enroll()
        forged_branch = chain([self.body(self.rows1[0]), {**self.body(self.rows1[1]), "extra": "alternate"}])
        bad_cp = self.cp(forged_branch)
        r = self.store.advance(self.audit2, _jsonl([self.cp1, bad_cp, self.cp2]), self.w2)
        self.assertEqual(r.reason, "checkpoint-off-audit-history")

    def test_missing_checkpoint_refused(self):
        self.enroll()
        r = self.store.advance(self.audit2, _jsonl([self.cp1]), self.w2)
        self.assertEqual(r.reason, "missing-full-snapshot-checkpoint")

    def test_missing_trusted_state_fails_closed(self):
        self.enroll()
        os.unlink(self.store.state)
        self.assertEqual(self.store.observe().reason, "not-enrolled")
        self.assertFalse(self.decide().admit)
        # Note: an operator with write access to this trusted directory can
        # start explicit reenrollment; this is outside the local assurance.

    def test_corrupt_state_refuses_without_reset(self):
        self.enroll()
        self.store.state.write_bytes(b'{"invalid":true}')
        self.assertEqual(self.store.observe().reason, "invalid-state-schema")
        r = self.store.advance(self.audit2, self.cps2, self.w2, enroll=True)
        self.assertEqual(r.reason, "invalid-state-schema")

    def test_modified_stored_witness_detected(self):
        self.enroll()
        obj = json.loads(self.store.state.read_bytes())
        raw = json.loads(__import__("base64").b64decode(obj["witness_b64"]))
        raw["signature"] = "0" * 128
        obj["witness_b64"] = __import__("base64").b64encode(json.dumps(raw).encode()).decode()
        self.store.state.write_text(json.dumps(obj))
        self.assertFalse(self.store.observe().ok)
        self.assertFalse(self.decide().admit)

    def test_wrong_pinned_witness_public_key_refused(self):
        self.enroll()
        other_store = self.new_store(witness_public=Ed25519PrivateKey.generate().public_key())
        self.assertFalse(other_store.observe().ok)
        self.assertFalse(self.decide(store=other_store).admit)

    def test_state_directory_permissions_enforced(self):
        self.enroll()
        os.chmod(self.root, 0o777)
        self.addCleanup(os.chmod, self.root, 0o700)
        self.assertEqual(self.store.observe().reason, "untrusted-state-directory")

    def test_state_file_symlink_refused(self):
        self.enroll()
        other = self.root / "other.json"
        other.write_bytes(self.store.state.read_bytes())
        os.unlink(self.store.state)
        os.symlink(other, self.store.state)
        self.assertFalse(self.store.observe().ok)

    def test_two_threads_cannot_move_pin_backwards(self):
        self.enroll()
        start = threading.Barrier(3)
        results = []
        def advance(a, c, w):
            start.wait()
            results.append(self.new_store().advance(a, c, w))
        a = threading.Thread(target=advance, args=(self.audit2, self.cps2, self.w2))
        b = threading.Thread(target=advance, args=(self.audit1, self.cps1, self.w1))
        a.start(); b.start(); start.wait()
        a.join(timeout=5); b.join(timeout=5)
        self.assertFalse(a.is_alive() or b.is_alive())
        self.assertEqual(len(results), 2)
        self.assertEqual(self.store.observe().count, 3)

    def test_pin_does_not_supply_semantic_warrant(self):
        self.enroll()
        request = make_request(claim_id="financial_advice_verified")
        self.assertFalse(self.decide(request=request).admit)

    def test_pin_does_not_prove_remote_acceptance(self):
        self.enroll()
        self.assertFalse(self.decide(request=make_request(claim_id="remote_acceptance_confirmed")).admit)

    def test_same_host_local_store_is_not_independent_service(self):
        self.enroll()
        old_state = self.store.state.read_bytes()
        self.assertTrue(self.advance2().ok)
        # Deliberate expected counterexample: a privileged adversary who can
        # roll back the trusted state file can evade the monotonic high-water
        # mark. Stage 5 cannot protect against this.
        self.store.state.write_bytes(old_state)
        self.assertTrue(self.decide().admit)


if __name__ == "__main__":
    unittest.main(verbosity=2)
