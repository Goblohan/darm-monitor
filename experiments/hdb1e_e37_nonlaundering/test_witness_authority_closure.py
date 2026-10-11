"""Security regression tests for the additive E38 remote-witness experiment."""
from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from darm_guard.attest import KeyRing
from guard_witness_bridge import verify_trusted_witness
from witness_authority import WitnessAuthority, WitnessRefusal
from witness_exact_head import verify_online_exact_head


def bytes_json(obj):
    return json.dumps(obj, sort_keys=True).encode()


def row(event, prev):
    body = dict(event, prev_hash=prev, ts="2026-10-10T00:00:00")
    return dict(body, entry_hash=hashlib.sha256(json.dumps(body, sort_keys=True).encode()).hexdigest())


class IndependentAuthorityTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.broker = KeyRing.generate()
        self.public = self.broker.public_only()
        self.signer = Ed25519PrivateKey.generate()
        self.authority = WitnessAuthority(self.root, self.signer, self.public)
        self.row1 = row({"event": "prepared", "request_id": "r1"}, "0" * 64)
        self.row2 = row({"event": "outcome", "request_id": "r1"}, self.row1["entry_hash"])
        self.cp1 = self.broker.sign_checkpoint(self.row1["entry_hash"], 1, self.row1["entry_hash"])
        self.cp2 = self.broker.sign_checkpoint(self.row1["entry_hash"], 2, self.row2["entry_hash"])

    def append(self, cp, entries, enroll=False):
        return self.authority.append(bytes_json({"checkpoint": cp, "entries": entries}), enroll=enroll)

    def test_enrollment_is_explicit_and_signed(self):
        with self.assertRaisesRegex(WitnessRefusal, "enrollment-required"):
            self.append(self.cp1, [self.row1])
        receipt = self.append(self.cp1, [self.row1], enroll=True)
        self.assertTrue(verify_trusted_witness(receipt, self.signer.public_key(), self.public).verified)

    def test_live_nonce_and_exact_head(self):
        self.append(self.cp1, [self.row1], enroll=True)
        nonce = "1" * 64
        live = self.authority.challenge(bytes_json({"nonce": nonce}))
        self.assertTrue(verify_online_exact_head(live, nonce, bytes_json(self.row1) + b"\n",
            self.signer.public_key(), self.public))
        self.assertFalse(verify_online_exact_head(live, "2" * 64, bytes_json(self.row1) + b"\n",
            self.signer.public_key(), self.public))
        self.assertFalse(verify_online_exact_head(live, nonce, bytes_json(self.row1) + b"\n" +
            bytes_json(self.row2) + b"\n", self.signer.public_key(), self.public))

    def test_nonacknowledged_extension_is_not_current(self):
        self.append(self.cp1, [self.row1], enroll=True)
        live = self.authority.challenge(bytes_json({"nonce": "a" * 64}))
        audit2 = bytes_json(self.row1) + b"\n" + bytes_json(self.row2) + b"\n"
        self.assertFalse(verify_online_exact_head(live, "a" * 64, audit2,
            self.signer.public_key(), self.public))
        self.append(self.cp2, [self.row2])
        live2 = self.authority.challenge(bytes_json({"nonce": "b" * 64}))
        self.assertTrue(verify_online_exact_head(live2, "b" * 64, audit2,
            self.signer.public_key(), self.public))

    def test_reject_fork_and_rollback(self):
        self.append(self.cp1, [self.row1], enroll=True)
        fork = row({"event": "outcome", "request_id": "fork"}, self.row1["entry_hash"])
        fork_cp = self.broker.sign_checkpoint(self.row1["entry_hash"], 2, fork["entry_hash"])
        self.append(self.cp2, [self.row2])
        with self.assertRaises(WitnessRefusal):
            self.append(fork_cp, [fork])
        with self.assertRaises(WitnessRefusal):
            self.append(self.cp1, [])

    def test_missing_or_modified_suffix_rejected(self):
        self.append(self.cp1, [self.row1], enroll=True)
        with self.assertRaises(WitnessRefusal):
            self.append(self.cp2, [])
        with self.assertRaises(WitnessRefusal):
            self.append(self.cp2, [dict(self.row2, event="altered")])
        with self.assertRaises(WitnessRefusal):
            self.append(self.cp2, [dict(self.row2, prev_hash="0" * 64)])

    def test_invalid_guard_signature_rejected(self):
        forged = dict(self.cp1, sig="0" * 128)
        with self.assertRaises(WitnessRefusal):
            self.append(forged, [self.row1], enroll=True)

    def test_idempotence_and_durable_reload(self):
        r1 = self.append(self.cp1, [self.row1], enroll=True)
        self.assertEqual(r1, self.append(self.cp1, []))
        reloaded = WitnessAuthority(self.root, self.signer, self.public)
        self.assertEqual(json.loads(reloaded.challenge(bytes_json({"nonce": "f" * 64})))["nonce"], "f" * 64)
        self.assertEqual(json.loads(reloaded.append(bytes_json({"checkpoint": self.cp1, "entries": []}))), json.loads(r1))

    def test_corrupted_state_refuses(self):
        self.append(self.cp1, [self.row1], enroll=True)
        self.authority.path.write_text("{}")
        with self.assertRaises(WitnessRefusal):
            self.authority.challenge(bytes_json({"nonce": "3" * 64}))

    def test_reject_same_witness_and_guard_signing_identity(self):
        shared = KeyRing(self.signer)
        with self.assertRaisesRegex(WitnessRefusal, "key-role-overlap"):
            WitnessAuthority(self.root, self.signer, shared.public_only())

    def test_replay_challenge_does_not_verify_other_nonce(self):
        self.append(self.cp1, [self.row1], enroll=True)
        old = self.authority.challenge(bytes_json({"nonce": "4" * 64}))
        self.assertFalse(verify_online_exact_head(old, "5" * 64, bytes_json(self.row1) + b"\n",
            self.signer.public_key(), self.public))

    def test_reenrollment_refused(self):
        self.append(self.cp1, [self.row1], enroll=True)
        with self.assertRaisesRegex(WitnessRefusal, "already-enrolled"):
            self.append(self.cp1, [self.row1], enroll=True)


if __name__ == "__main__":
    unittest.main()
