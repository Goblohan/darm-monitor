"""E38 Stage 4 witness-pin tests, including explicit old-witness counterexample."""
from __future__ import annotations

import hashlib
import json
import unittest

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from darm_guard.attest import KeyRing
from fixtures import NOW, POLICY, make_request
from guard_bridge import TrustedArtifact
from guard_witness_bridge import (
    WITNESS_DOMAIN, _canonical, decide_with_witness,
    verify_trusted_witness, verify_extension,
)
from test_guard_audit_bridge import chain, _jsonl

RID = "req-0001"
TARGET = "/workspace/reports/benign_report.txt"
CONTENT = b"benign report v1"
DIGEST = hashlib.sha256(CONTENT).hexdigest()


class IndependentlyWitnessedRollbackTests(unittest.TestCase):
    def setUp(self):
        self.broker_key = KeyRing.generate()
        self.broker_public = self.broker_key.public_only()
        self.witness_private = Ed25519PrivateKey.generate()
        self.witness_public = self.witness_private.public_key()
        self.other_witness_public = Ed25519PrivateKey.generate().public_key()
        self.trusted = TrustedArtifact(RID, TARGET)
        self.att = self.broker_key.sign(RID, TARGET, DIGEST)
        self.prep = {
            "event": "prepared", "request_id": RID, "tool": "write_file",
            "target": TARGET, "decision": "admit", "effect": None,
            "invocation_hash": "a" * 64, "intended_state": ["present", DIGEST],
        }
        self.out = {
            "event": "outcome", "request_id": RID, "tool": "write_file",
            "target": TARGET, "decision": "admit", "effect": "succeeded",
            "executed": True, "reconciliation": "confirmedSuccess",
            "invocation_hash": "a" * 64, "intended_state": ["present", DIGEST],
            "observed_state": ["present", DIGEST],
        }
        self.rows1 = chain([self.prep, self.out])
        self.cp1 = self.broker_key.sign_checkpoint(
            self.rows1[0]["entry_hash"], len(self.rows1), self.rows1[-1]["entry_hash"]
        )
        self.audit1, self.cps1 = _jsonl(self.rows1), _jsonl([self.cp1])
        self.unrelated = dict(self.out, request_id="req-other", target="/workspace/reports/unrelated.txt")
        self.rows2 = chain([self.prep, self.out, self.unrelated])
        self.cp2 = self.broker_key.sign_checkpoint(
            self.rows2[0]["entry_hash"], len(self.rows2), self.rows2[-1]["entry_hash"]
        )
        self.audit2, self.cps2 = _jsonl(self.rows2), _jsonl([self.cp2])

    def witness(self, cp=None, *, signer=None):
        body = {"v": 1, "checkpoint": self.cp1 if cp is None else cp}
        sig = (self.witness_private if signer is None else signer).sign(
            WITNESS_DOMAIN + _canonical(body)
        ).hex()
        return json.dumps(dict(body, signature=sig), sort_keys=True).encode()

    def verdict(self, audit=None, cps=None, witness=None, request=None, public=None, ring=None):
        return decide_with_witness(
            make_request(claim_id="document_integrity") if request is None else request,
            POLICY, NOW, self.att, CONTENT, self.trusted,
            self.broker_public if ring is None else ring,
            self.audit1 if audit is None else audit,
            self.cps1 if cps is None else cps,
            self.witness() if witness is None else witness,
            self.witness_public if public is None else public,
        )

    def test_admit_matching_witness_and_signed_snapshot(self):
        self.assertTrue(self.verdict().admit)

    def test_admit_later_unrelated_append_extending_old_witness(self):
        self.assertTrue(self.verdict(self.audit2, self.cps2).admit)

    def test_reject_valid_old_snapshot_with_newer_trusted_witness(self):
        v = self.verdict(witness=self.witness(self.cp2))
        self.assertFalse(v.admit)
        self.assertIn("witness:audit-behind-trusted-witness", v.reasons)

    def test_accept_newer_snapshot_with_newer_trusted_witness(self):
        self.assertTrue(self.verdict(self.audit2, self.cps2, self.witness(self.cp2)).admit)

    def test_reject_same_length_conflicting_branch(self):
        alter = dict(self.out, independent_note="competing but internally valid history")
        forked = chain([self.prep, alter])
        cp = self.broker_key.sign_checkpoint(forked[0]["entry_hash"], len(forked), forked[-1]["entry_hash"])
        # Despite a correctly broker-signed different fork, the anchored pin
        # cannot be quietly rewritten or reinterpreted.
        result = verify_extension(_jsonl(forked), _jsonl([cp]), self.broker_public,
                                  self.trusted, DIGEST, self.witness(), self.witness_public)
        self.assertEqual(result.reason, "audit-does-not-extend-witness")

    def test_reject_signed_fork_with_other_genesis(self):
        alternate = chain([dict(self.prep, independent_note="different genesis"), self.out])
        cp = self.broker_key.sign_checkpoint(alternate[0]["entry_hash"], len(alternate), alternate[-1]["entry_hash"])
        result = verify_extension(_jsonl(alternate), _jsonl([cp]), self.broker_public,
                                  self.trusted, DIGEST, self.witness(), self.witness_public)
        self.assertEqual(result.reason, "audit-genesis-differs-from-witness")

    def test_reject_wrong_trusted_witness_key(self):
        self.assertEqual(
            verify_trusted_witness(self.witness(), self.other_witness_public, self.broker_public).reason,
            "witness-signature-invalid"
        )

    def test_reject_witness_signature_changed(self):
        raw = json.loads(self.witness())
        raw["signature"] = "0" * 128
        self.assertFalse(self.verdict(witness=json.dumps(raw).encode()).admit)

    def test_reject_changed_witness_checkpoint_count(self):
        raw = json.loads(self.witness())
        raw["checkpoint"]["count"] += 1
        self.assertFalse(self.verdict(witness=json.dumps(raw).encode()).admit)

    def test_reject_re_signed_witness_with_fake_broker_checkpoint(self):
        forged_cp = dict(self.cp1, head="f" * 64)
        res = verify_trusted_witness(self.witness(forged_cp), self.witness_public, self.broker_public)
        self.assertEqual(res.reason, "broker-checkpoint-signature-invalid")

    def test_reject_role_key_reuse_for_witness(self):
        # The broker key must not be accepted as the independently trusted
        # witness key, even if it signs a correctly encoded witness message.
        same_key = self.broker_key._private
        res = verify_trusted_witness(self.witness(signer=same_key),
                                     same_key.public_key(), self.broker_public)
        self.assertEqual(res.reason, "witness-and-broker-key-roles-overlap")

    def test_reject_duplicate_witness_json_fields(self):
        raw = self.witness()
        tampered = raw[:-1] + b',"v":1}'
        self.assertFalse(self.verdict(witness=tampered).admit)

    def test_reject_extra_field_in_witness(self):
        raw = json.loads(self.witness())
        raw["claimed_fresh"] = True
        self.assertFalse(self.verdict(witness=json.dumps(raw).encode()).admit)

    def test_reject_witness_boolean_count_even_when_signed(self):
        malformed = dict(self.cp1, count=True)
        self.assertEqual(verify_trusted_witness(
            self.witness(malformed), self.witness_public, self.broker_public
        ).reason, "invalid-broker-checkpoint-fields")

    def test_reject_unsigned_witness(self):
        self.assertFalse(self.verdict(witness=b'{}').admit)

    def test_reject_broker_private_ring(self):
        self.assertFalse(self.verdict(ring=self.broker_key).admit)

    def test_valid_witness_cannot_grant_unsupported_claim(self):
        req = make_request(claim_id="financial_advice_verified")
        self.assertFalse(self.verdict(request=req).admit)

    def test_valid_witness_cannot_grant_remote_acceptance(self):
        req = make_request(claim_id="remote_acceptance_confirmed")
        self.assertFalse(self.verdict(request=req).admit)

    def test_old_signed_witness_still_admits_historical_snapshot(self):
        # An honest test of the remaining gap: if the verifier's trusted
        # witness is stale, this mechanism has no oracle for unseen updates.
        self.assertTrue(self.verdict().admit)
        self.assertTrue(self.verdict(self.audit2, self.cps2).admit)
        self.assertTrue(self.verdict().admit)
        # External witness distribution / monotonic state is REQUIRED.

    def test_reject_missing_checkpoint_evidence(self):
        self.assertFalse(self.verdict(cps=b'').admit)


if __name__ == "__main__":
    unittest.main()
