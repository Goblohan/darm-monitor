"""Run with: PYTHONPATH=$HOME/darm-guard:. python3 -m unittest -v test_guard_bridge"""
from __future__ import annotations

import copy
import json
import unittest
from dataclasses import replace

from darm_guard.attest import KeyRing
from fixtures import NOW, POLICY, make_evidence, make_request
from guard_bridge import TrustedArtifact, decide_with_guard_artifact, verify_guard_artifact


CONTENT = b"benign report v1"
TARGET = "/workspace/reports/benign_report.txt"
RID = "req-0001"


class GuardBridgeTests(unittest.TestCase):
    def setUp(self):
        # Ephemeral test-only keys. Nothing is saved in the user's Guard tree.
        self.signer = KeyRing.generate()
        self.public = self.signer.public_only()
        self.expectation = TrustedArtifact(RID, TARGET)
        import hashlib
        self.digest = hashlib.sha256(CONTENT).hexdigest()
        self.att = self.signer.sign(RID, TARGET, self.digest)

    def check(self, request=None, att=None, content=CONTENT, expect=None, ring=None):
        return decide_with_guard_artifact(
            make_request() if request is None else request, POLICY, NOW,
            self.att if att is None else att,
            content,
            self.expectation if expect is None else expect,
            self.public if ring is None else ring,
        )

    def test_bound_guard_artifact_and_independent_hdb_warrant_admitted(self):
        self.assertTrue(self.check().admit)

    def test_real_guard_public_ring_verifies_genuine_attestation(self):
        c = verify_guard_artifact(self.att, CONTENT, self.expectation, self.public)
        self.assertTrue(c.verified, c.reason)
        self.assertEqual(c.digest, self.digest)

    def test_guard_signature_never_grants_financial_advice_warrant(self):
        verdict = self.check(request=make_request(claim_id="financial_advice_verified"))
        self.assertFalse(verdict.admit)
        self.assertIn("undischarged-target-warrant", verdict.reasons)

    def test_guard_signature_never_grants_missing_source_predicates(self):
        weak = make_request(source_evidence=make_evidence(claims=["json_shape", "file_integrity"]))
        self.assertFalse(self.check(request=weak).admit)

    def test_guard_signature_does_not_validate_remote_acceptance(self):
        self.assertFalse(self.check(request=make_request(claim_id="remote_acceptance_confirmed")).admit)

    def test_independently_signed_target_receipt_can_support_mock_remote_claim(self):
        request = make_request(claim_id="remote_acceptance_confirmed", target_evidence=make_evidence(issuer="target-key"))
        self.assertTrue(self.check(request=request).admit)

    def test_delimiter_in_signed_target_refused(self):
        target = "/workspace/report|other.txt"
        att = self.signer.sign(RID, target, self.digest)
        c = verify_guard_artifact(att, CONTENT, TrustedArtifact(RID, target), self.public)
        self.assertEqual(c.reason, "ambiguous-guard-delimited-identity")

    def test_delimiter_in_signed_request_id_refused(self):
        rid = "req|other"
        att = self.signer.sign(rid, TARGET, self.digest)
        c = verify_guard_artifact(att, CONTENT, TrustedArtifact(rid, TARGET), self.public)
        self.assertEqual(c.reason, "ambiguous-guard-delimited-identity")

    def test_modified_artifact_bytes_refused(self):
        self.assertIn("guard:guard-content-digest-mismatch", self.check(content=CONTENT+b"!").reasons)

    def test_replayed_to_other_target_refused(self):
        expected = TrustedArtifact(RID, "/workspace/reports/other.txt")
        self.assertIn("guard:guard-target-binding-mismatch", self.check(expect=expected).reasons)

    def test_request_id_mismatch_refused(self):
        expected = TrustedArtifact("req-9999", TARGET)
        self.assertIn("guard:guard-request-binding-mismatch", self.check(expect=expected).reasons)

    def test_hdb_request_mismatch_refused(self):
        request=make_request()
        request["request_id"]="req-other"
        self.assertIn("guard:reliance-request-mismatch", self.check(request=request).reasons)

    def test_reliance_subject_mismatch_refused(self):
        request=make_request()
        request["subject_digest"]="sha256:"+"0"*64
        self.assertIn("guard:reliance-subject-mismatch",self.check(request=request).reasons)

    def test_forged_guard_attestation_refused(self):
        obj=json.loads(self.att)
        obj["digest"]="1"*64
        self.assertIn("guard:guard-signature-untrusted-or-invalid",self.check(att=json.dumps(obj).encode()).reasons)

    def test_unknown_guard_key_refused(self):
        other=KeyRing.generate().public_only()
        self.assertIn("guard:guard-signature-untrusted-or-invalid",self.check(ring=other).reasons)

    def test_verifier_must_not_require_private_key(self):
        self.assertIn("guard:not-a-public-only-key-ring", self.check(ring=self.signer).reasons)

    def test_duplicate_signed_field_refused(self):
        obj=json.loads(self.att)
        parts=[f'"{k}":{json.dumps(v)}' for k,v in obj.items()]
        raw=('{' + ','.join(parts + ['"rid":"'+RID+'"']) + '}').encode()
        self.assertIn("guard:malformed-or-ambiguous-attestation", self.check(att=raw).reasons)

    def test_unknown_extra_field_refused(self):
        obj=json.loads(self.att);obj["semantic_safety_validated"]=True
        self.assertIn("guard:invalid-attestation-schema",self.check(att=json.dumps(obj).encode()).reasons)

    def test_legacy_version_refused(self):
        obj=json.loads(self.att);obj["v"]=1
        self.assertIn("guard:unsupported-attestation-version",self.check(att=json.dumps(obj).encode()).reasons)

    def test_unsupported_source_evidence_still_refused(self):
        request=make_request()
        request["source_evidence"]["signed"]["issued_at"]-=1
        self.assertIn("source:invalid-signature",self.check(request=request).reasons)

    def test_action_flag_does_not_grant_semantic_warrant(self):
        request=make_request(claim_id="financial_advice_verified")
        request["action_authorized"]=True
        verdict=self.check(request=request)
        self.assertFalse(verdict.admit)
        self.assertTrue(verdict.action_authorized)  # explicitly *mock*, not verified

    def test_absent_attestation_refused(self):
        c=verify_guard_artifact(b"",CONTENT,self.expectation,self.public)
        self.assertFalse(c.verified)

    def test_invalid_expected_context_refused(self):
        c=verify_guard_artifact(self.att,CONTENT,TrustedArtifact("",TARGET),self.public)
        self.assertFalse(c.verified)


if __name__ == '__main__':
    unittest.main()
