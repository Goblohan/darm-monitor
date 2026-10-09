"""Adversarial tests. Execute: python -m unittest -v tests"""
from __future__ import annotations

import copy
import unittest
from dataclasses import replace

from fixtures import NOW, POLICY, SUBJECT, make_evidence, make_request
from verifier import Issuer, Policy, Rule, decide


class NonLaunderingTests(unittest.TestCase):
    def test_hdb_A_complete_without_reassurance_needed(self):
        self.assertTrue(decide(make_request(), POLICY, NOW).admit)

    def test_hdb_B_json_shape_only(self):
        r = make_request(source_evidence=make_evidence(claims=["json_shape", "file_integrity"]))
        self.assertFalse(decide(r, POLICY, NOW).admit)

    def test_hdb_C_no_confidence_label(self):
        r = make_request()
        self.assertTrue(decide(r, POLICY, NOW).admit)

    def test_hdb_D_inflated_validation_label_no_effect(self):
        r = make_request(source_evidence=make_evidence(claims=["json_shape", "file_integrity", "payload_authority"]))
        self.assertFalse(decide(r, POLICY, NOW).admit)

    def test_signature_tampered(self):
        r=make_request()
        r["source_evidence"]["signed"]["issued_at"] = NOW-31  # plausible value, invalid signature only
        self.assertIn("source:invalid-signature", decide(r, POLICY, NOW).reasons)

    def test_signature_replayed_on_other_subject(self):
        r=make_request()
        r["subject_digest"]="sha256:"+"1"*64
        self.assertIn("source:wrong-subject",decide(r,POLICY,NOW).reasons)

    def test_other_request(self):
        r=make_request()
        r["request_id"]="req-attacker"
        self.assertIn("source:wrong-request",decide(r,POLICY,NOW).reasons)

    def test_expired_valid_signature(self):
        r=make_request(source_evidence=make_evidence(expires_at=NOW-1))
        self.assertIn("source:expired-or-not-yet-valid",decide(r,POLICY,NOW).reasons)

    def test_future_valid_signature(self):
        r=make_request(source_evidence=make_evidence(issued_at=NOW+1))
        self.assertFalse(decide(r,POLICY,NOW).admit)

    def test_wrong_policy(self):
        r=make_request(source_evidence=make_evidence(policy_id="policy:old"))
        self.assertIn("source:policy-version-mismatch",decide(r,POLICY,NOW).reasons)

    def test_wrong_audience(self):
        r=make_request(source_evidence=make_evidence(audience="different.consumer"))
        self.assertIn("source:wrong-audience",decide(r,POLICY,NOW).reasons)

    def test_wrong_boundary_pair(self):
        r=make_request()
        r["target_boundary"]="decision.v3"
        self.assertIn("wrong-boundary-pair",decide(r,POLICY,NOW).reasons)

    def test_unknown_mapping(self):
        r=make_request()
        r["mapping_id"]="user-provided-mapping"
        self.assertIn("unknown-mapping",decide(r,POLICY,NOW).reasons)

    def test_unmapped_semantic_upgrade(self):
        r=make_request(claim_id="financial_advice_verified")
        self.assertIn("financial_advice_verified:no-trusted-mapping",decide(r,POLICY,NOW).outstanding)

    def test_target_new_obligation_not_in_source(self):
        r=make_request(source_evidence=make_evidence(claims=["json_shape", "recipient_authority", "payload_authority", "external_send_authority"]))
        self.assertIn("artifact_integrity:missing(file_integrity)",decide(r,POLICY,NOW).outstanding)

    def test_remote_persistence_needs_independent_target_receipt(self):
        r=make_request(claim_id="remote_acceptance_confirmed")
        self.assertFalse(decide(r,POLICY,NOW).admit)
        self.assertIn("remote_accepted:missing(remote_receipt)",decide(r,POLICY,NOW).outstanding)
        r["target_evidence"]=make_evidence(issuer="target-key")
        self.assertTrue(decide(r,POLICY,NOW).admit)

    def test_target_receipt_from_wrong_boundary(self):
        r=make_request(claim_id="remote_acceptance_confirmed",target_evidence=make_evidence(issuer="target-key",boundary="validation.v1"))
        self.assertFalse(decide(r,POLICY,NOW).admit)

    def test_target_receipt_from_unpermitted_issuer(self):
        r=make_request(claim_id="remote_acceptance_confirmed",target_evidence=make_evidence(issuer="source-key",claims=["remote_receipt"],boundary="decision.v2",schema="decision-receipt/1"))
        self.assertIn("target:issuer-claim-exceeds-authority",decide(r,POLICY,NOW).reasons)

    def test_authorized_effect_does_not_imply_reliance(self):
        r=make_request(claim_id="financial_advice_verified")
        v=decide(r,POLICY,NOW)
        self.assertTrue(v.action_authorized)
        self.assertFalse(v.admit)

    def test_unrelated_action_auth_is_not_source_of_reliance(self):
        r=make_request()
        r["action_authorized"]=False
        v=decide(r,POLICY,NOW)
        self.assertFalse(v.action_authorized)
        self.assertTrue(v.admit)  # relying on a verified proposition != permission to cause an effect

    def test_revoked_issuer(self):
        issuers=dict(POLICY.accepted_issuers)
        issuers["source-key"]=replace(issuers["source-key"],revoked=True)
        p=replace(POLICY,accepted_issuers=issuers)
        self.assertIn("source:unknown-or-revoked-issuer",decide(make_request(),p,NOW).reasons)

    def test_unauthorized_assertion_even_if_signed(self):
        r=make_request(source_evidence=make_evidence(claims=["json_shape", "file_integrity", "recipient_authority", "payload_authority", "external_send_authority", "risk_certified"]))
        self.assertIn("source:issuer-claim-exceeds-authority",decide(r,POLICY,NOW).reasons)

    def test_invalid_duplicate_claims(self):
        r=make_request(source_evidence=make_evidence(claims=["json_shape", "json_shape"]))
        self.assertIn("source:invalid-claims",decide(r,POLICY,NOW).reasons)

    def test_policy_introduces_new_required_predicate(self):
        p=replace(POLICY,introduced_obligations=POLICY.introduced_obligations | {"remote_accepted"})
        self.assertFalse(decide(make_request(),p,NOW).admit)

    def test_malformed_request_rejected(self):
        r=make_request();r["unexpected_authority"]=True
        self.assertIn("invalid-request",decide(r,POLICY,NOW).reasons)

    def test_agent_cannot_reduce_required_warrants(self):
        r=make_request(source_evidence=make_evidence(claims=["json_shape", "file_integrity"]))
        r["required_target_warrant"]=["json_shape"]  # attempt to rewrite target policy
        self.assertIn("invalid-request",decide(r,POLICY,NOW).reasons)

    def test_undocumented_target_claim_is_rejected(self):
        r=make_request();r["claim_id"]="trust_me"
        self.assertIn("unknown-target-claim",decide(r,POLICY,NOW).reasons)

    def test_wrong_signer_and_same_key_id(self):
        r=make_request(source_evidence=make_evidence(issuer="target-key",boundary="validation.v1",schema="validation-receipt/1",claims=["json_shape", "file_integrity"]))
        self.assertFalse(decide(r,POLICY,NOW).admit)

    def test_genuine_different_encoding_only_with_trusted_mapping(self):
        r=make_request(claim_id="document_integrity")
        v=decide(r,POLICY,NOW)
        self.assertTrue(v.admit)
        self.assertIn("structured_document",v.discharged)


if __name__ == "__main__":
    unittest.main()
