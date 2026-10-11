"""Security regressions for the consumer-owned relying profile."""
from __future__ import annotations
import copy
import json
import unittest
from dataclasses import replace
from unittest.mock import patch

from fixtures import NOW, POLICY, SUBJECT, make_request, make_evidence
from verifier import decide, Rule
from correspondence_core import admit_core
from correspondence_runtime import (PinnedRelianceVerifier, TrustedReliance,
    freeze_policy, policy_fingerprint, load_request)
import correspondence_runtime as runtime
import test_guard_monotonic_bridge as pin_tests
from test_guard_audit_bridge import chain, _jsonl


class ConsumerProfileTests(unittest.TestCase):
    def setUp(self):
        # Reuse only setup/helpers, not inherited tests or an alternate key API.
        self.fx = pin_tests.MonotonicWitnessStoreTests(methodName="test_explicit_enrollment_and_reliance")
        self.fx.setUp()
        self.addCleanup(self.fx.doCleanups)
        self.fx.enroll()
        self.context = TrustedReliance("document_integrity", self.fx.trusted.request_id,
            self.fx.trusted.target, SUBJECT, policy_fingerprint(POLICY))
        self.gate = PinnedRelianceVerifier(POLICY, self.context, self.fx.store)

    def check(self, request=None, gate=None, **kw):
        f = self.fx
        return (gate or self.gate).decide(
            make_request("document_integrity") if request is None else request,
            kw.get("now", NOW), kw.get("att", f.att), kw.get("content", b"benign report v1"),
            kw.get("audit", f.audit1), kw.get("cps", f.cps1))

    def test_valid_consumer_bound_claim_admitted(self):
        self.assertTrue(self.check().admit)

    def test_claim_downgrade_cannot_satisfy_stronger_consumer(self):
        weak = make_request("document_integrity",
            source_evidence=make_evidence(claims=["json_shape", "file_integrity"]))
        self.assertTrue(decide(weak, POLICY, NOW).admit)  # legacy query answers weaker claim
        gate = PinnedRelianceVerifier(POLICY,
            replace(self.context, claim_id="report_transmission_authorized"), self.fx.store)
        result = self.check(weak, gate)
        self.assertFalse(result.admit)
        self.assertIn("consumer:claim_id-mismatch", result.reasons)

    def test_pin_is_mandatory(self):
        self.fx.store.state.unlink()
        self.assertEqual(self.check().reasons, ("pin:not-enrolled",))

    def test_old_snapshot_refused_after_advance(self):
        self.assertTrue(self.fx.advance2().ok)
        self.assertFalse(self.check().admit)
        self.assertTrue(self.check(audit=self.fx.audit2, cps=self.fx.cps2).admit)

    def test_signed_fork_refused(self):
        bodies = [self.fx.body(x) for x in self.fx.rows1]
        bodies[-1]["note"] = "fork"
        rows = chain(bodies)
        self.assertFalse(self.check(audit=_jsonl(rows), cps=_jsonl([self.fx.cp(rows)])).admit)

    def test_signed_off_branch_checkpoint_cannot_hide_among_valid_ones(self):
        cp = self.fx.key.sign_checkpoint(self.fx.cp1["genesis"], 1, "f" * 64)
        v = self.check(cps=_jsonl([cp, self.fx.cp1]))
        self.assertFalse(v.admit)
        self.assertEqual(v.reasons, ("audit:checkpoint-off-audit-history",))

    def test_unknown_checkpoint_field_refused(self):
        cp = dict(self.fx.cp1, semantic_truth=True)
        self.assertFalse(self.check(cps=_jsonl([cp])).admit)

    def test_subject_request_and_target_replay_refused(self):
        for field, value in (("subject_digest", "sha256:" + "0" * 64),
                             ("request_id", "other")):
            with self.subTest(field=field):
                req = make_request("document_integrity")
                req[field] = value
                self.assertFalse(self.check(req).admit)
        wrong = self.fx.key.sign(self.context.request_id, "/wrong", self.fx.cp1["head"])
        self.assertFalse(self.check(att=wrong).admit)

    def test_missing_warrant_refused_despite_broker_admission(self):
        req = make_request("document_integrity", source_evidence=make_evidence(claims=["file_integrity"]))
        self.assertFalse(self.check(req).admit)

    def test_remote_receipt_must_come_from_target_channel(self):
        ctx = replace(self.context, claim_id="remote_acceptance_confirmed")
        gate = PinnedRelianceVerifier(POLICY, ctx, self.fx.store)
        self.assertFalse(self.check(make_request(ctx.claim_id), gate).admit)
        req = make_request(ctx.claim_id, target_evidence=make_evidence(issuer="target-key"))
        self.assertTrue(self.check(req, gate).admit)

    def test_signature_and_expiry_are_not_bypassed(self):
        bad = make_request("document_integrity")
        bad["source_evidence"]["signed"]["issued_at"] -= 1
        self.assertFalse(self.check(bad).admit)
        expired = make_request("document_integrity", source_evidence=make_evidence(expires_at=NOW))
        self.assertFalse(self.check(expired).admit)

    def test_same_policy_id_cannot_hide_changed_policy_contents(self):
        variants = [
            replace(POLICY, mapping_id="other"),
            replace(POLICY, introduced_obligations=frozenset()),
            replace(POLICY, rules={**POLICY.rules, "artifact_integrity": Rule("source", ("json_shape",))}),
            replace(POLICY, claim_requirements={**POLICY.claim_requirements,
                "document_integrity": frozenset({"structured_document"})}),
            replace(POLICY, accepted_issuers={**POLICY.accepted_issuers,
                "source-key": replace(POLICY.accepted_issuers["source-key"], revoked=True)}),
            replace(POLICY, accepted_issuers={**POLICY.accepted_issuers,
                "source-key": replace(POLICY.accepted_issuers["source-key"],
                    key=POLICY.accepted_issuers["target-key"].key)}),
            replace(POLICY, accepted_issuers={**POLICY.accepted_issuers,
                "source-key": replace(POLICY.accepted_issuers["source-key"],
                    permitted_claims=frozenset({"json_shape"}))}),
        ]
        for policy in variants:
            with self.subTest(fingerprint=policy_fingerprint(policy)):
                with self.assertRaisesRegex(ValueError, "fingerprint-mismatch"):
                    PinnedRelianceVerifier(policy, self.context, self.fx.store)

    def test_policy_frozen_after_configuration(self):
        rules, claims = dict(POLICY.rules), dict(POLICY.claim_requirements)
        policy = replace(POLICY, rules=rules, claim_requirements=claims)
        gate = PinnedRelianceVerifier(policy, self.context, self.fx.store)
        rules.clear()
        claims.clear()
        self.assertTrue(self.check(gate=gate).admit)

    def test_duplicate_keys_rejected_before_verification(self):
        req = json.dumps(make_request("document_integrity"))
        raw = (req[:-1] + ',"claim_id":"document_integrity"}').encode()
        with self.assertRaises(ValueError):
            load_request(raw)
        v = self.gate.decide_json(raw, NOW, self.fx.att, b"benign report v1", self.fx.audit1, self.fx.cps1)
        self.assertFalse(v.admit)

    def test_nonfinite_numbers_and_nonobject_requests_refused(self):
        for raw in (b'{"x":NaN}', b'{"x":Infinity}', b'null', b'[]', b'{}' * 600000):
            with self.subTest(raw=raw[:30]):
                with self.assertRaises(ValueError):
                    load_request(raw)
        for request in (None, [], True, "x"):
            self.assertFalse(self.gate.decide(request, NOW, self.fx.att,
                b"benign report v1", self.fx.audit1, self.fx.cps1).admit)

    def test_invalid_clock_refused(self):
        for now in (True, "1800000000", float("nan"), -1):
            self.assertFalse(self.check(now=now).admit)

    def test_no_duplicate_artifact_or_snapshot_verification(self):
        with patch.object(runtime, "verify_guard_artifact", wraps=runtime.verify_guard_artifact) as a:
            with patch.object(runtime, "verify_snapshot", wraps=runtime.verify_snapshot) as s:
                self.assertTrue(self.check().admit)
                self.assertEqual((a.call_count, s.call_count), (1, 1))

    def test_action_metadata_does_not_grant_or_remove_reliance(self):
        req = make_request("document_integrity")
        req["action_authorized"] = False
        self.assertTrue(self.check(req).admit)
        req["source_evidence"] = make_evidence(claims=[])
        req["action_authorized"] = True
        self.assertFalse(self.check(req).admit)

    def test_authenticated_assertion_is_not_external_truth(self):
        # The test issuer asserts json_shape for these non-JSON bytes. Its valid
        # signature supplies policy entitlement, never a proof that it was honest.
        with self.assertRaises(ValueError):
            json.loads(b"benign report v1")
        self.assertTrue(self.check().admit)


class OperationalCoreTests(unittest.TestCase):
    def test_empty_contract_and_empty_row_refuse(self):
        self.assertFalse(admit_core(("source:p",), (), (True,)))
        self.assertFalse(admit_core(("source:p",), ((),), (True,)))

    def test_channel_identity_and_conjunction_are_required(self):
        self.assertFalse(admit_core(("source:p",), (("target:p",),), (True,)))
        self.assertFalse(admit_core(("source:p",), (("source:p", "source:q"),), (True,)))
        self.assertTrue(admit_core(("source:p", "target:p"), (("target:p",),), (True,)))

    def test_every_gate_bit_is_required_and_truthy_is_insufficient(self):
        for i in range(9):
            gates = [True] * 9
            gates[i] = False
            self.assertFalse(admit_core(("source:p",), (("source:p",),), tuple(gates)))
        self.assertFalse(admit_core(("source:p",), (("source:p",),), (1,)))

    def test_empty_policy_contract_refused_in_legacy_entry(self):
        p = replace(POLICY, claim_requirements={"document_integrity": frozenset()},
                    introduced_obligations=frozenset())
        self.assertFalse(decide(make_request("document_integrity"), p, NOW).admit)
        with self.assertRaises(ValueError):
            freeze_policy(p)

    def test_nonobject_legacy_input_refuses(self):
        for req in (None, [], 1, "x"):
            self.assertFalse(decide(req, POLICY, NOW).admit)


if __name__ == "__main__":
    unittest.main()
