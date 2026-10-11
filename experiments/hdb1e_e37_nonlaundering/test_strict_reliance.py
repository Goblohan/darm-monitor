"""Evidence-bound integration regressions. No claim of complete effect mediation."""
from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from fixtures import NOW, POLICY, SUBJECT, make_request
from correspondence_runtime import TrustedReliance, policy_fingerprint
from lean_authority import LeanAuthoritativeCore
from strict_reliance import StrictRelianceGate
from test_guard_monotonic_bridge import MonotonicWitnessStoreTests, CONTENT
from witness_authority import WitnessAuthority


class StrictRelianceIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.fx = MonotonicWitnessStoreTests(methodName="test_explicit_enrollment_and_reliance")
        self.fx.setUp()
        self.addCleanup(self.fx.doCleanups)
        self.fx.enroll()
        self.auth_dir = self.fx.root / "separate-demo-witness"
        self.auth_dir.mkdir(mode=0o700)
        self.authority = WitnessAuthority(self.auth_dir, self.fx.witness_private, self.fx.public)
        self.authority.append(self.pack(self.fx.cp1, self.fx.rows1), enroll=True)
        self.sandbox = tempfile.TemporaryDirectory()
        self.addCleanup(self.sandbox.cleanup)
        root = Path(self.sandbox.name)
        oracle = root / "experiments/hdb1e_e37_nonlaundering/CorrespondenceOracle.lean"
        oracle.parent.mkdir(parents=True)
        oracle.write_text("-- dummy for unit mock")
        self.core = LeanAuthoritativeCore(root)
        self.trusted = TrustedReliance("document_integrity", self.fx.trusted.request_id,
                                       self.fx.trusted.target, SUBJECT, policy_fingerprint(POLICY))
        self.gate = self.new_gate()
        self.raw_req = json.dumps(make_request("document_integrity"), sort_keys=True).encode()

    @staticmethod
    def pack(cp, rows):
        return json.dumps({"checkpoint": cp, "entries": rows}, sort_keys=True).encode()

    def new_gate(self, fetch=None):
        return StrictRelianceGate(POLICY, self.trusted, self.fx.store, self.core,
                                  self.authority.challenge if fetch is None else fetch)

    def decide(self, gate=None, *, raw_req=None, audit=None, cps=None, att=None, content=None):
        f = self.fx
        return (gate or self.gate).decide_json(
            self.raw_req if raw_req is None else raw_req,
            NOW, f.att if att is None else att,
            CONTENT if content is None else content,
            f.audit1 if audit is None else audit,
            f.cps1 if cps is None else cps)

    @staticmethod
    def lean_response(decision):
        return subprocess.CompletedProcess(["lean"], 0,
                                           json.dumps([decision]) + "\n", "")

    @patch("lean_authority.subprocess.run")
    def test_positive_uses_live_witness_and_lean(self, run):
        run.return_value = self.lean_response(True)
        v = self.decide()
        self.assertTrue(v.admit, v.reasons)
        self.assertEqual(run.call_count, 1)

    @patch("lean_authority.subprocess.run")
    def test_lean_refuses_no_python_fallback(self, run):
        run.return_value = self.lean_response(False)
        self.assertFalse(self.decide().admit)
        self.assertEqual(run.call_count, 1)

    @patch("lean_authority.subprocess.run")
    def test_lean_failure_refuses(self, run):
        run.side_effect = subprocess.TimeoutExpired("lean", 20)
        self.assertFalse(self.decide().admit)
        self.assertEqual(run.call_count, 1)

    @patch("lean_authority.subprocess.run")
    def test_no_witness_refuses_before_lean(self, run):
        gate = self.new_gate(fetch=lambda _: (_ for _ in ()).throw(OSError("offline")))
        self.assertFalse(self.decide(gate).admit)
        run.assert_not_called()

    @patch("lean_authority.subprocess.run")
    def test_unacknowledged_new_audit_head_refuses(self, run):
        run.return_value = self.lean_response(True)
        self.assertFalse(self.decide(audit=self.fx.audit2, cps=self.fx.cps2).admit)
        run.assert_not_called()
        self.authority.append(self.pack(self.fx.cp2, self.fx.rows2[2:]))
        self.assertTrue(self.decide(audit=self.fx.audit2, cps=self.fx.cps2).admit)
        self.assertEqual(run.call_count, 1)

    @patch("lean_authority.subprocess.run")
    def test_mismatched_subject_refuses_before_lean(self, run):
        self.assertFalse(self.decide(content=b"unexpected content").admit)
        run.assert_not_called()

    @patch("lean_authority.subprocess.run")
    def test_agent_action_flag_not_independent_effect_authority(self, run):
        run.return_value = self.lean_response(True)
        req = json.loads(self.raw_req)
        req["action_authorized"] = True
        v = self.decide(raw_req=json.dumps(req).encode())
        self.assertTrue(v.admit)
        self.assertTrue(v.action_authorized)
        # This flags data from the request. StrictRelianceGate does not
        # implement, claim or confer effect authorization.
        self.assertFalse(hasattr(self.gate, "execute_effect"))

    def test_reject_nonlean_core(self):
        with self.assertRaisesRegex(ValueError, "genuine-lean-executor"):
            StrictRelianceGate(POLICY, self.trusted, self.fx.store, object(),
                               self.authority.challenge)


if __name__ == "__main__":
    unittest.main()
