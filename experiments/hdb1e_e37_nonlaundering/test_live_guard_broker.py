#!/usr/bin/env python3
"""E38 live local broker experiment, deliberately NOT an end-to-end proof.

Drives the actual DARM Guard BrokerClient -> socket server -> kernel ->
broker execution -> filesystem xattr -> audit log -> signed checkpoints,
then runs the existing E38 verifier on that evidence.

All effects live in a TemporaryDirectory under Linux /tmp. The HDB claim
issuer is a test-only fixture, not a real deployment authority. The
checkpoint sink shares this temporary host and is not an independent trust
domain. The experiment tests one local write tool, not arbitrary effects.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import tempfile
import threading
import unittest

import darm_guard.broker as B
from fixtures import NOW, POLICY, make_evidence, make_request
from guard_bridge import TrustedArtifact
from guard_audit_bridge import decide_with_guard_audit

LOGICAL_TARGET = "/workspace/reports/e38_live.txt"
CLAIM = "document_integrity"


def make_valid_hdb_request(rid: str, payload: bytes, claim: str = CLAIM,
                           claims: list[str] | None = None) -> dict:
    """Independent signed *test fixture*, not a DARM Guard-generated warrant."""
    digest = "sha256:" + hashlib.sha256(payload).hexdigest()
    evidence = make_evidence(
        request_id=rid,
        subject_digest=digest,
        claims=claims if claims is not None else [
            "json_shape", "file_integrity", "recipient_authority",
            "payload_authority", "external_send_authority"
        ],
    )
    request = make_request(claim_id=claim, source_evidence=evidence)
    request["request_id"] = rid
    request["subject_digest"] = digest
    # This field is explicitly mock metadata; the E38 adapter never uses
    # it to make a positive admission decision.
    request["action_authorized"] = False
    return request


class LiveBrokerEvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix="e38-live-")
        cls.base = Path(cls.tmp.name)
        cls.workspace = cls.base / "workspace"
        (cls.workspace / "reports").mkdir(parents=True)
        cls.config_path = cls.base / "config.json"
        cls.registry_path = cls.base / "registry.txt"
        cls.audit_path = cls.base / "audit.jsonl"
        cls.sink = cls.base / "checkpoint-sink"
        cls.sock = str(cls.base / "broker.sock")
        cls.config_path.write_text(json.dumps({
            "policy": {
                "tools": [{
                    "tool": "write_file",
                    "rules": [
                        {"key": "path", "allowedValues": [],
                         "allowedPrefixes": ["/workspace/reports/"]},
                        {"key": "content", "allowedValues": [],
                         "allowedPrefixes": [""], "payload": True},
                    ],
                }]
            },
            "credential_tools": ["write_file"],
            "workspace": str(cls.workspace),
        }))
        cls.registry_path.write_text("/workspace/reports/*\n")
        cls.server = None
        cls.thread = None
        try:
            cfg = B.BrokerConfig.load(str(cls.config_path), str(cls.registry_path))
            cls.server = B.serve(
                cfg, cls.sock, str(cls.audit_path),
                checkpoint_sink=str(cls.sink), checkpoint_every=1,
            )
            cls.thread = threading.Thread(target=cls.server.serve_forever,
                                          daemon=True)
            cls.thread.start()
            cls.client = B.BrokerClient(cls.sock)
            cls.public_ring = cls.server.broker.key.ring.public_only()
            cls.checkpoint_path = Path(
                cls.server.broker.audit.checkpointer.path_for(
                    cls.server.broker.audit.genesis or "0"*64
                )
            )
            # Unlike main(), serve() starts with an empty log. Add a real
            # AuditLog start entry before any effect for this fixture.
            cls.server.broker.audit.append({"event": "start"})
            cls.checkpoint_path = Path(
                cls.server.broker.audit.checkpointer.path_for(
                    cls.server.broker.audit.genesis
                )
            )
        except Exception:
            cls.tearDownClass()
            raise

    @classmethod
    def tearDownClass(cls):
        server = getattr(cls, "server", None)
        if server is not None:
            try:
                if getattr(cls, "thread", None) is not None:
                    server.shutdown()
            finally:
                try:
                    server.server_close()
                finally:
                    kernel = server.broker.kernel
                    proc = getattr(kernel, "_proc", None)
                    kernel.close()
                    if proc is not None:
                        try:
                            proc.wait(timeout=5)
                        finally:
                            for stream in (proc.stdin, proc.stdout, proc.stderr):
                                if stream is not None:
                                    stream.close()
        if getattr(cls, "thread", None) is not None:
            cls.thread.join(timeout=2)
        if hasattr(cls, "tmp"):
            cls.tmp.cleanup()

    @classmethod
    def write(cls, content: bytes):
        response = cls.client.propose(
            "write_file", {"path": LOGICAL_TARGET,
                           "content": content.decode("utf-8")}
        )
        if response.get("decision") != "admit" or response.get("effect") != "succeeded":
            raise AssertionError(
                "Actual Guard broker rejected the disposable write: "
                + json.dumps({
                    k: response.get(k) for k in
                    ("decision", "effect", "failure", "error")
                }, sort_keys=True)
            )
        path = cls.workspace / "reports" / "e38_live.txt"
        observed = path.read_bytes()
        if observed != content:
            raise AssertionError("Actual file bytes did not match requested write")
        attestation = os.getxattr(path, B.XATTR)
        return response["request_id"], attestation, observed

    @classmethod
    def snapshot(cls):
        if not cls.checkpoint_path.exists():
            raise AssertionError("Guard has not published a signed checkpoint")
        return cls.audit_path.read_bytes(), cls.checkpoint_path.read_bytes()

    @classmethod
    def verdict(cls, rid, att, content, audit, checkpoints, claim=CLAIM,
                claims=None):
        return decide_with_guard_audit(
            make_valid_hdb_request(rid, content, claim=claim, claims=claims),
            POLICY, NOW, att, content,
            TrustedArtifact(rid, LOGICAL_TARGET),
            cls.public_ring, audit, checkpoints,
        )

    def test_real_broker_and_stale_snapshot(self):
        first = b'{"report":"E38 first"}'
        rid1, att1, bytes1 = self.write(first)
        audit1, cp1 = self.snapshot()

        valid1 = self.verdict(rid1, att1, bytes1, audit1, cp1)
        self.assertTrue(valid1.admit, valid1.reasons)

        # Even valid execution evidence must not mint unrelated semantic
        # authority, or compensate for separately insufficient source warrant.
        no_financial_warrant = self.verdict(
            rid1, att1, bytes1, audit1, cp1, claim="financial_advice_verified"
        )
        self.assertFalse(no_financial_warrant.admit)

        insufficient = self.verdict(
            rid1, att1, bytes1, audit1, cp1, claims=["json_shape"]
        )
        self.assertFalse(insufficient.admit)

        second = b'{"report":"E38 second"}'
        rid2, att2, bytes2 = self.write(second)
        audit2, cp2 = self.snapshot()
        self.assertNotEqual(rid1, rid2)

        # First signed artifact is genuine but superseded in the later log.
        stale_in_current_snapshot = self.verdict(
            rid1, att1, bytes1, audit2, cp2
        )
        self.assertFalse(stale_in_current_snapshot.admit)
        self.assertTrue(any("later-operation" in r for r in
                            stale_in_current_snapshot.reasons),
                        stale_in_current_snapshot.reasons)

        valid2 = self.verdict(rid2, att2, bytes2, audit2, cp2)
        self.assertTrue(valid2.admit, valid2.reasons)

        # This deliberate counterexample exposes the limitation: presenting
        # only the OLD checkpoint and OLD log still permits an old "as-of"
        # conclusion. A deployment needs an independently obtained current
        # checkpoint or a freshness protocol.
        historical = self.verdict(rid1, att1, bytes1, audit1, cp1)
        self.assertTrue(historical.admit, historical.reasons)

        print("\nE38 live broker experiment:")
        print(json.dumps({
            "real_broker_execution": True,
            "first_write_admitted_as_of_first_snapshot": valid1.admit,
            "unsupported_financial_claim_refused": not no_financial_warrant.admit,
            "insufficient_source_warrant_refused": not insufficient.admit,
            "superseded_first_write_refused_in_new_snapshot":
                not stale_in_current_snapshot.admit,
            "second_write_admitted_as_of_new_snapshot": valid2.admit,
            "old_snapshot_still_admits_historical_claim": historical.admit,
            "external_independent_freshness_established": False,
            "hdb_issuers_are_synthetic_test_only": True,
            "actual_broker_version_used": True,
        }, indent=2))


if __name__ == "__main__":
    unittest.main(verbosity=2)
