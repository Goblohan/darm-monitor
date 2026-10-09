"""Deterministic synthetic Ed25519 research fixtures. PRIVATE KEYS FOR TESTS ONLY."""
from __future__ import annotations

import base64
import copy
import hashlib
from dataclasses import replace

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from verifier import Issuer, Policy, Rule, canonical

SEED_SOURCE = b"\x17" * 32  # DO NOT USE OUTSIDE TESTS
SEED_TARGET = b"\x29" * 32  # DO NOT USE OUTSIDE TESTS
SOURCE_KEY = Ed25519PrivateKey.from_private_bytes(SEED_SOURCE)
TARGET_KEY = Ed25519PrivateKey.from_private_bytes(SEED_TARGET)
NOW = 1_800_000_000   # fixed clock: no dependence on wall time
SUBJECT = "sha256:" + hashlib.sha256(b"benign report v1").hexdigest()

POLICY = Policy(
    policy_id="policy:2026-10-demo-v1",
    mapping_id="mapping:validation-v1_to_decision-v2",
    source_boundary="validation.v1",
    target_boundary="decision.v2",
    rules={
        "structured_document": Rule("source", ("json_shape",)),
        "artifact_integrity": Rule("source", ("file_integrity",)),
        "recipient_authorized": Rule("source", ("recipient_authority",)),
        "payload_authorized": Rule("source", ("payload_authority",)),
        "send_authorized": Rule("source", ("external_send_authority",)),
        # A source cannot claim what actually happened in the remote system.
        "remote_accepted": Rule("target", ("remote_receipt",)),
    },
    claim_requirements={
        "report_transmission_authorized": frozenset({"structured_document", "recipient_authorized", "payload_authorized", "send_authorized"}),
        "document_integrity": frozenset({"structured_document", "artifact_integrity"}),
        "remote_acceptance_confirmed": frozenset({"remote_accepted"}),
        "financial_advice_verified": frozenset({"financial_advice_verified"}),
    },
    introduced_obligations=frozenset({"artifact_integrity"}),
    accepted_issuers={
        "source-key": Issuer(SOURCE_KEY.public_key(), "validation.v1",
            frozenset({"json_shape", "file_integrity", "recipient_authority", "payload_authority", "external_send_authority"}),
            frozenset({"validation-receipt/1"})),
        "target-key": Issuer(TARGET_KEY.public_key(), "decision.v2",
            frozenset({"remote_receipt"}), frozenset({"decision-receipt/1"})),
    },
)


def sign(fields, private_key):
    return {"signed": copy.deepcopy(fields),
            "signature": base64.b64encode(private_key.sign(canonical(fields))).decode()}


def make_evidence(issuer="source-key", claims=None, **overrides):
    source = issuer == "source-key"
    fields = dict(schema="validation-receipt/1" if source else "decision-receipt/1",
                  issuer=issuer, boundary="validation.v1" if source else "decision.v2",
                  audience="decision.v2", subject_digest=SUBJECT, policy_id=POLICY.policy_id,
                  issued_at=NOW-30, expires_at=NOW+3600, request_id="req-0001",
                  claims=list(claims if claims is not None else (
                      ["json_shape", "file_integrity", "recipient_authority", "payload_authority", "external_send_authority"]
                      if source else ["remote_receipt"])))
    fields.update(overrides)
    return sign(fields, SOURCE_KEY if source else TARGET_KEY)


def make_request(claim_id="report_transmission_authorized", target_evidence=None, source_evidence=None):
    return dict(source_evidence=source_evidence if source_evidence is not None else make_evidence(),
                target_evidence=target_evidence, subject_digest=SUBJECT, request_id="req-0001",
                mapping_id=POLICY.mapping_id, source_boundary=POLICY.source_boundary,
                target_boundary=POLICY.target_boundary,
                claim_id=claim_id, action_authorized=True)
