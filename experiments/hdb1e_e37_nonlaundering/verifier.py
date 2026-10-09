"""HDB-1E x E37 experimental claim-reliance verifier.

This is a research prototype, not an end-to-end proof of deployed security.
It checks cryptographic provenance, subject/policy/target binding, freshness,
issuer permissions and heterogeneous semantic obligations. No action is run.
"""
from __future__ import annotations

import base64
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from typing import Any, Mapping

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey


def canonical(value: Mapping[str, Any]) -> bytes:
    """Stable encoding for the *demo's* signing format; not generic canonical JSON."""
    return json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":"), allow_nan=False).encode()


@dataclass(frozen=True)
class Issuer:
    key: Ed25519PublicKey
    boundary: str
    permitted_claims: frozenset[str]
    allowed_schemas: frozenset[str]
    revoked: bool = False


@dataclass(frozen=True)
class Rule:
    """Target predicate requires every listed source predicate (conjunction)."""
    channel: str  # 'source' or 'target'
    requires: tuple[str, ...]


@dataclass(frozen=True)
class Policy:
    policy_id: str
    mapping_id: str
    source_boundary: str
    target_boundary: str
    rules: Mapping[str, Rule]
    claim_requirements: Mapping[str, frozenset[str]]
    introduced_obligations: frozenset[str]
    accepted_issuers: Mapping[str, Issuer]


@dataclass(frozen=True)
class Verdict:
    admit: bool
    reasons: tuple[str, ...]
    discharged: tuple[str, ...]
    outstanding: tuple[str, ...]
    action_authorized: bool

    def as_dict(self) -> dict[str, Any]:
        return {
            "reliance": "ADMIT" if self.admit else "REFUSE",
            "action_authorized": self.action_authorized,
            "reasons": list(self.reasons),
            "discharged": list(self.discharged),
            "outstanding": list(self.outstanding),
        }


REQUIRED_SIGNED_FIELDS = frozenset({
    "schema", "issuer", "boundary", "audience", "subject_digest",
    "policy_id", "issued_at", "expires_at", "claims", "request_id",
})


class InvalidEnvelope(Exception):
    pass


def _strings_list(value: Any) -> bool:
    return (isinstance(value, list) and all(isinstance(x, str) and x for x in value)
            and len(value) == len(set(value)))


def verify_envelope(envelope: Mapping[str, Any], policy: Policy,
                    now: int, audience: str, subject_digest: str,
                    request_id: str, required_boundary: str) -> tuple[frozenset[str], tuple[str, ...]]:
    """Return authenticated permitted predicates and refusal reasons.

    Never trust claims on failure, even when an intact envelope supplies some.
    """
    reasons: list[str] = []
    if not isinstance(envelope, dict) or set(envelope) != {"signed", "signature"}:
        return frozenset(), ("invalid-envelope",)
    signed = envelope["signed"]
    signature = envelope["signature"]
    if not isinstance(signed, dict) or set(signed) != REQUIRED_SIGNED_FIELDS:
        return frozenset(), ("invalid-schema",)
    if not _strings_list(signed["claims"]):
        return frozenset(), ("invalid-claims",)
    if not all(isinstance(signed[x], str) and signed[x] for x in REQUIRED_SIGNED_FIELDS - {"claims", "issued_at", "expires_at"}):
        return frozenset(), ("invalid-fields",)
    if any(type(signed[x]) is not int for x in ("issued_at", "expires_at")):
        return frozenset(), ("invalid-time-fields",)
    issuer = policy.accepted_issuers.get(signed["issuer"])
    if issuer is None or issuer.revoked:
        reasons.append("unknown-or-revoked-issuer")
    else:
        if signed["boundary"] != issuer.boundary or signed["schema"] not in issuer.allowed_schemas:
            reasons.append("issuer-domain-or-schema-mismatch")
        if not set(signed["claims"]) <= issuer.permitted_claims:
            reasons.append("issuer-claim-exceeds-authority")
        if not isinstance(signature, str):
            reasons.append("invalid-signature")
        else:
            try:
                issuer.key.verify(base64.b64decode(signature, validate=True), canonical(signed))
            except (InvalidSignature, ValueError, TypeError):
                reasons.append("invalid-signature")
    if signed["boundary"] != required_boundary:
        reasons.append("wrong-evidence-boundary")
    if signed["audience"] != audience:
        reasons.append("wrong-audience")
    if signed["subject_digest"] != subject_digest:
        reasons.append("wrong-subject")
    if signed["policy_id"] != policy.policy_id:
        reasons.append("policy-version-mismatch")
    if signed["request_id"] != request_id:
        reasons.append("wrong-request")
    if not (signed["issued_at"] <= now < signed["expires_at"]):
        reasons.append("expired-or-not-yet-valid")
    if reasons:
        return frozenset(), tuple(sorted(set(reasons)))
    return frozenset(signed["claims"]), ()


def decide(request: Mapping[str, Any], policy: Policy, now: int) -> Verdict:
    """Fail closed, and keep action authority separate from reliance authority."""
    action_authorized = request.get("action_authorized") is True
    if set(request) != {"source_evidence", "target_evidence", "subject_digest", "request_id",
                        "mapping_id", "source_boundary", "target_boundary",
                        "claim_id", "action_authorized"}:
        return Verdict(False, ("invalid-request",), (), (), action_authorized)
    if not isinstance(request["subject_digest"], str) or not request["subject_digest"]:
        return Verdict(False, ("invalid-subject",), (), (), action_authorized)
    if not isinstance(request["request_id"], str) or not request["request_id"]:
        return Verdict(False, ("invalid-request-id",), (), (), action_authorized)
    claim_id = request["claim_id"]
    if not isinstance(claim_id, str) or claim_id not in policy.claim_requirements:
        return Verdict(False, ("unknown-target-claim",), (), (), action_authorized)
    errors: list[str] = []
    if request["mapping_id"] != policy.mapping_id:
        errors.append("unknown-mapping")
    if request["source_boundary"] != policy.source_boundary or request["target_boundary"] != policy.target_boundary:
        errors.append("wrong-boundary-pair")
    subject = request["subject_digest"]
    reqid = request["request_id"]
    source_claims, source_errors = verify_envelope(
        request["source_evidence"], policy, now, policy.target_boundary,
        subject, reqid, policy.source_boundary)
    errors.extend("source:"+e for e in source_errors)
    target_claims = frozenset()
    if request["target_evidence"] is not None:
        target_claims, target_errors = verify_envelope(
            request["target_evidence"], policy, now, policy.target_boundary,
            subject, reqid, policy.target_boundary)
        errors.extend("target:"+e for e in target_errors)
    discharged: list[str] = []
    outstanding: list[str] = []
    required = policy.claim_requirements[claim_id] | policy.introduced_obligations
    for target_claim in sorted(required):
        rule = policy.rules.get(target_claim)
        if rule is None or rule.channel not in {"source", "target"} or not rule.requires:
            outstanding.append(target_claim + ":no-trusted-mapping")
            continue
        available = source_claims if rule.channel == "source" else target_claims
        missing = set(rule.requires) - available
        if missing:
            outstanding.append(target_claim + ":missing(" + ",".join(sorted(missing)) + ")")
        else:
            discharged.append(target_claim)
    if outstanding:
        errors.append("undischarged-target-warrant")
    return Verdict(not errors, tuple(sorted(set(errors))), tuple(discharged),
                   tuple(outstanding), action_authorized)
