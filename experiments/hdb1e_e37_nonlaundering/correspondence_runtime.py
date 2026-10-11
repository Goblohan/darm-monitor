"""Consumer-owned E38 profile: pinned claim, policy, target, and log witness.

This is a relying verifier for immutable observed bytes at a signed snapshot.
The consumer MUST call it at reliance and honor REFUSE. It cannot prove issuer
honesty, independent witness operation, host protection, or Python refinement.
No agent-controlled switch to the weaker legacy profiles is provided here.
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from types import MappingProxyType

from cryptography.hazmat.primitives import serialization

from guard_audit_bridge import _parse_jsonl, verify_snapshot
from guard_bridge import TrustedArtifact, verify_guard_artifact
from guard_monotonic_bridge import MonotonicWitnessStore, PinError
from verifier import Policy, Rule, Issuer, Verdict, canonical, decide
from correspondence_core import admit_core

MAX_REQUEST_BYTES = 1_048_576


def _names(values, *, nonempty=False):
    if not isinstance(values, (tuple, list, set, frozenset)):
        raise ValueError("invalid-name-collection")
    if nonempty and not values:
        raise ValueError("empty-name-collection")
    if any(type(x) is not str or not x for x in values):
        raise ValueError("invalid-name")
    return tuple(sorted(values))


def freeze_policy(policy: Policy) -> Policy:
    """Take one immutable local snapshot of trusted policy configuration."""
    if not isinstance(policy, Policy):
        raise ValueError("invalid-policy")
    for x in (policy.policy_id, policy.mapping_id, policy.source_boundary, policy.target_boundary):
        if type(x) is not str or not x:
            raise ValueError("invalid-policy-identity")
    rules, claims, issuers = {}, {}, {}
    for name, rule in policy.rules.items():
        if type(name) is not str or not name or not isinstance(rule, Rule):
            raise ValueError("invalid-policy-rule")
        if rule.channel not in {"source", "target"}:
            raise ValueError("invalid-policy-channel")
        rules[name] = Rule(rule.channel, _names(rule.requires, nonempty=True))
    for name, required in policy.claim_requirements.items():
        if type(name) is not str or not name:
            raise ValueError("invalid-policy-claim")
        claims[name] = frozenset(_names(required, nonempty=True))
    for name, issuer in policy.accepted_issuers.items():
        if (type(name) is not str or not name or not isinstance(issuer, Issuer)
                or type(issuer.boundary) is not str or not issuer.boundary
                or type(issuer.revoked) is not bool):
            raise ValueError("invalid-policy-issuer")
        issuers[name] = Issuer(issuer.key, issuer.boundary,
            frozenset(_names(issuer.permitted_claims)),
            frozenset(_names(issuer.allowed_schemas, nonempty=True)), issuer.revoked)
    return Policy(policy.policy_id, policy.mapping_id, policy.source_boundary,
        policy.target_boundary, MappingProxyType(rules), MappingProxyType(claims),
        frozenset(_names(policy.introduced_obligations)), MappingProxyType(issuers))


def policy_fingerprint(policy: Policy) -> str:
    """Pin actual rules, obligations, permissions, revocation and public keys.

    A hash is an identity binding, not certification of policy adequacy.
    The expected hash must be provisioned by the relying consumer.
    """
    body = dict(v=1, policy_id=policy.policy_id, mapping_id=policy.mapping_id,
        source_boundary=policy.source_boundary, target_boundary=policy.target_boundary,
        rules={k: [v.channel, sorted(v.requires)] for k, v in policy.rules.items()},
        claims={k: sorted(v) for k, v in policy.claim_requirements.items()},
        delta=sorted(policy.introduced_obligations),
        issuers={k: dict(key=v.key.public_bytes(serialization.Encoding.Raw,
            serialization.PublicFormat.Raw).hex(), boundary=v.boundary,
            claims=sorted(v.permitted_claims), schemas=sorted(v.allowed_schemas),
            revoked=v.revoked) for k, v in policy.accepted_issuers.items()})
    return "sha256:" + hashlib.sha256(b"DARM-E38-policy-v1\x00" + canonical(body)).hexdigest()


@dataclass(frozen=True)
class TrustedReliance:
    """Provisioned by consumer, never constructed from the incoming request."""
    claim_id: str
    request_id: str
    target: str
    subject_digest: str
    policy_fingerprint: str


def _unique(pairs):
    obj = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError("duplicate-json-field")
        obj[key] = value
    return obj


def _reject_constant(value):
    raise ValueError("nonfinite-json-number")


def load_request(raw: bytes) -> dict:
    if type(raw) is not bytes or not raw or len(raw) > MAX_REQUEST_BYTES:
        raise ValueError("invalid-request-bytes")
    obj = json.loads(raw, object_pairs_hook=_unique, parse_constant=_reject_constant)
    if not isinstance(obj, dict):
        raise ValueError("invalid-request-object")
    return obj


class PinnedRelianceVerifier:
    """Single-pass verification profile with a mandatory protected local pin.

    Snapshot each trusted policy once per verifier instance. Rotation requires
    a new instance and a freshly provisioned TrustedReliance fingerprint.
    This class verifies a decision. It does not execute a subsequent effect.
    """
    def __init__(self, policy: Policy, trusted: TrustedReliance,
                 store: MonotonicWitnessStore, *, admission_core=admit_core):
        self.policy = freeze_policy(policy)
        if not isinstance(trusted, TrustedReliance) or any(
                type(x) is not str or not x for x in (
                    trusted.claim_id, trusted.request_id, trusted.target,
                    trusted.subject_digest, trusted.policy_fingerprint)):
            raise ValueError("invalid-trusted-reliance")
        if trusted.claim_id not in self.policy.claim_requirements:
            raise ValueError("unknown-consumer-claim")
        if policy_fingerprint(self.policy) != trusted.policy_fingerprint:
            raise ValueError("consumer-policy-fingerprint-mismatch")
        if not isinstance(store, MonotonicWitnessStore):
            raise ValueError("protected-pin-store-required")
        if not callable(admission_core):
            raise ValueError("admission-core-required")
        self.admission_core = admission_core
        self.trusted = trusted
        self.store = store

    def decide_json(self, raw_request: bytes, now: int, attestation: bytes,
                    content: bytes, audit: bytes, checkpoints: bytes) -> Verdict:
        try:
            request = load_request(raw_request)
        except (ValueError, TypeError, UnicodeError, RecursionError):
            return Verdict(False, ("consumer:malformed-request",), (), (), False)
        return self.decide(request, now, attestation, content, audit, checkpoints)

    def decide(self, request: dict, now: int, attestation: bytes, content: bytes,
               audit: bytes, checkpoints: bytes) -> Verdict:
        flag = isinstance(request, dict) and request.get("action_authorized") is True
        def refuse(reason):
            return Verdict(False, (reason,), (), (), flag)
        if type(now) is not int or now < 0:
            return refuse("consumer:invalid-trusted-clock")
        # Copy JSON data once. Reject duplicate fields at decide_json entry.
        try:
            request = load_request(canonical(request))
        except (ValueError, TypeError, UnicodeError, RecursionError):
            return refuse("consumer:malformed-request")
        for field in ("claim_id", "request_id", "subject_digest"):
            if request.get(field) != getattr(self.trusted, field):
                return refuse("consumer:" + field + "-mismatch")
        expected = TrustedArtifact(self.trusted.request_id, self.trusted.target)
        try:
            # Use one stored witness while holding the existing stable lock.
            with self.store._locked():
                stored = self.store._read()
                if stored is None:
                    return refuse("pin:not-enrolled")
                pin = stored[1]  # already cryptographically verified by _read
                artifact = verify_guard_artifact(attestation, content, expected,
                                                 self.store.guard_public_ring)
                if not artifact.verified:
                    return refuse("guard:" + artifact.reason)
                if "sha256:" + artifact.digest != self.trusted.subject_digest:
                    return refuse("consumer:observed-subject-mismatch")
                snapshot = verify_snapshot(audit, checkpoints, self.store.guard_public_ring,
                                           expected, artifact.digest)
                if not snapshot.verified:
                    return refuse("audit:" + snapshot.reason)
                rows = _parse_jsonl(audit)
                if len(rows) < pin.count:
                    return refuse("pin:audit-behind-stored-pin")
                if (rows[0]["entry_hash"] != pin.genesis or
                        rows[pin.count - 1]["entry_hash"] != pin.head):
                    return refuse("pin:audit-does-not-extend-stored-pin")
                return decide(request, self.policy, now,
                              admission_core=self.admission_core)
        except PinError as exc:
            return refuse("pin:" + str(exc))
        except (ValueError, TypeError, UnicodeError, KeyError, AttributeError,
                RecursionError, OverflowError):
            return refuse("consumer:malformed-evidence")
