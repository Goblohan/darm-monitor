"""E38 experimental adapter for actual DARM Guard attestation-v2 artifacts.

This adapter authenticates a broker-signed request/target/digest tuple and
checks it against *trusted* request/path expectations and observed bytes.
The tuple alone is NOT evidence that the effect was admitted, the audit log is
current, or a downstream semantic claim is warranted. Semantic claims must
separately pass the existing HDB-1E verifier's issuer and policy checks.

Requires import of the actual local darm_guard.attest.KeyRing implementation.
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Mapping

from verifier import Policy, Verdict, decide


@dataclass(frozen=True)
class TrustedArtifact:
    """Must come from a trusted receiver or a verified ledger, never an agent."""
    request_id: str
    target: str


@dataclass(frozen=True)
class GuardArtifactCheck:
    verified: bool
    reason: str
    digest: str | None = None


class _DuplicateKey(ValueError):
    pass


def _pairs_no_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    obj: dict[str, Any] = {}
    for name, value in pairs:
        if name in obj:
            raise _DuplicateKey("duplicate field")
        obj[name] = value
    return obj


def verify_guard_artifact(
    raw_attestation: bytes,
    observed_content: bytes,
    trusted: TrustedArtifact,
    public_ring: Any,
) -> GuardArtifactCheck:
    """Verify actual Guard v2 signature, exact tuple binding, and observed bytes.

    Does not verify log freshness, kernel admission, or semantic truth.
    The given `trusted` expectation and public key ring are trust anchors.
    """
    if not isinstance(trusted, TrustedArtifact) or not all(
        isinstance(x, str) and x for x in (trusted.request_id, trusted.target)
    ):
        return GuardArtifactCheck(False, "invalid-trusted-expectation")
    if not isinstance(raw_attestation, bytes) or not raw_attestation or len(raw_attestation) > 16_384:
        return GuardArtifactCheck(False, "invalid-attestation-bytes")
    if not isinstance(observed_content, bytes):
        return GuardArtifactCheck(False, "invalid-observed-content")
    if public_ring is None or not callable(getattr(public_ring, "verify", None)):
        return GuardArtifactCheck(False, "missing-trusted-public-key-ring")
    # KeyRing.public_only(): prevent accidentally treating a local signing key
    # as a prerequisite for a read-only downstream check.
    if not callable(getattr(public_ring, "can_sign", None)) or public_ring.can_sign():
        return GuardArtifactCheck(False, "not-a-public-only-key-ring")

    try:
        envelope = json.loads(raw_attestation, object_pairs_hook=_pairs_no_duplicate_keys)
    except (UnicodeDecodeError, ValueError, TypeError, RecursionError):
        return GuardArtifactCheck(False, "malformed-or-ambiguous-attestation")
    if not isinstance(envelope, dict) or set(envelope) != {"v", "rid", "target", "digest", "kid", "sig"}:
        return GuardArtifactCheck(False, "invalid-attestation-schema")
    if type(envelope["v"]) is not int or envelope["v"] != 2:
        return GuardArtifactCheck(False, "unsupported-attestation-version")
    if any(not isinstance(envelope[k], str) or not envelope[k] for k in ("rid", "target", "digest", "kid", "sig")):
        return GuardArtifactCheck(False, "invalid-attestation-fields")
    # Guard v2 currently signs a pipe-delimited tuple rather than a length-prefixed
    # encoding. Refuse delimiters in the variable identity fields to avoid
    # multiple (rid, target) tuples mapping to the same signed message bytes.
    if "|" in envelope["rid"] or "|" in envelope["target"]:
        return GuardArtifactCheck(False, "ambiguous-guard-delimited-identity")
    digest = hashlib.sha256(observed_content).hexdigest()

    # This is the real DARM Guard API. It checks its own `darm-attest-v2`
    # domain-separated Ed25519 signature with the public key selected by kid.
    try:
        verified, error = public_ring.verify(raw_attestation)
    except (TypeError, ValueError, KeyError, AttributeError):
        return GuardArtifactCheck(False, "guard-signature-verification-error")
    if verified is None or error is not None or verified != envelope:
        return GuardArtifactCheck(False, "guard-signature-untrusted-or-invalid")
    if envelope["rid"] != trusted.request_id:
        return GuardArtifactCheck(False, "guard-request-binding-mismatch")
    if envelope["target"] != trusted.target:
        return GuardArtifactCheck(False, "guard-target-binding-mismatch")
    if envelope["digest"] != digest:
        return GuardArtifactCheck(False, "guard-content-digest-mismatch")
    return GuardArtifactCheck(True, "guard-artifact-signature-and-bytes-match", digest)


def decide_with_guard_artifact(
    request: Mapping[str, Any],
    policy: Policy,
    now: int,
    raw_attestation: bytes,
    observed_content: bytes,
    trusted: TrustedArtifact,
    public_ring: Any,
) -> Verdict:
    """Conjunction of DARM Guard artifact check and independent HDB-1E gate.

    An accepted report does NOT imply current log state, action authorization,
    external-world truth, or real-world complete mediation. Those require
    independently verified evidence and a future integration step.
    """
    checked = verify_guard_artifact(raw_attestation, observed_content, trusted, public_ring)
    action_flag = isinstance(request, Mapping) and request.get("action_authorized") is True
    if not checked.verified:
        return Verdict(False, ("guard:" + checked.reason,), (), (), action_flag)
    if not isinstance(request, Mapping):
        return Verdict(False, ("invalid-request",), (), (), action_flag)
    if request.get("request_id") != trusted.request_id:
        return Verdict(False, ("guard:reliance-request-mismatch",), (), (), action_flag)
    if request.get("subject_digest") != "sha256:" + checked.digest:
        return Verdict(False, ("guard:reliance-subject-mismatch",), (), (), action_flag)
    # This independent decision must verify HDB-1E evidence signed under its
    # own permitted issuers. Guard signatures NEVER mint its claim predicates.
    return decide(request, policy, now)
