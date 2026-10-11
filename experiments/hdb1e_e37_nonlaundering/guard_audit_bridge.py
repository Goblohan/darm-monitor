"""E38 experimental signed-snapshot audit adapter for DARM Guard v0.28.x.

Checks: real Guard v2 artifact signature / bytes (guard_bridge), complete broker
hash chain, separately signed external checkpoint matching the *whole* audit
snapshot, admitted preparation, successful exact write outcome, and absence of
superseding or unresolved later effects on the governed target.

This is NOT a proof of the Python broker, live freshness, kernel proof replay,
external truth, or complete mediation. The audit and checkpoint must come from
independently trusted channels, rather than values supplied by an agent.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from typing import Any, Mapping

from guard_bridge import TrustedArtifact, decide_with_guard_artifact, verify_guard_artifact
from verifier import Policy, Verdict

_MAX_BYTES = 16 * 1024 * 1024
_MAX_ENTRIES = 10000
_ZERO = "0" * 64


@dataclass(frozen=True)
class AuditResult:
    verified: bool
    reason: str
    count: int = 0
    head: str | None = None


class _Ambiguous(ValueError):
    pass


def _unique(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise _Ambiguous("duplicate json key")
        out[k] = v
    return out


def _parse_jsonl(raw: bytes):
    if not isinstance(raw, bytes) or not raw or len(raw) > _MAX_BYTES:
        raise ValueError("empty or oversized input")
    rows = raw.splitlines()
    if not rows or len(rows) > _MAX_ENTRIES or any(not r.strip() for r in rows):
        raise ValueError("invalid record count")
    def reject_constant(value):
        raise ValueError("nonfinite-json-number")
    data = [json.loads(r, object_pairs_hook=_unique, parse_constant=reject_constant) for r in rows]
    if any(not isinstance(x, dict) for x in data):
        raise ValueError("not an object")
    return data


def _state_present_digest(s: Any, digest: str) -> bool:
    return isinstance(s, list) and len(s) == 2 and s == ["present", digest]


def _valid_hash(s: Any) -> bool:
    return isinstance(s, str) and len(s) == 64 and all(c in "0123456789abcdef" for c in s)


def verify_snapshot(
    raw_audit: bytes,
    raw_checkpoints: bytes,
    public_ring: Any,
    trusted: TrustedArtifact,
    expected_digest: str,
) -> AuditResult:
    """Verify authorization/effect attribution *as of a signed log snapshot*.

    The external checkpoint is required to cover the entire supplied log.
    It is the caller's responsibility to obtain the most recent checkpoint
    from a trusted independent sink and to know whether it is sufficiently
    recent. This function cannot detect withheld later records/checkpoints.
    """
    if (not isinstance(trusted, TrustedArtifact)
        or not isinstance(trusted.target, str)
        or not isinstance(trusted.request_id, str)
        or not _valid_hash(expected_digest)):
        return AuditResult(False, "invalid-expected-identity")
    if not callable(getattr(public_ring, "verify_checkpoint", None)):
        return AuditResult(False, "missing-checkpoint-verifier")
    if not callable(getattr(public_ring, "can_sign", None)) or public_ring.can_sign():
        return AuditResult(False, "not-a-public-only-ring")
    try:
        events = _parse_jsonl(raw_audit)
        cps = _parse_jsonl(raw_checkpoints)
    except (UnicodeError, ValueError, TypeError, RecursionError):
        return AuditResult(False, "malformed-audit-or-checkpoint")

    prev = _ZERO
    for i, e in enumerate(events):
        entry_hash = e.get("entry_hash")
        if not _valid_hash(entry_hash) or e.get("prev_hash") != prev:
            return AuditResult(False, "broken-audit-chain", i)
        body = {k: v for k, v in e.items() if k != "entry_hash"}
        digest = hashlib.sha256(json.dumps(body, sort_keys=True).encode()).hexdigest()
        if entry_hash != digest:
            return AuditResult(False, "broken-audit-chain", i)
        prev = entry_hash

    # Refuse malformed/invalid checkpoint entries rather than silently
    # ignoring a malicious or misdirected external-sink record.
    for cp in cps:
        if (set(cp) != {"v", "genesis", "count", "head", "kid", "sig"}
            or type(cp.get("v")) is not int or cp["v"] != 1
            or type(cp.get("count")) is not int or cp["count"] <= 0
            or cp["count"] > len(events)
            or not _valid_hash(cp.get("genesis"))
            or not _valid_hash(cp.get("head"))
            or not isinstance(cp.get("kid"), str) or len(cp["kid"]) != 16
            or any(c not in "0123456789abcdef" for c in cp["kid"])
            or not isinstance(cp.get("sig"), str) or len(cp["sig"]) != 128
            or any(c not in "0123456789abcdef" for c in cp["sig"])):
            return AuditResult(False, "invalid-checkpoint-schema", len(events), prev)
        try:
            ok, _ = public_ring.verify_checkpoint(cp)
        except (ValueError, TypeError, KeyError, AttributeError):
            ok = False
        if not ok:
            return AuditResult(False, "checkpoint-signature-invalid", len(events), prev)
        if (cp["genesis"] != events[0]["entry_hash"] or
                cp["head"] != events[cp["count"] - 1]["entry_hash"]):
            return AuditResult(False, "checkpoint-off-audit-history", len(events), prev)
    full_cp = [c for c in cps if c["count"] == len(events)
               and c["genesis"] == events[0]["entry_hash"] and c["head"] == prev]
    if not full_cp:
        return AuditResult(False, "no-full-snapshot-checkpoint", len(events), prev)

    # Require a decision record with the exact admitted invocation. An
    # outcome or attestation by itself cannot serve as kernel-admission proof.
    rid = trusted.request_id
    target = trusted.target
    own = [(i, e) for i, e in enumerate(events) if e.get("request_id") == rid]
    prepared = [(i, e) for i, e in own if e.get("event") == "prepared"]
    if len(prepared) != 1:
        return AuditResult(False, "missing-or-duplicate-preparation", len(events), prev)
    prep_index, prep = prepared[0]
    inv_hash = prep.get("invocation_hash")
    if not (_valid_hash(inv_hash) and prep.get("decision") == "admit"
            and prep.get("tool") == "write_file" and prep.get("target") == target
            and _state_present_digest(prep.get("intended_state"), expected_digest)):
        return AuditResult(False, "admission-or-intended-state-mismatch", len(events), prev)
    outcomes = [(i, e) for i, e in own if e.get("event") == "outcome"]
    if len(outcomes) != 1:
        return AuditResult(False, "missing-or-duplicate-outcome", len(events), prev)
    out_index, outcome = outcomes[0]
    if not (out_index > prep_index
            and outcome.get("tool") == "write_file"
            and outcome.get("target") == target
            and outcome.get("decision") == "admit"
            and outcome.get("effect") == "succeeded"
            and outcome.get("executed") is True
            and outcome.get("reconciliation") == "confirmedSuccess"
            and outcome.get("invocation_hash") == inv_hash
            and _state_present_digest(outcome.get("intended_state"), expected_digest)
            and _state_present_digest(outcome.get("observed_state"), expected_digest)):
        return AuditResult(False, "effect-not-confirmed-or-not-matched", len(events), prev)
    # If there are additional records for the same request implying different
    # outcomes, the trace is ambiguous. A genuine later write/rename/delete or
    # an unresolved later prepared operation at the same location similarly
    # blocks current reliance. The target can be affected via rename.source.
    for i, e in enumerate(events):
        if i <= out_index:
            continue
        if e.get("request_id") == rid and e.get("event") in ("prepared", "outcome", "reconciled"):
            return AuditResult(False, "later-request-status-ambiguous", len(events), prev)
        if e.get("target") != target and e.get("source") != target:
            continue
        if e.get("event") == "prepared" and e.get("decision") == "admit":
            # Might be unresolved, or may have completed later. Conservative.
            return AuditResult(False, "later-operation-possibly-supersedes", len(events), prev)
        if e.get("event") in ("outcome", "reconciled") and (
                e.get("effect") == "succeeded"
                or e.get("reconciliation") == "confirmedSuccess"
                or e.get("effect") == "unknown"
                or e.get("reconciliation") == "unresolved"):
            return AuditResult(False, "later-operation-supersedes", len(events), prev)

    return AuditResult(True, "matched-current-write-as-of-signed-snapshot", len(events), prev)


def decide_with_guard_audit(
    request: Mapping[str, Any], policy: Policy, now: int,
    raw_attestation: bytes, observed_content: bytes,
    trusted: TrustedArtifact, public_ring: Any,
    raw_audit: bytes, raw_checkpoints: bytes,
) -> Verdict:
    """Conjunction: authentic artifact + anchored causal record + HDB warrant.

    Does not prove semantic truth, runtime kernel implementation refinement,
    or freshness beyond the trusted snapshot. `request.action_authorized`
    remains a mock field and is NEVER a source of admission.
    """
    flag = isinstance(request, Mapping) and request.get("action_authorized") is True
    artifact = verify_guard_artifact(raw_attestation, observed_content, trusted, public_ring)
    if not artifact.verified:
        return Verdict(False, ("guard:" + artifact.reason,), (), (), flag)
    audit = verify_snapshot(raw_audit, raw_checkpoints, public_ring, trusted, artifact.digest)
    if not audit.verified:
        return Verdict(False, ("audit:" + audit.reason,), (), (), flag)
    return decide_with_guard_artifact(
        request, policy, now, raw_attestation, observed_content, trusted, public_ring
    )
