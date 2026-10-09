"""E38 Stage 4: independent *witness-pinned* audit rollback resistance.

A caller-supplied, independently trusted witness public key authenticates a
pinned DARM Guard-signed checkpoint. A fully verified supplied log must
extend that pin, or reliance is refused. The witness must come from an
independent channel. A signature alone cannot prove the newest world state.

NOT a claim of live freshness, complete mediation, remote semantic truth,
or Lean-to-Python implementation refinement. Only write_file is covered by
the existing signed-snapshot adapter.
"""
from __future__ import annotations

from dataclasses import dataclass
import json
from typing import Any, Mapping

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import serialization

from guard_audit_bridge import _parse_jsonl, decide_with_guard_audit, verify_snapshot
from guard_bridge import TrustedArtifact
from verifier import Policy, Verdict

WITNESS_DOMAIN = b"DARM-E38-independent-checkpoint-witness-v1\x00"
MAX_WITNESS_BYTES = 8_192


@dataclass(frozen=True)
class WitnessResult:
    verified: bool
    reason: str
    count: int = 0
    genesis: str | None = None
    head: str | None = None


class _DuplicateField(ValueError):
    pass


def _unique(pairs):
    found = {}
    for k, v in pairs:
        if k in found:
            raise _DuplicateField(k)
        found[k] = v
    return found


def _is_hex(value, size):
    return isinstance(value, str) and len(value) == size and all(c in "0123456789abcdef" for c in value)


def _canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def verify_trusted_witness(raw_witness: bytes, witness_public: Any, guard_public_ring: Any) -> WitnessResult:
    """Authenticate one pinned checkpoint with a SEPARATELY TRUSTED witness key.

    The key must be supplied by trusted local configuration, not extracted from
    the untrusted witness or supplied by an agent. Witness signature and Guard
    checkpoint signatures are checked under distinct verification keys.
    """
    if not isinstance(raw_witness, bytes) or not raw_witness or len(raw_witness) > MAX_WITNESS_BYTES:
        return WitnessResult(False, "invalid-witness-bytes")
    if not callable(getattr(witness_public, "verify", None)) or not callable(
        getattr(witness_public, "public_bytes", None)
    ):
        return WitnessResult(False, "missing-trusted-witness-public-key")
    if not callable(getattr(guard_public_ring, "verify_checkpoint", None)) or not callable(
        getattr(guard_public_ring, "can_sign", None)
    ) or guard_public_ring.can_sign():
        return WitnessResult(False, "invalid-guard-public-ring")
    try:
        raw_key = witness_public.public_bytes(
            serialization.Encoding.Raw, serialization.PublicFormat.Raw
        )
        # Reusing a DARM Guard signing key as an external witness signing key
        # defeats role separation, regardless of how the signed object is named.
        guard_keys = list(getattr(guard_public_ring, "publics", {}).values())
        if raw_key in guard_keys:
            return WitnessResult(False, "witness-and-broker-key-roles-overlap")
        envelope = json.loads(raw_witness, object_pairs_hook=_unique)
        if not isinstance(envelope, dict) or set(envelope) != {"v", "checkpoint", "signature"}:
            return WitnessResult(False, "invalid-witness-schema")
        if type(envelope["v"]) is not int or envelope["v"] != 1:
            return WitnessResult(False, "invalid-witness-version")
        cp = envelope["checkpoint"]
        if not isinstance(cp, dict) or set(cp) != {"v", "genesis", "count", "head", "kid", "sig"}:
            return WitnessResult(False, "invalid-broker-checkpoint-schema")
        if not (type(cp["v"]) is int and cp["v"] == 1 and
                type(cp["count"]) is int and 1 <= cp["count"] <= 10_000 and
                _is_hex(cp["genesis"], 64) and _is_hex(cp["head"], 64) and
                _is_hex(cp["kid"], 16) and _is_hex(cp["sig"], 128)):
            return WitnessResult(False, "invalid-broker-checkpoint-fields")
        signature = envelope["signature"]
        if not _is_hex(signature, 128):
            return WitnessResult(False, "invalid-witness-signature-format")
        body = {"v": 1, "checkpoint": cp}
        witness_public.verify(bytes.fromhex(signature), WITNESS_DOMAIN + _canonical(body))
        verified, _ = guard_public_ring.verify_checkpoint(cp)
        if not verified:
            return WitnessResult(False, "broker-checkpoint-signature-invalid")
        return WitnessResult(True, "separately-signed-broker-checkpoint", cp["count"], cp["genesis"], cp["head"])
    except InvalidSignature:
        return WitnessResult(False, "witness-signature-invalid")
    except (UnicodeError, ValueError, TypeError, KeyError, AttributeError, RecursionError, OverflowError):
        return WitnessResult(False, "malformed-witness-or-verification-error")


def verify_extension(raw_audit: bytes, raw_checkpoints: bytes, public_ring: Any,
                     trusted: TrustedArtifact, expected_digest: str,
                     raw_witness: bytes, witness_public: Any) -> WitnessResult:
    """Require fully checkpointed audit snapshot to extend the witnessed pin.

    No `latest` claim: the caller must maintain an independently updated pin.
    The signed witness can attest an earlier state; replay of that authentic
    witness is detectable only against a *newer trusted* pin.
    """
    witness = verify_trusted_witness(raw_witness, witness_public, public_ring)
    if not witness.verified:
        return witness
    snap = verify_snapshot(raw_audit, raw_checkpoints, public_ring, trusted, expected_digest)
    if not snap.verified:
        return WitnessResult(False, "audit:" + snap.reason)
    try:
        rows = _parse_jsonl(raw_audit)
    except (UnicodeError, ValueError, TypeError, RecursionError):
        return WitnessResult(False, "malformed-audit")
    if len(rows) < witness.count:
        return WitnessResult(False, "audit-behind-trusted-witness", len(rows))
    if rows[0].get("entry_hash") != witness.genesis:
        return WitnessResult(False, "audit-genesis-differs-from-witness", len(rows))
    if rows[witness.count - 1].get("entry_hash") != witness.head:
        return WitnessResult(False, "audit-does-not-extend-witness", len(rows))
    return WitnessResult(True, "audit-extends-independently-witnessed-checkpoint", len(rows),
                         witness.genesis, snap.head)


def decide_with_witness(
    request: Mapping[str, Any], policy: Policy, now: int,
    raw_attestation: bytes, observed_content: bytes, trusted: TrustedArtifact,
    public_ring: Any, raw_audit: bytes, raw_checkpoints: bytes,
    raw_witness: bytes, witness_public: Any,
) -> Verdict:
    """Conjunction of witnessed log extension and existing signed-snapshot gate."""
    from guard_bridge import verify_guard_artifact

    flag = isinstance(request, Mapping) and request.get("action_authorized") is True
    artifact = verify_guard_artifact(raw_attestation, observed_content, trusted, public_ring)
    if not artifact.verified:
        return Verdict(False, ("guard:" + artifact.reason,), (), (), flag)
    extension = verify_extension(
        raw_audit, raw_checkpoints, public_ring, trusted,
        artifact.digest, raw_witness, witness_public
    )
    if not extension.verified:
        return Verdict(False, ("witness:" + extension.reason,), (), (), flag)
    return decide_with_guard_audit(
        request, policy, now, raw_attestation, observed_content,
        trusted, public_ring, raw_audit, raw_checkpoints
    )
