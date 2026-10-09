"""E38 Stage 5: locally persisted, witness-verified monotonic checkpoint pin.

Research prototype. Assumes a trusted, owner-private persistent directory and
trusted public keys, and an independently delivered checkpoint witness.
A hostile host that rolls back BOTH the trusted directory and its keys is NOT
covered. There is no live freshness oracle, service, or Lean/Python proof.
Only the previously scoped write-file relying gate is provided.
"""
from __future__ import annotations

import base64
from contextlib import contextmanager
from dataclasses import dataclass
import fcntl
import hashlib
import json
import os
from pathlib import Path
import stat
import tempfile
from typing import Any, Mapping

from guard_audit_bridge import _parse_jsonl, _valid_hash
from guard_witness_bridge import verify_trusted_witness, decide_with_witness
from guard_bridge import TrustedArtifact
from verifier import Policy, Verdict

ZERO = "0" * 64
MAX_STORE_BYTES = 16_384


@dataclass(frozen=True)
class PinResult:
    ok: bool
    reason: str
    count: int = 0
    head: str | None = None


class PinError(Exception):
    pass


def _unique(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise PinError("duplicate-stored-field")
        out[k] = v
    return out


def _valid_checkpoint(cp: Any) -> bool:
    def hexd(s, n):
        return isinstance(s, str) and len(s) == n and all(c in "0123456789abcdef" for c in s)
    return (isinstance(cp, dict) and set(cp) == {"v", "genesis", "count", "head", "kid", "sig"}
            and type(cp["v"]) is int and cp["v"] == 1
            and type(cp["count"]) is int and cp["count"] >= 1
            and hexd(cp["genesis"], 64) and hexd(cp["head"], 64)
            and hexd(cp["kid"], 16) and hexd(cp["sig"], 128))


def _verified_history(audit_raw: bytes, checkpoints_raw: bytes, public_ring: Any,
                      witnessed_raw: bytes, witness_public: Any):
    """Validate a whole logged history and witness independent of target.

    Rejects invalid or off-branch checkpoints, even if signed. A full-log
    signed checkpoint and the witnessed checkpoint must both be included.
    The witness must name the log's current head; this prevents a silent
    pin advancement to a partial, unrelated log.
    """
    witness = verify_trusted_witness(witnessed_raw, witness_public, public_ring)
    if not witness.verified:
        raise PinError("witness:" + witness.reason)
    try:
        rows = _parse_jsonl(audit_raw)
        cps = _parse_jsonl(checkpoints_raw)
    except (ValueError, UnicodeError, TypeError, RecursionError):
        raise PinError("invalid-audit-or-checkpoints")
    prev = ZERO
    for i, row in enumerate(rows):
        h = row.get("entry_hash")
        if not _valid_hash(h) or row.get("prev_hash") != prev:
            raise PinError("broken-log-chain")
        body = {k: v for k, v in row.items() if k != "entry_hash"}
        if hashlib.sha256(json.dumps(body, sort_keys=True).encode()).hexdigest() != h:
            raise PinError("broken-log-hash")
        prev = h
    genesis = rows[0]["entry_hash"]
    matched = False
    full = False
    for cp in cps:
        if not _valid_checkpoint(cp) or cp["count"] > len(rows):
            raise PinError("invalid-checkpoint")
        try:
            good, _ = public_ring.verify_checkpoint(cp)
        except (ValueError, TypeError, AttributeError, KeyError):
            good = False
        if not good:
            raise PinError("invalid-checkpoint-signature")
        if cp["genesis"] != genesis or rows[cp["count"] - 1]["entry_hash"] != cp["head"]:
            raise PinError("checkpoint-off-audit-history")
        if cp["count"] == len(rows) and cp["head"] == prev:
            full = True
        if cp["count"] == witness.count and cp["genesis"] == witness.genesis and cp["head"] == witness.head:
            matched = True
    if not full:
        raise PinError("missing-full-snapshot-checkpoint")
    if not matched:
        raise PinError("witnessed-checkpoint-not-in-snapshot")
    if witness.count != len(rows) or witness.head != prev or witness.genesis != genesis:
        raise PinError("witness-not-at-current-snapshot-head")
    return rows, witness


class MonotonicWitnessStore:
    """Owner-private local state, guarded by a stable flock and atomic replace.

    This only protects against stale *supplied* witnesses while the trusted
    state directory survives unchanged. Host compromise, disk rollback,
    deletion of state and reenrollment, or compromised trusted keys are not
    addressed. An operator should guard initial enrollment out of band.
    """
    def __init__(self, root: Path | str, witness_public: Any, guard_public_ring: Any):
        self.root = Path(root)
        self.witness_public = witness_public
        self.guard_public_ring = guard_public_ring
        self.state = self.root / "witness-pin.json"
        self.lock = self.root / "witness-pin.lock"

    @contextmanager
    def _locked(self):
        try:
            d = os.lstat(self.root)
            if (not stat.S_ISDIR(d.st_mode) or stat.S_ISLNK(d.st_mode)
                or d.st_uid != os.geteuid() or stat.S_IMODE(d.st_mode) & 0o077):
                raise PinError("untrusted-state-directory")
            fd = os.open(self.lock, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
            try:
                fs = os.fstat(fd)
                if (not stat.S_ISREG(fs.st_mode) or fs.st_uid != os.geteuid()
                    or stat.S_IMODE(fs.st_mode) & 0o077):
                    raise PinError("untrusted-lock-file")
                fcntl.flock(fd, fcntl.LOCK_EX)
                yield
            finally:
                os.close(fd)
        except OSError as exc:
            raise PinError("state-storage-error:" + type(exc).__name__) from exc

    def _read(self):
        try:
            fd = os.open(self.state, os.O_RDONLY | os.O_NOFOLLOW)
        except FileNotFoundError:
            return None
        except OSError as exc:
            raise PinError("invalid-state-file:" + type(exc).__name__) from exc
        try:
            fs = os.fstat(fd)
            if (not stat.S_ISREG(fs.st_mode) or fs.st_uid != os.geteuid()
                or stat.S_IMODE(fs.st_mode) & 0o077 or fs.st_size > MAX_STORE_BYTES):
                raise PinError("invalid-state-file")
            with os.fdopen(fd, "rb") as f:
                fd = -1
                raw = f.read(MAX_STORE_BYTES + 1)
        finally:
            if fd >= 0:
                os.close(fd)
        if len(raw) > MAX_STORE_BYTES:
            raise PinError("oversized-state-file")
        try:
            obj = json.loads(raw, object_pairs_hook=_unique)
            if not isinstance(obj, dict) or set(obj) != {"v", "witness_b64"} or type(obj["v"]) is not int or obj["v"] != 1:
                raise PinError("invalid-state-schema")
            if not isinstance(obj["witness_b64"], str):
                raise PinError("invalid-state-witness")
            witness_raw = base64.b64decode(obj["witness_b64"], validate=True)
        except (UnicodeError, ValueError, TypeError, RecursionError) as exc:
            raise PinError("malformed-stored-witness") from exc
        pin = verify_trusted_witness(witness_raw, self.witness_public, self.guard_public_ring)
        if not pin.verified:
            raise PinError("stored-" + pin.reason)
        return witness_raw, pin

    def _write(self, raw_witness: bytes):
        obj = {"v": 1, "witness_b64": base64.b64encode(raw_witness).decode("ascii")}
        data = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()
        if len(data) > MAX_STORE_BYTES:
            raise PinError("state-too-large")
        temp_path = None
        try:
            fd, temp_path = tempfile.mkstemp(prefix=".pin-new-", dir=self.root)
            with os.fdopen(fd, "wb") as f:
                f.write(data)
                f.flush()
                os.fsync(f.fileno())
            os.replace(temp_path, self.state)
            temp_path = None
            dir_fd = os.open(self.root, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(dir_fd)
            finally:
                os.close(dir_fd)
        except OSError as exc:
            raise PinError("state-write-failed:" + type(exc).__name__) from exc
        finally:
            if temp_path is not None:
                try:
                    os.unlink(temp_path)
                except FileNotFoundError:
                    pass

    def observe(self) -> PinResult:
        """Read the current pin; missing or corrupt state never means fresh."""
        try:
            with self._locked():
                previous = self._read()
                if previous is None:
                    return PinResult(False, "not-enrolled")
                return PinResult(True, "pinned", previous[1].count, previous[1].head)
        except PinError as exc:
            return PinResult(False, str(exc))

    def advance(self, audit: bytes, checkpoints: bytes, witnessed: bytes,
                *, enroll: bool = False) -> PinResult:
        """Bootstrap only with explicit enroll=True; then strictly nondecreasing.

        A witness received from an agent may be authentic but old. It cannot
        lower this store. A higher count must extend the pinned exact hash.
        """
        try:
            with self._locked():
                prev = self._read()
                if prev is None and not enroll:
                    raise PinError("enrollment-required")
                rows, current = _verified_history(audit, checkpoints, self.guard_public_ring,
                                                  witnessed, self.witness_public)
                if prev is not None:
                    old = prev[1]
                    if current.genesis != old.genesis:
                        raise PinError("different-genesis")
                    if current.count < old.count:
                        raise PinError("rollback-below-pinned-count")
                    if rows[old.count - 1]["entry_hash"] != old.head:
                        raise PinError("fork-does-not-extend-stored-pin")
                    if current.count == old.count:
                        # Existing pin always wins; no rewrite even with a
                        # differently encoded but equivalent witness.
                        return PinResult(True, "unchanged", old.count, old.head)
                self._write(witnessed)
                return PinResult(True, "enrolled" if prev is None else "advanced",
                                 current.count, current.head)
        except PinError as exc:
            return PinResult(False, str(exc))

    def decide(self, request: Mapping[str, Any], policy: Policy, now: int,
               attestation: bytes, content: bytes, trusted: TrustedArtifact,
               audit: bytes, checkpoints: bytes) -> Verdict:
        """Never accept a witness selected by the calling agent.

        Uses the highest locally pinned witness under the store lock.
        The snapshot, signed checkpoint and semantic warrant are still
        checked by Stage 4's verifier. This is a snapshot-level statement.
        """
        flag = isinstance(request, Mapping) and request.get("action_authorized") is True
        try:
            with self._locked():
                stored = self._read()
                if stored is None:
                    raise PinError("not-enrolled")
                return decide_with_witness(
                    request, policy, now, attestation, content, trusted,
                    self.guard_public_ring, audit, checkpoints,
                    stored[0], self.witness_public,
                )
        except PinError as exc:
            return Verdict(False, ("pin:" + str(exc),), (), (), flag)
