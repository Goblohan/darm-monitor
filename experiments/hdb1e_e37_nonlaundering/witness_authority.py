"""E38 experimental independently hosted witness *authority* (NOT deployment evidence).

A single Guard audit stream is pinned by the first explicitly enrolled checkpoint.
Later checkpoints require a hash-verified suffix extending the exact stored head.
An offline witness key signs v1 compatible receipts. A distinct v2 nonce response
allows a consumer to query this authority's latest *acknowledged* state.

Security assumptions: exclusive administrative/key domain from Guard, trusted public
ring, persistent storage immune to Guard-controlled deletion/rollback, and authenticated
network channel. No guarantee that Guard submits every event. No production claim.
"""
from __future__ import annotations

import fcntl
import hashlib
import json
import os
import stat
import tempfile
from contextlib import contextmanager
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from guard_audit_bridge import _valid_hash
from guard_witness_bridge import WITNESS_DOMAIN, _canonical, verify_trusted_witness

ONLINE_DOMAIN = b"DARM-E38-witness-online-v2\x00"
MAX_APPEND_BYTES = 16 * 1024 * 1024
MAX_EVENTS = 10_000
ZERO = "0" * 64


class WitnessRefusal(ValueError):
    pass


def _pairs_unique(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise WitnessRefusal("duplicate-field")
        out[key] = value
    return out


def _no_constant(_value):
    raise WitnessRefusal("nonfinite-number")


def _load(raw: bytes, *, maximum=MAX_APPEND_BYTES):
    if type(raw) is not bytes or not raw or len(raw) > maximum:
        raise WitnessRefusal("malformed-or-oversized-json")
    try:
        return json.loads(raw, object_pairs_hook=_pairs_unique, parse_constant=_no_constant)
    except (UnicodeError, ValueError, TypeError, RecursionError, OverflowError) as exc:
        raise WitnessRefusal("malformed-json") from exc


def _valid_cp(cp):
    hexd = lambda value, n: isinstance(value, str) and len(value) == n and all(c in "0123456789abcdef" for c in value)
    return (type(cp) is dict and set(cp) == {"v", "genesis", "count", "head", "kid", "sig"}
            and type(cp["v"]) is int and cp["v"] == 1
            and type(cp["count"]) is int and 1 <= cp["count"] <= MAX_EVENTS
            and hexd(cp["genesis"], 64) and hexd(cp["head"], 64)
            and hexd(cp["kid"], 16) and hexd(cp["sig"], 128))


def _strict_event(row, prev):
    if type(row) is not dict or not _valid_hash(row.get("entry_hash")) or row.get("prev_hash") != prev:
        raise WitnessRefusal("broken-or-malformed-entry")
    body = {k: v for k, v in row.items() if k != "entry_hash"}
    try:
        expected = hashlib.sha256(json.dumps(body, sort_keys=True).encode()).hexdigest()
    except (ValueError, TypeError, UnicodeError, RecursionError) as exc:
        raise WitnessRefusal("invalid-entry-body") from exc
    if row["entry_hash"] != expected:
        raise WitnessRefusal("entry-hash-mismatch")
    return expected


class WitnessAuthority:
    """Owner-private filesystem state for exactly one Guard stream.

    Crash consistency is via fsync + atomic replace, not rollback-proof storage.
    Explicit initial enrollment and a separate witness server administrator required.
    """
    def __init__(self, root: str | Path, witness_private, guard_public_ring):
        self.root = Path(root)
        self.private = witness_private
        self.public = witness_private.public_key()
        self.guard_ring = guard_public_ring
        if guard_public_ring.can_sign():
            raise WitnessRefusal("public-only-guard-ring-required")
        public_raw = self.public.public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
        if public_raw in getattr(guard_public_ring, "publics", {}).values():
            raise WitnessRefusal("key-role-overlap")
        self.path = self.root / "latest.json"
        self.lock_path = self.root / "authority.lock"

    @contextmanager
    def _locked(self):
        try:
            s = os.lstat(self.root)
            if (not stat.S_ISDIR(s.st_mode) or stat.S_ISLNK(s.st_mode)
                or s.st_uid != os.geteuid() or stat.S_IMODE(s.st_mode) & 0o077):
                raise WitnessRefusal("insecure-authority-state-directory")
            fd = os.open(self.lock_path, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
            try:
                s = os.fstat(fd)
                if not stat.S_ISREG(s.st_mode) or s.st_uid != os.geteuid() or stat.S_IMODE(s.st_mode) & 0o077:
                    raise WitnessRefusal("insecure-authority-lock")
                fcntl.flock(fd, fcntl.LOCK_EX)
                yield
            finally:
                os.close(fd)
        except OSError as exc:
            raise WitnessRefusal("authority-state-unavailable") from exc

    def _read(self):
        try:
            fd = os.open(self.path, os.O_RDONLY | os.O_NOFOLLOW)
        except FileNotFoundError:
            return None
        except OSError as exc:
            raise WitnessRefusal("unreadable-authority-state") from exc
        try:
            s = os.fstat(fd)
            if (not stat.S_ISREG(s.st_mode) or s.st_uid != os.geteuid()
                or stat.S_IMODE(s.st_mode) & 0o077 or s.st_size > 16_384):
                raise WitnessRefusal("untrusted-authority-state")
            with os.fdopen(fd, "rb") as f:
                fd = -1
                saved = _load(f.read(16_385), maximum=16_384)
        finally:
            if fd >= 0: os.close(fd)
        if (type(saved) is not dict or set(saved) != {"v", "receipt"}
                or type(saved["v"]) is not int or saved["v"] != 1
                or type(saved["receipt"]) is not dict):
            raise WitnessRefusal("corrupt-authority-state")
        receipt = _canonical(saved["receipt"])
        check = verify_trusted_witness(receipt, self.public, self.guard_ring)
        if not check.verified:
            raise WitnessRefusal("invalid-stored-receipt:" + check.reason)
        return saved["receipt"]

    def _write(self, receipt):
        data = _canonical({"v": 1, "receipt": receipt})
        temp = None
        try:
            fd, temp = tempfile.mkstemp(prefix=".latest-", dir=self.root)
            with os.fdopen(fd, "wb") as f:
                f.write(data)
                f.flush()
                os.fsync(f.fileno())
            os.replace(temp, self.path)
            temp = None
            dirfd = os.open(self.root, os.O_RDONLY | os.O_DIRECTORY)
            try: os.fsync(dirfd)
            finally: os.close(dirfd)
        except OSError as exc:
            raise WitnessRefusal("authority-persistence-failed") from exc
        finally:
            if temp is not None:
                try: os.unlink(temp)
                except FileNotFoundError: pass

    def append(self, raw: bytes, *, enroll=False) -> bytes:
        """Accept a Guard-signed head plus exact new chain suffix; sign only after fsync."""
        obj = _load(raw)
        if type(obj) is not dict or set(obj) != {"checkpoint", "entries"}:
            raise WitnessRefusal("invalid-append-schema")
        cp, rows = obj["checkpoint"], obj["entries"]
        if not _valid_cp(cp) or type(rows) is not list or len(rows) > MAX_EVENTS:
            raise WitnessRefusal("invalid-checkpoint-or-suffix")
        try: valid, _ = self.guard_ring.verify_checkpoint(cp)
        except (ValueError, TypeError, AttributeError, KeyError): valid = False
        if not valid:
            raise WitnessRefusal("broker-signature-invalid")
        with self._locked():
            old = self._read()
            if old is None and not enroll:
                raise WitnessRefusal("explicit-enrollment-required")
            if old is not None and enroll:
                raise WitnessRefusal("already-enrolled")
            old_cp = old["checkpoint"] if old is not None else None
            if old_cp is not None and not rows and cp == old_cp:
                return _canonical(old)
            if not rows:
                raise WitnessRefusal("missing-chain-suffix")
            before = old_cp["count"] if old_cp is not None else 0
            if cp["count"] != before + len(rows):
                raise WitnessRefusal("checkpoint-count-not-extension")
            prev = old_cp["head"] if old_cp is not None else ZERO
            first = None
            for row in rows:
                prev = _strict_event(row, prev)
                if first is None:
                    first = prev
            genesis = old_cp["genesis"] if old_cp is not None else first
            if cp["genesis"] != genesis or cp["head"] != prev:
                raise WitnessRefusal("checkpoint-off-history")
            body = {"v": 1, "checkpoint": cp}
            receipt = dict(body, signature=self.private.sign(WITNESS_DOMAIN + _canonical(body)).hex())
            self._write(receipt)
            return _canonical(receipt)

    def challenge(self, raw: bytes) -> bytes:
        """Reply under a fresh nonce with the authority's most recent ACKNOWLEDGED head."""
        obj = _load(raw, maximum=4096)
        if type(obj) is not dict or set(obj) != {"nonce"}:
            raise WitnessRefusal("invalid-challenge-schema")
        nonce = obj["nonce"]
        if not (isinstance(nonce, str) and len(nonce) == 64
                and all(x in "0123456789abcdef" for x in nonce)):
            raise WitnessRefusal("invalid-challenge-nonce")
        with self._locked():
            receipt = self._read()
            if receipt is None:
                raise WitnessRefusal("authority-not-enrolled")
            body = {"v": 2, "nonce": nonce, "witness": receipt}
            return _canonical(dict(body, signature=self.private.sign(ONLINE_DOMAIN + _canonical(body)).hex()))
