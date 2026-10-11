"""E38 Stage 2: narrow verifier for *native* DARM Guard v2 file evidence.

This is a research adapter, not a DARM Guard runtime modification. It accepts
only the original Guard Ed25519 message and signed audit checkpoints. It never
interprets a broker file signature as validation of the file's meaning.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

NARROW_CLAIM = 'broker_attested_file_content_at_observation'
XATTR = 'user.darm'


def _no_dupes(pairs):
    d = {}
    for key, value in pairs:
        if key in d:
            raise ValueError('duplicate JSON key: ' + key)
        d[key] = value
    return d


def _json(data):
    return json.loads(data, object_pairs_hook=_no_dupes)


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _pub(ring: Mapping[str, Any], kid: str) -> Ed25519PublicKey:
    keys = ring['keys']
    if not isinstance(keys, dict) or kid not in keys:
        raise ValueError('unknown signing key')
    raw = bytes.fromhex(keys[kid])
    if len(raw) != 32 or _sha256(raw)[:16] != kid:
        raise ValueError('public ring contains an incorrectly identified key')
    return Ed25519PublicKey.from_public_bytes(raw)


def _verify_att(raw: bytes, ring, rid: str, logical_target: str, digest: str) -> None:
    a = _json(raw)
    if not isinstance(a, dict) or set(a) != {'v', 'rid', 'target', 'digest', 'kid', 'sig'}:
        raise ValueError('invalid v2 attestation schema')
    if type(a['v']) is not int or a['v'] != 2:
        raise ValueError('not a v2 attestation')
    if (a['rid'], a['target'], a['digest']) != (rid, logical_target, digest):
        raise ValueError('request, logical target or file digest mismatch')
    if not all(isinstance(a[k], str) for k in ('rid','target','digest','kid','sig')):
        raise ValueError('invalid attestation fields')
    msg = f'darm-attest-v2|{rid}|{logical_target}|{digest}'.encode()
    _pub(ring, a['kid']).verify(bytes.fromhex(a['sig']), msg)


def _read_audit(entries: list[dict[str, Any]]) -> tuple[list[str], int]:
    if not entries:
        raise ValueError('empty audit')
    hashes = []
    prev = '0' * 64
    for idx, e in enumerate(entries):
        if not isinstance(e, dict):
            raise ValueError('invalid audit entry')
        if e.get('prev_hash') != prev or not isinstance(e.get('entry_hash'), str):
            raise ValueError(f'audit link mismatch at {idx}')
        body = dict(e)
        claimed_hash = body.pop('entry_hash')
        calc = _sha256(json.dumps(body, sort_keys=True).encode())
        if calc != claimed_hash:
            raise ValueError(f'audit hash mismatch at {idx}')
        hashes.append(claimed_hash)
        prev = claimed_hash
    return hashes, len(entries)


def _latest_for_target(entries, target):
    latest = None
    index = -1
    for i, e in enumerate(entries):
        if (e.get('event') in ('outcome','reconciled') and e.get('target') == target
            and (e.get('effect') == 'succeeded' or e.get('reconciliation') == 'confirmedSuccess')):
            latest = (e.get('request_id'), 'delete' if e.get('tool') == 'delete_file' else 'write')
            index = i
        # A rename of this target away supersedes its old file identity.
        if (e.get('event') in ('outcome','reconciled') and e.get('source') == target
            and e.get('tool') == 'rename_file'
            and (e.get('effect') == 'succeeded' or e.get('reconciliation') == 'confirmedSuccess')):
            latest = (e.get('request_id'), 'delete')
            index = i
    return latest, index


def _checkpoint_covers(entries, hashes, checkpoints, ring):
    if not isinstance(checkpoints, list) or not checkpoints:
        raise ValueError('no independent signed checkpoint')
    genesis = hashes[0]
    # Require a checkpoint authenticating *all* entries, not merely a prefix.
    for cp in checkpoints:
        if not isinstance(cp, dict):
            continue
        try:
            if type(cp.get('count')) is not int or cp['count'] != len(entries):
                continue
            if cp.get('v') != 1 or cp.get('genesis') != genesis or cp.get('head') != hashes[-1]:
                continue
            msg = f"darm-checkpoint-v1|{cp['genesis']}|{cp['count']}|{cp['head']}".encode()
            _pub(ring, cp['kid']).verify(bytes.fromhex(cp['sig']), msg)
            return
        except (InvalidSignature, ValueError, KeyError, TypeError, AttributeError):
            continue
    raise ValueError('no valid checkpoint covers the complete audit snapshot')


@dataclass(frozen=True)
class Result:
    admit: bool
    claim: str
    reason: str
    # Not an assertion about content semantics, current deployment, or runtime authority.
    evidentiary_scope: tuple[str, ...]

    def as_dict(self):
        return {'reliance': 'ADMIT' if self.admit else 'REFUSE',
                'claim': self.claim, 'reason': self.reason,
                'evidentiary_scope': list(self.evidentiary_scope)}


def verify_snapshot(*, raw_attestation: bytes, content: bytes, logical_target: str,
                    expected_request_id: str, public_ring: dict, audit_entries: list[dict],
                    published_checkpoints: list[dict], requested_claim: str) -> Result:
    """Admit only narrow evidence, and only against a fully signed log snapshot.

    The public ring and checkpoint provenance must be independently trusted.
    This does not prove the snapshot reflects the newest possible world state.
    """
    if requested_claim != NARROW_CLAIM:
        return Result(False, requested_claim, 'unsupported target claim: signature is not semantic validation', ())
    try:
        if not logical_target.startswith('/workspace/') or any(
                seg in ('', '.', '..') for seg in logical_target[len('/workspace/'):].split('/')):
            raise ValueError('noncanonical or out-of-workspace logical target')
        if not isinstance(expected_request_id, str) or not expected_request_id:
            raise ValueError('missing independently specified request id')
        _verify_att(raw_attestation, public_ring, expected_request_id, logical_target, _sha256(content))
        hashes, _ = _read_audit(audit_entries)
        latest, _idx = _latest_for_target(audit_entries, logical_target)
        if latest != (expected_request_id, 'write'):
            raise ValueError('latest successful audit event does not match attestation')
        _checkpoint_covers(audit_entries, hashes, published_checkpoints, public_ring)
        return Result(True, requested_claim, 'native Guard v2 bytes, latest audit event and signed checkpoint match',
                      ('request_binding', 'logical_path_binding', 'observed_bytes_digest',
                       'guard_key_signature', 'anchored_audit_snapshot'))
    except (InvalidSignature, ValueError, KeyError, TypeError, AttributeError, UnicodeError) as exc:
        return Result(False, requested_claim, f'{type(exc).__name__}: {exc}', ())


def read_workspace_snapshot(workspace_root: str, logical_target: str):
    """Read a broker path through no-follow directory handles, as Guard does.

    The caller supplies the deployment's trusted workspace root. The read
    describes one observed descriptor, not an immutable future file state.
    """
    if not logical_target.startswith('/workspace/'):
        raise ValueError('file is outside the logical workspace')
    parts = logical_target[len('/workspace/'):].split('/')
    if not parts or any(part in ('', '.', '..') for part in parts):
        raise ValueError('not a normalized workspace path')
    dfd = os.open(workspace_root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for part in parts[:-1]:
            nxt = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=dfd)
            os.close(dfd)
            dfd = nxt
        fd = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW, dir_fd=dfd)
        try:
            st = os.fstat(fd)
            if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
                raise ValueError('not an exclusive regular file')
            raw = os.getxattr(fd, XATTR)
            with os.fdopen(os.dup(fd), 'rb') as stream:
                data = stream.read()
            return raw, data
        finally:
            os.close(fd)
    finally:
        os.close(dfd)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--workspace', required=True, help='Trusted physical root of broker workspace')
    p.add_argument('--target', required=True, help='Logical target, e.g. /workspace/reports/a.txt')
    p.add_argument('--rid', required=True, help='Expected request ID from a trusted source')
    p.add_argument('--public-ring', required=True, help='Principal-trusted <audit>.pub.json')
    p.add_argument('--audit', required=True)
    p.add_argument('--checkpoints', required=True, help='Principal-trusted signed checkpoints JSONL')
    p.add_argument('--claim', default=NARROW_CLAIM)
    args = p.parse_args()
    try:
        raw, content = read_workspace_snapshot(args.workspace, args.target)
        ring = _json(Path(args.public_ring).read_text())
        entries = [_json(s) for s in Path(args.audit).read_text().splitlines() if s.strip()]
        cps = [_json(s) for s in Path(args.checkpoints).read_text().splitlines() if s.strip()]
        result = verify_snapshot(raw_attestation=raw, content=content,
             logical_target=args.target, expected_request_id=args.rid,
             public_ring=ring, audit_entries=entries, published_checkpoints=cps,
             requested_claim=args.claim)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        result = Result(False, args.claim, f'{type(exc).__name__}: {exc}', ())
    print(json.dumps(result.as_dict(), indent=2))
    return 0 if result.admit else 2


if __name__ == '__main__':
    raise SystemExit(main())
