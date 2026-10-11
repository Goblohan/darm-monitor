"""Interoperate with DARM Guard's real local KeyRing API. No broker is started."""
from pathlib import Path
import hashlib
import json
import os
import sys

sys.path.insert(0, str(Path.home() / 'darm-guard'))
try:
    from darm_guard.attest import KeyRing
except ImportError as exc:
    raise SystemExit(f'DARM Guard source not available at ~/darm-guard: {exc}')
from guard_v2_bridge import NARROW_CLAIM, verify_snapshot

ring = KeyRing.generate()
rid, target, content = 'e38-native-keyring-test', '/workspace/report.txt', b'e38 interoperability test'
digest = hashlib.sha256(content).hexdigest()
raw = ring.sign(rid, target, digest)
public_ring = {'active': ring.active, 'keys': {k:v.hex() for k,v in ring.publics.items()}}

def line(body, prev):
    e = dict(body, prev_hash=prev, ts='2026-10-09T00:00:00')
    e['entry_hash'] = hashlib.sha256(json.dumps(e, sort_keys=True).encode()).hexdigest()
    return e

entries = [line({'event':'prepared','request_id':rid},'0'*64)]
entries.append(line({'event':'outcome','request_id':rid, 'target':target,
                     'effect':'succeeded','tool':'write_file'},entries[-1]['entry_hash']))
cp = ring.sign_checkpoint(entries[0]['entry_hash'],len(entries), entries[-1]['entry_hash'])

kwargs = dict(raw_attestation=raw, content=content, logical_target=target,
              expected_request_id=rid, public_ring=public_ring, audit_entries=entries,
              published_checkpoints=[cp], requested_claim=NARROW_CLAIM)
accepted = verify_snapshot(**kwargs)
assert accepted.admit, accepted
assert not verify_snapshot(**dict(kwargs,requested_claim='financially_validated')).admit
assert not verify_snapshot(**dict(kwargs,content=b'corrupted')).admit
print('NATIVE_GUARD_KEYRING_INTEROPERABILITY: PASS')
print('SEMANTIC_UPGRADE_REFUSAL: PASS')
print('CHANGED_BYTES_REFUSAL: PASS')
print('LIMITATION: no running broker, policy authority or world-truth verification performed')
