"""Explicit offline enrollment for localhost E38 witness prototype only."""
import argparse
from pathlib import Path
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from darm_guard.attest import KeyRing
from witness_authority import WitnessAuthority


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--state', required=True)
    p.add_argument('--witness-seed', required=True)
    p.add_argument('--guard-public-ring', required=True)
    p.add_argument('--first-append-json', required=True)
    args = p.parse_args()
    key = Ed25519PrivateKey.from_private_bytes(Path(args.witness_seed).read_bytes())
    ring = KeyRing.load(None, args.guard_public_ring)
    receipt = WitnessAuthority(args.state, key, ring).append(
        Path(args.first_append_json).read_bytes(), enroll=True)
    print('Enrolled one stream at signed head. V1 receipt:', receipt.decode())


if __name__ == '__main__':
    main()
