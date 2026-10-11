"""Loopback demonstration HTTP transport for E38 experimental witness authority.

NOT a production server: no TLS, DoS protection, formalized auth channel, HSM or
independent deployment evidence. Refuses non-loopback binding by design.
"""
import argparse
import hmac
import json
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from darm_guard.attest import KeyRing
from witness_authority import WitnessAuthority, WitnessRefusal


class Handler(BaseHTTPRequestHandler):
    def do_POST(self):
        if self.path not in {"/append", "/challenge"}:
            self.send_error(404)
            return
        try:
            n = int(self.headers.get("Content-Length", "0"))
            if not 1 <= n <= 16 * 1024 * 1024:
                raise WitnessRefusal("invalid-body-length")
            if self.path == "/append" and not hmac.compare_digest(
                    self.headers.get("X-Witness-Token", ""), self.server.append_token):
                self.send_error(403)
                return
            raw = self.rfile.read(n)
            if len(raw) != n:
                raise WitnessRefusal("incomplete-body")
            if self.path == "/append":
                result = self.server.authority.append(raw, enroll=False)
            else:
                result = self.server.authority.challenge(raw)
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(result)))
            self.end_headers()
            self.wfile.write(result)
        except WitnessRefusal as exc:
            response = json.dumps({"error": str(exc)}).encode()
            self.send_response(400)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(response)))
            self.end_headers()
            self.wfile.write(response)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--state", required=True)
    p.add_argument("--witness-seed", required=True)
    p.add_argument("--guard-public-ring", required=True)
    p.add_argument("--append-token-file", required=True)
    p.add_argument("--port", type=int, default=8168)
    args = p.parse_args()
    # Explicitly no remote exposure; real service requires separate deployment
    # design with strong authentication, TLS/mTLS and protected witness storage.
    key = Ed25519PrivateKey.from_private_bytes(Path(args.witness_seed).read_bytes())
    ring = KeyRing.load(None, args.guard_public_ring)
    authority = WitnessAuthority(args.state, key, ring)
    token = Path(args.append_token_file).read_text().strip()
    if len(token) < 32:
        p.error("append token must be at least 32 characters")
    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    server.authority = authority
    server.append_token = token
    print(f"EXPERIMENT ONLY. Loopback witness on 127.0.0.1:{args.port}", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
