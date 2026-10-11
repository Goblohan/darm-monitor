"""EXPERIMENTAL authoritative Lean operational core, not a Python proof.

For a narrow explicitly validated input domain, use the *Lean* executable
admission operation as the decision source rather than compare sampled Python
results. Invalid inputs, oracle crashes, malformed output and timeouts REFUSE.
Not integrated into the published E38 consumer profile. This does not prove
CPython parsing, crypto, normalization, invocation integrity or effect mediation.
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path

MAX_BYTES = 65536
MAX_STR = 128
MAX_FACTS = 256
MAX_OBLIGATIONS = 256
MAX_CHECKS = 32
ALLOWED = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789:._-/")


def validate_domain(facts, obligations, checks):
    """Restrict inputs to exact native tuples, ASCII labels and Bool values."""
    if type(facts) is not tuple or len(facts) > MAX_FACTS:
        return False
    if type(obligations) is not tuple or len(obligations) > MAX_OBLIGATIONS:
        return False
    if type(checks) is not tuple or len(checks) > MAX_CHECKS:
        return False
    def label(s):
        return type(s) is str and 0 < len(s) <= MAX_STR and all(c in ALLOWED for c in s)
    return (all(label(s) for s in facts)
            and all(type(r) is tuple and len(r) <= MAX_FACTS and all(label(a) for a in r)
                    for r in obligations)
            and all(type(c) is bool for c in checks))


class LeanAuthoritativeCore:
    def __init__(self, monitor_root: str | Path, *, timeout=20, persistent=False):
        self.root = Path(monitor_root).resolve()
        self.oracle = self.root / "experiments/hdb1e_e37_nonlaundering/CorrespondenceOracle.lean"
        self.timeout = timeout
        self._worker = None
        if persistent:
            from lean_worker import LeanPersistentWorker
            self._worker = LeanPersistentWorker(self.root)
            self._worker.start()

    def close(self):
        if self._worker is not None:
            self._worker.close()

    @property
    def last_status(self):
        if self._worker is not None:
            return self._worker.last_status
        return "ONE_SHOT_NO_STATUS"

    def admit_core(self, facts, obligations, checks):
        """Return true iff the trusted Lean oracle admits. Never Python fallback."""
        if not validate_domain(facts, obligations, checks):
            return False
        if self._worker is not None:
            return self._worker.admit_core(facts, obligations, checks)
        payload = [{"facts": facts, "obligations": obligations, "checks": checks}]
        request = json.dumps(payload, ensure_ascii=True, separators=(",", ":")) + "\n"
        if len(request.encode()) > MAX_BYTES or not self.oracle.is_file():
            return False
        try:
            result = subprocess.run(
                ["lake", "env", "lean", "--run", str(self.oracle)],
                cwd=self.root, input=request, capture_output=True, text=True,
                timeout=self.timeout, check=False)
            if result.returncode or len(result.stdout) > 32:
                return False
            response = json.loads(result.stdout)
            return type(response) is list and len(response) == 1 and response[0] is True
        except (OSError, ValueError, TypeError, subprocess.TimeoutExpired):
            return False
