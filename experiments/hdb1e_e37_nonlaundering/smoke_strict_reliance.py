"""Run disposable signed evidence through exact-head witness and REAL Lean process.

Not a live DARM Guard broker integration, production witness or effect mediation.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from lean_authority import LeanAuthoritativeCore
from test_strict_reliance import StrictRelianceIntegrationTests


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--repo", required=True)
    p.add_argument("--persistent", action="store_true", help="Use a prestarted persistent Lean worker")
    args = p.parse_args()
    fx = StrictRelianceIntegrationTests(methodName="test_positive_uses_live_witness_and_lean")
    fx.setUp()
    try:
        fx.core = LeanAuthoritativeCore(Path(args.repo), persistent=args.persistent)
        good_core = fx.core
        fx.gate = fx.new_gate()
        good = fx.decide()
        unavailable = fx.decide(fx.new_gate(fetch=lambda _: (_ for _ in ()).throw(OSError("offline"))))
        mismatched = fx.decide(content=b"tampered bytes")
        bad_core = LeanAuthoritativeCore(Path(fx.sandbox.name) / "missing-lean")
        fx.core = bad_core
        failed_lean = fx.decide(fx.new_gate())
        cases = [
            ("valid-witness-guard-lean", good.admit is True, good.reasons),
            ("witness-outage-refuses", unavailable.admit is False, unavailable.reasons),
            ("tampered-content-refuses", mismatched.admit is False, mismatched.reasons),
            ("lean-missing-refuses", failed_lean.admit is False, failed_lean.reasons),
        ]
        result = {"scope": "disposable Guard-format evidence and signed witness; real Lean process; no effect executed",
                  "passed": sum(ok for _, ok, _ in cases), "total": len(cases),
                  "status": "PASS" if all(ok for _,ok,_ in cases) else "FAIL",
                  "cases": [{"case": name, "pass": ok, "reasons": reasons} for name,ok,reasons in cases]}
        print(json.dumps(result, indent=2))
        return 0 if result["status"] == "PASS" else 1
    finally:
        if "good_core" in locals():
            good_core.close()
        fx.doCleanups()


if __name__ == "__main__":
    sys.exit(main())
