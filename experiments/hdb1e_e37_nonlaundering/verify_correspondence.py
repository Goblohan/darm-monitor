"""Run all local acceptance gates without silently skipping unavailable gates.

Writes a fresh report on every run. A report is PASS only when Python, both
mutation gates, the Lean build/axiom audit, finite conformance, and the real
broker test all pass. This is still not a proof of all-input Python refinement.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import unittest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--guard", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    guard = args.guard.expanduser().resolve()
    if not (guard / "darm_guard/attest.py").is_file():
        parser.error("--guard must name the actual DARM Guard repository")
    output = args.output.expanduser().resolve()
    output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["PYTHONPATH"] = os.pathsep.join((str(guard), str(HERE), env.get("PYTHONPATH", "")))
    env["LEAN_NUM_THREADS"] = "1"
    runner = '''import json,sys,unittest
s=unittest.defaultTestLoader.loadTestsFromNames(sys.argv[1:])
r=unittest.TextTestRunner(verbosity=2).run(s)
print(json.dumps(dict(ran=r.testsRun,failures=len(r.failures),errors=len(r.errors),skipped=len(r.skipped))))
sys.exit(0 if r.wasSuccessful() and not r.skipped and r.testsRun else 1)
'''
    steps = [
        ("python", [sys.executable, "-c", runner, "tests", "test_guard_bridge", "test_guard_audit_bridge",
                    "test_guard_witness_bridge", "test_guard_monotonic_bridge", "test_correspondence_runtime"], 180),
        ("legacy_mutations", [sys.executable, str(HERE/"mutation_gate.py")], 180),
        ("correspondence_mutations", [sys.executable, str(HERE/"correspondence_mutation_gate.py")], 180),
        ("lean_build", ["lake", "build", "+E38OperationalCore", "+E38OperationalCorrespondence"], 7200),
        ("lean_axioms", ["lake", "env", "lean", str(REPO/"GRBS/E38OperationalCorrespondence.lean")], 180),
        ("finite_conformance", [sys.executable, str(HERE/"check_correspondence.py")], 180),
        ("live_broker", [sys.executable, "-c", runner, "test_live_guard_broker"], 180),
    ]
    records = []
    for name, command, timeout in steps:
        print("RUN " + name, flush=True)
        try:
            done = subprocess.run(command, cwd=REPO, env=env, text=True,
                                  capture_output=True, timeout=timeout)
            log = done.stdout + done.stderr
            passed = done.returncode == 0
            if name.startswith("lean") and ("sorryAx" in log or re.search(r"\buses 'sorry'\b", log)):
                passed = False
            if name.startswith("lean"):
                for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", log, re.S):
                    if set(x.strip() for x in group.split(",")) - {"propext", "Classical.choice", "Quot.sound"}:
                        passed = False
            if name == "lean_axioms":
                for theorem in ("support_check_sound", "admitted_implies_e37_entitled",
                                "world_truth_only_with_adequacy"):
                    if theorem not in log:
                        passed = False
            status = "PASS" if passed else "FAIL"
            returncode = done.returncode
        except (OSError, subprocess.TimeoutExpired) as exc:
            log, status, returncode = str(exc), "BLOCKED", None
        (output/(name+".log")).write_text(log)
        records.append(dict(name=name, status=status, returncode=returncode,
                            log_sha256=hashlib.sha256(log.encode()).hexdigest()))
        print(status + " " + name, flush=True)
    hashes = {}
    for p in list(HERE.glob("*.py")) + list(HERE.glob("*.lean")) + [
            REPO/"GRBS/E38RelianceNonLaundering.lean", REPO/"GRBS/E38OperationalCore.lean",
            REPO/"GRBS/E38OperationalCorrespondence.lean"]:
        hashes[str(p.relative_to(REPO))] = hashlib.sha256(p.read_bytes()).hexdigest()
    def git_head(path):
        r = subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"], capture_output=True, text=True)
        return r.stdout.strip() if r.returncode == 0 else None
    report = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(),
        status="PASS" if all(x["status"] == "PASS" for x in records) else "INCOMPLETE",
        scope="tested Python plus conditional Lean support proof; not end-to-end refinement",
        monitor_head=git_head(REPO), guard_head=git_head(guard), steps=records, source_sha256=hashes)
    (output/"CORRESPONDENCE_VERIFICATION.json").write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    print("Report: " + str(output/"CORRESPONDENCE_VERIFICATION.json"))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
