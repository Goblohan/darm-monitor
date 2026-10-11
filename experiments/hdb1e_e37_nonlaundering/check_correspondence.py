"""Finite Python/Lean conformance. Missing Lean is a failure, never a pass."""
from __future__ import annotations
import argparse
import itertools
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile
from unittest.mock import patch

from correspondence_core import admit_core
from fixtures import NOW, POLICY
from run_experiment import cases
import verifier

HERE = Path(__file__).resolve().parent


def vectors():
    universe = ["source:p", "target:p", "source:q"]
    subsets = [list(s) for n in range(4) for s in itertools.combinations(universe, n)]
    contracts = [[]] + [[a] for a in subsets] + [[a, b] for a in subsets for b in subsets]
    result = [dict(facts=f, obligations=o, checks=list(c))
        for f in subsets for o in contracts for c in itertools.product((False, True), repeat=3)]
    # Each of E38's nine Boolean positions independently participates.
    for c in itertools.product((False, True), repeat=9):
        result.append(dict(facts=["source:p"], obligations=[["source:p"]], checks=list(c)))
    rng = random.Random(38)
    for _ in range(1000):
        result.append(dict(facts=rng.choice(subsets),
            obligations=[rng.choice(subsets) for _ in range(rng.randrange(7))],
            checks=[rng.choice([False, True]) for _ in range(rng.randrange(10))]))
    # Capture the actual post-envelope, post-policy inputs used by verifier.py.
    for name, request, expected in cases():
        calls = []
        def capture(facts, obligations, checks):
            calls.append(dict(facts=list(facts), obligations=[list(x) for x in obligations], checks=list(checks)))
            return admit_core(facts, obligations, checks)
        with patch.object(verifier, "admit_core", capture):
            actual = verifier.decide(request, POLICY, NOW).admit
        if actual is not expected:
            raise RuntimeError("fixture disagrees with specified verdict: " + name)
        # Unknown claims reject before reaching the core and need no vector.
        result.extend(calls)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", help="Explicit Lean binary, otherwise use lake env lean")
    parser.add_argument("--generate-only", action="store_true", help="Inspect corpus; NOT a conformance pass")
    args = parser.parse_args()
    data = vectors()
    expected = [admit_core(tuple(x["facts"]), tuple(tuple(r) for r in x["obligations"]), tuple(x["checks"])) for x in data]
    if args.generate_only:
        print(json.dumps(dict(vectors=len(data), admits=sum(expected), lean_conformance="NOT_RUN")))
        return 0
    env = dict(os.environ)
    repo = HERE.parents[1]
    try:
        with tempfile.TemporaryDirectory(prefix="e38-lean-") as tmp:
            if args.lean:
                lean = str(Path(args.lean).resolve())
                core = repo / "GRBS/E38OperationalCore.lean"
                build = subprocess.run([lean, "-o", str(Path(tmp)/"E38OperationalCore.olean"), str(core)],
                    cwd=repo, env=env, capture_output=True, text=True, timeout=180)
                if build.returncode:
                    raise RuntimeError(build.stdout + build.stderr)
                env["LEAN_PATH"] = tmp + os.pathsep + env.get("LEAN_PATH", "")
                command = [lean, "--run", str(HERE/"CorrespondenceOracle.lean")]
            else:
                command = ["lake", "env", "lean", "--run", str(HERE/"CorrespondenceOracle.lean")]
            run = subprocess.run(command, cwd=repo, env=env,
                input=json.dumps(data, separators=(",", ":"))+"\n", capture_output=True,
                text=True, timeout=180)
            if run.returncode:
                raise RuntimeError(run.stdout + run.stderr)
            answers = json.loads(run.stdout)
            if (not isinstance(answers, list) or len(answers) != len(expected)
                    or any(type(x) is not bool for x in answers)):
                raise RuntimeError("malformed or incomplete Lean oracle output")
            mismatches = [i for i, (x,y) in enumerate(zip(expected,answers)) if x is not y]
            if mismatches:
                raise RuntimeError("Python/Lean disagreement at cases " + repr(mismatches[:20]))
    except (OSError, RuntimeError, ValueError, subprocess.TimeoutExpired) as exc:
        print(json.dumps(dict(vectors=len(data), lean_conformance="FAILED_OR_BLOCKED", error=str(exc))))
        return 1
    print(json.dumps(dict(vectors=len(data), mismatches=0, lean_conformance="PASS",
        scope="finite normalized core, not all-input Python refinement")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
