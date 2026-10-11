"""Targeted mutation gate. Assertion failures count, harness errors do not."""
from __future__ import annotations
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
MUTATIONS = [
    ("consumer-claim-context-removed", "correspondence_runtime.py", [
        ('for field in ("claim_id", "request_id", "subject_digest"):', 'for field in ():')],
     "ConsumerProfileTests.test_claim_downgrade_cannot_satisfy_stronger_consumer"),
    ("policy-content-pin-removed", "correspondence_runtime.py", [
        ('if policy_fingerprint(self.policy) != trusted.policy_fingerprint:', 'if False:')],
     "ConsumerProfileTests.test_same_policy_id_cannot_hide_changed_policy_contents"),
    ("stored-pin-rollback-checks-removed", "correspondence_runtime.py", [
        ('if len(rows) < pin.count:', 'if False:'),
        ('if (rows[0]["entry_hash"] != pin.genesis or\n                        rows[pin.count - 1]["entry_hash"] != pin.head):', 'if False:')],
     "ConsumerProfileTests.test_old_snapshot_refused_after_advance"),
    ("off-branch-checkpoint-check-removed", "guard_audit_bridge.py", [
        ('if (cp["genesis"] != events[0]["entry_hash"] or\n                cp["head"] != events[cp["count"] - 1]["entry_hash"]):', 'if False:')],
     "ConsumerProfileTests.test_signed_off_branch_checkpoint_cannot_hide_among_valid_ones"),
    ("core-gate-bits-ignored", "correspondence_core.py", [
        ('all(c is True for c in checks)', 'True')],
     "OperationalCoreTests.test_every_gate_bit_is_required_and_truthy_is_insufficient"),
    ("core-conjunction-weakened", "correspondence_core.py", [
        ('all(a in available for a in row)', 'any(a in available for a in row)')],
     "OperationalCoreTests.test_channel_identity_and_conjunction_are_required"),
    ("core-empty-contract-allowed", "correspondence_core.py", [
        ('bool(obligations) and', 'True and')],
     "OperationalCoreTests.test_empty_contract_and_empty_row_refuse"),
    ("core-empty-mapping-allowed", "correspondence_core.py", [
        ('bool(row) and', 'True and')],
     "OperationalCoreTests.test_empty_contract_and_empty_row_refuse"),
]

RUNNER = '''import json, unittest, sys
s = unittest.defaultTestLoader.loadTestsFromName(sys.argv[1])
r = unittest.TestResult()
s.run(r)
print(json.dumps(dict(ran=r.testsRun, failures=len(r.failures), errors=len(r.errors), skipped=len(r.skipped))))
'''


def run():
    results = []
    for name, filename, edits, case in MUTATIONS:
        with tempfile.TemporaryDirectory(prefix="e38-mut-") as d:
            root = Path(d)
            for p in HERE.glob("*.py"):
                shutil.copy2(p, root / p.name)
            env = dict(os.environ)
            env["PYTHONPATH"] = str(root) + os.pathsep + env.get("PYTHONPATH", "")
            command = [sys.executable, "-B", "-c", RUNNER, "test_correspondence_runtime." + case]
            baseline = subprocess.run(command, cwd=root, env=env, text=True,
                capture_output=True, timeout=30, check=True)
            before = json.loads(baseline.stdout)
            if before != dict(ran=1, failures=0, errors=0, skipped=0):
                raise RuntimeError("invalid mutation baseline: " + name + repr(before))
            p = root / filename
            text = p.read_text()
            for old, new in edits:
                if text.count(old) != 1:
                    raise RuntimeError("mutation no longer matches: " + name)
                text = text.replace(old, new, 1)
            compile(text, filename, "exec")
            p.write_text(text)
            run = subprocess.run(command, cwd=root, env=env, text=True,
                capture_output=True, timeout=30, check=True)
            result = json.loads(run.stdout)
            caught = result["ran"] == 1 and result["failures"] > 0 and result["errors"] == 0
            results.append(dict(name=name, caught=caught, **result))
            print(("CAUGHT " if caught else "MISSED ") + name)
    print(json.dumps(dict(caught=sum(x["caught"] for x in results),
                         total=len(results), results=results), sort_keys=True))
    return 0 if all(x["caught"] for x in results) else 1


if __name__ == "__main__":
    raise SystemExit(run())
