#!/usr/bin/env python3
"""Every module in GRBS/ is built by the gate (a root, or imported by one); no
file contains sorry; no axiom is declared. Fails otherwise."""
import json, subprocess, sys
s = json.loads(subprocess.run([sys.executable, "scripts/stats.py", "--json"],
                              capture_output=True, text=True, check=True).stdout)
bad = []
if s["modules_not_built_by_the_gate"]:
    bad.append("not built by the gate: " + ", ".join(s["modules_not_built_by_the_gate"]))
if s["files_with_sorry"]:
    bad.append("sorry in: " + ", ".join(s["files_with_sorry"]))
if s["declared_axioms"]:
    bad.append(f"{s['declared_axioms']} declared axiom(s)")
for b in bad:
    print("BUILT", b)
print(f"modules: {s['modules_built_by_the_gate']}/{s['modules']} built by the gate; "
      f"theorems in built modules: {s['theorems_in_built_modules']}")
sys.exit(1 if bad else 0)
