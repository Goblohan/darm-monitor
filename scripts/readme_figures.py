#!/usr/bin/env python3
"""darm-monitor's README figures, generated from scripts/stats.py: modules and how
each library is checked, theorems, lines, sorry and declared axioms, and the
theorems the paper cites. --write fills the block between the figures markers;
--check fails if it differs. Usage: scripts/readme_figures.py --write | --check"""
import json, re, subprocess, sys
s = json.loads(subprocess.run([sys.executable, "scripts/stats.py", "--json"],
                              capture_output=True, text=True, check=True).stdout)
cited = re.match(r"(\d+)/(\d+)", s["paper_citations"])
n = lambda x: f"{x:,}"
block = "\n".join([
    "<!-- figures:start -->",
    "| | |",
    "| --- | --- |",
    f"| Lean modules | {n(s['corpus_modules'])}: {s['modules']} in `GRBS/`, every one built by the gate; "
    f"{s['darmmonitor_modules']} in `DarmMonitor/`, built or elaborated by CI |",
    f"| Theorems and lemmas | {n(s['corpus_theorems'])} |",
    f"| Lines of Lean | {n(s['corpus_lines'])} |",
    f"| `sorry`, declared axioms | {len(s['files_with_sorry']) + len(s['darmmonitor_files_with_sorry'])}, "
    f"{s['declared_axioms'] + s['darmmonitor_declared_axioms']} |",
    f"| Theorems the paper cites, each checked to exist | {cited.group(2) if cited else '?'} |",
    "<!-- figures:end -->"])
readme = open("README.md").read()
m = re.search(r"<!-- figures:start -->.*?<!-- figures:end -->", readme, re.S)
if not m:
    sys.exit("README has no figures block")
if "--write" in sys.argv:
    open("README.md", "w").write(readme[:m.start()] + block + readme[m.end():])
    print(block)
elif m.group(0) != block:
    print("README figures are out of date; run scripts/readme_figures.py --write"); print(block); sys.exit(1)
else:
    print("README figures match the repository")
