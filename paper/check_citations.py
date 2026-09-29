#!/usr/bin/env python3
"""Every `Module.theorem` cited in paper/*.md must be a theorem in GRBS/Module.lean.
Usage (from the repository root): python3 paper/check_citations.py"""
import glob, os, re, sys

root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
cite = re.compile(r"`([A-Z][A-Za-z0-9_]*)\.([A-Za-z_][A-Za-z0-9_']*)`")
bad, seen = [], set()
for md in sorted(glob.glob(os.path.join(root, "paper", "*.md"))):
    for n, line in enumerate(open(md), 1):
        for mod, thm in cite.findall(line):
            seen.add((mod, thm))
            path = os.path.join(root, "GRBS", mod + ".lean")
            if not os.path.exists(path):
                bad.append(f"{os.path.basename(md)}:{n}: module {mod} not found")
            elif not re.search(rf"^\s*theorem\s+{re.escape(thm)}\b", open(path).read(), re.M):
                bad.append(f"{os.path.basename(md)}:{n}: theorem {mod}.{thm} not found")
for b in bad:
    print("MISSING  " + b)
print(f"{len(seen) - len({(m, t) for m, t in seen if any(f'{m}.{t}' in b or f'module {m}' in b for b in bad)})}"
      f"/{len(seen)} cited theorems exist")
sys.exit(1 if bad else 0)
