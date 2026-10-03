#!/usr/bin/env python3
"""Figures for darm-monitor, generated from the repository, with the commit.
Theorems are counted as declarations written in the source (`theorem` or
`lemma`, with any attributes and modifiers; comments stripped), not as
constants in Lean's environment, which also holds lemmas Lean generates itself
(equation and injectivity lemmas) that nobody wrote or reviewed.
Usage: scripts/stats.py [--json]"""
import glob, json, os, re, subprocess, sys
KINDS = ("theorem", "lemma", "def", "abbrev", "structure", "inductive", "instance", "example", "axiom")
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped)\s+)*("
                  + "|".join(KINDS) + r")\b")
def strip_comments(src):
    return re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", src, flags=re.S))
def sh(*cmd):
    return subprocess.run(cmd, capture_output=True, text=True).stdout.strip()
files = sorted(glob.glob("GRBS/*.lean"))
counts, lines, sorry_files, per_module = {k: 0 for k in KINDS}, 0, [], {}
for f in files:
    src = open(f).read()
    lines += src.count("\n")
    code = strip_comments(src)
    for l in code.split("\n"):
        m = DECL.match(l)
        if m:
            counts[m.group(1)] += 1
            if m.group(1) in ("theorem", "lemma"):
                per_module[os.path.basename(f)[:-5]] = per_module.get(os.path.basename(f)[:-5], 0) + 1
    if re.search(r"\bsorry\b", code):
        sorry_files.append(f)
roots = set(re.findall(r"^\s*`([A-Za-z0-9_.]+),?\s*$", open("lakefile.lean").read(), re.M))
mods = {os.path.basename(f)[:-5] for f in files}
imports = {m: set() for m in mods}            # what each GRBS module imports from GRBS
for f in files:
    m = os.path.basename(f)[:-5]
    for line in open(f):
        if line.startswith("import "):
            imports[m] |= {x for x in line.split()[1:] if x in mods}
built, todo = set(), [r for r in roots if r in mods]
while todo:                                   # the roots, and everything they import, transitively
    m = todo.pop()
    if m not in built:
        built.add(m); todo.extend(imports[m])
cited = (sh(sys.executable, "paper/check_citations.py").splitlines() or ["?"])[-1]
s = {"commit": sh("git", "rev-parse", "--short", "HEAD"), "modules": len(files),
     "theorems": counts["theorem"] + counts["lemma"], "definitions": counts["def"] + counts["abbrev"],
     "structures_and_inductives": counts["structure"] + counts["inductive"], "instances": counts["instance"],
     "examples": counts["example"], "declared_axioms": counts["axiom"], "lines": lines,
     "files_with_sorry": sorry_files, "modules_built_by_the_gate": len(built),
     "theorems_in_built_modules": sum(per_module.get(m, 0) for m in built),
     "modules_not_built_by_the_gate": sorted(mods - built),
     "paper_citations": cited}
if "--json" in sys.argv:
    print(json.dumps(s, indent=1)); sys.exit(0)
for k, v in s.items():
    print(f"{k.replace('_', ' '):32} {v}")
