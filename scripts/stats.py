#!/usr/bin/env python3
"""Figures for darm-monitor, generated from the repository, with the commit.

Two libraries. GRBS: every module is a root or imported by one, and the gate
(scripts/gate.sh) builds them all. DarmMonitor: the default `lake build` and
darmdemo build the modules reachable from their roots; CI's tier 3 elaborates
every other module in the folder, file by file.

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

def scan(path):
    """Declarations by kind, lines, and whether the code (comments aside) uses sorry."""
    src = open(path).read()
    code = strip_comments(src)
    kinds = {k: 0 for k in KINDS}
    for l in code.split("\n"):
        m = DECL.match(l)
        if m:
            kinds[m.group(1)] += 1
    return kinds, src.count("\n"), bool(re.search(r"\bsorry\b", code))

def imports(path, known):
    return {x for l in open(path) if l.startswith("import ") for x in l.split()[1:] if x in known}

def closure(roots, imp):
    seen, todo = set(), list(roots)
    while todo:
        m = todo.pop()
        if m not in seen:
            seen.add(m); todo.extend(imp.get(m, ()))
    return seen

# ---- GRBS: modules are file stems; built by the gate = roots and their imports
grbs = {os.path.basename(f)[:-5]: f for f in sorted(glob.glob("GRBS/*.lean"))}
roots = set(re.findall(r"^\s*`([A-Za-z0-9_.]+),?\s*$", open("lakefile.lean").read(), re.M))
grbs_imp = {m: imports(p, grbs) for m, p in grbs.items()}
grbs_built = closure([r for r in roots if r in grbs], grbs_imp)
g_scan = {m: scan(p) for m, p in grbs.items()}

# ---- DarmMonitor: dotted names; default build from DarmMonitor, darmdemo from Main
dm = {}
for d, _, fs in os.walk("DarmMonitor"):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(d, f); dm[p[:-5].replace(os.sep, ".")] = p
if os.path.exists("DarmMonitor.lean"):
    dm["DarmMonitor"] = "DarmMonitor.lean"
dm_imp = {m: imports(p, dm) for m, p in dm.items()}
dm_roots = ["DarmMonitor"] + (sorted(imports("Main.lean", dm)) if os.path.exists("Main.lean") else [])
dm_built = closure([r for r in dm_roots if r in dm], dm_imp)
d_scan = {m: scan(p) for m, p in dm.items()}

def tally(scans, mods):
    th = sum(scans[m][0]["theorem"] + scans[m][0]["lemma"] for m in mods)
    return th, sum(scans[m][1] for m in mods)

g_th, g_lines = tally(g_scan, grbs)
d_th, d_lines = tally(d_scan, dm)
cited = (sh(sys.executable, "paper/check_citations.py").splitlines() or ["?"])[-1]
s = {"commit": sh("git", "rev-parse", "--short", "HEAD"),
     # GRBS: the gate builds every module (scripts/check_built.py enforces these four)
     "modules": len(grbs),
     "modules_built_by_the_gate": len(grbs_built),
     "theorems_in_built_modules": sum(g_scan[m][0]["theorem"] + g_scan[m][0]["lemma"] for m in grbs_built),
     "modules_not_built_by_the_gate": sorted(set(grbs) - grbs_built),
     "theorems": g_th,
     "definitions": sum(v[0]["def"] + v[0]["abbrev"] for v in g_scan.values()),
     "structures_and_inductives": sum(v[0]["structure"] + v[0]["inductive"] for v in g_scan.values()),
     "instances": sum(v[0]["instance"] for v in g_scan.values()),
     "examples": sum(v[0]["example"] for v in g_scan.values()),
     "declared_axioms": sum(v[0]["axiom"] for v in g_scan.values()),
     "lines": g_lines,
     "files_with_sorry": sorted(grbs[m] for m in grbs if g_scan[m][2]),
     # DarmMonitor: reported, built by CI (default build and darmdemo; tier 3 for the rest)
     "darmmonitor_modules": len(dm),
     "darmmonitor_in_default_build_or_darmdemo": len(dm_built),
     # tier 3 elaborates the folder's top level only (find -maxdepth 1): a module in a subfolder,
     # outside the default build, is checked by nothing in CI
     "darmmonitor_elaborated_by_ci_tier3": len([m for m in set(dm) - dm_built if m.count(".") == 1]),
     "darmmonitor_not_checked_by_ci": sorted(m for m in set(dm) - dm_built if m.count(".") > 1),
     "darmmonitor_theorems": d_th,
     "darmmonitor_lines": d_lines,
     "darmmonitor_declared_axioms": sum(v[0]["axiom"] for v in d_scan.values()),
     "darmmonitor_files_with_sorry": sorted(dm[m] for m in dm if d_scan[m][2]),
     # the whole corpus
     "corpus_modules": len(grbs) + len(dm),
     "corpus_theorems": g_th + d_th,
     "corpus_lines": g_lines + d_lines,
     "paper_citations": cited}
if "--json" in sys.argv:
    print(json.dumps(s, indent=1)); sys.exit(0)
for k, v in s.items():
    print(f"{k.replace('_', ' '):42} {v}")
