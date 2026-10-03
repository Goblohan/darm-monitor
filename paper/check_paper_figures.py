#!/usr/bin/env python3
"""The figures the paper states match paper/figures.json (Darm-Guard's figures,
recorded with its commit by snapshot_figures.py). Each figure sentence in
core.md must be found exactly once and state the recorded number, in digits or
words. With --guard PATH (Darm-Guard checked out), the snapshot must also match
Darm-Guard's current figures. Every other mention of a number of claims,
guarantees, mutations or effect sites in paper/ is listed for review.
Usage: paper/check_paper_figures.py [--guard PATH]"""
import glob, json, os, re, sys
UNITS = "zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen " \
        "sixteen seventeen eighteen nineteen".split()
TENS = {"twenty": 20, "thirty": 30, "forty": 40, "fifty": 50, "sixty": 60, "seventy": 70, "eighty": 80, "ninety": 90}
def num(w):
    w = w.lower().strip(".,;:")
    if w.isdigit():
        return int(w)
    if w in UNITS:
        return UNITS.index(w)
    if w in TENS:
        return TENS[w]
    if "-" in w:
        a, b = w.split("-", 1)
        if a in TENS and b in UNITS:
            return TENS[a] + UNITS.index(b)
    return None
W = r"([A-Za-z]+(?:-[a-z]+)?|\d+)"
SENTENCES = [   # (template with {} for each number, the figures they state)
    ("threat model lists {} guarantees", ["guarantees"]),
    ("each of the graph's {} claims", ["claims"]),
    ("Of the {} claims, {} have both", ["claims", "complete"]),
    ("{} claim by construction, {} proved, {} tested", ["construction", "proved", "tested"]),
    ("every effect site in the package, {} in all", ["effect_sites"]),
    ("{} mutations, covering", ["mutations"]),
]
fig = json.load(open("paper/figures.json"))
core = open("paper/core.md").read()
bad = []
for tmpl, keys in SENTENCES:
    pat = r"\s+".join(re.escape(w).replace(re.escape("{}"), W) for w in tmpl.split())
    found = re.findall(pat, core, re.I)
    if len(found) != 1:
        bad.append(f"'{tmpl}': found {len(found)} times in core.md (expected once)")
        continue
    vals = found[0] if isinstance(found[0], tuple) else (found[0],)
    for k, v in zip(keys, vals):
        if num(v) != fig[k]:
            bad.append(f"'{tmpl}': the paper says {v} {k}, the snapshot says {fig[k]}")
if "--guard" in sys.argv:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from snapshot_figures import guard_figures
    now = guard_figures(sys.argv[sys.argv.index("--guard") + 1])
    stale = {k: (fig.get(k), v) for k, v in now.items() if k != "darm_guard_commit" and fig.get(k) != v}
    for k, (was, is_) in stale.items():
        bad.append(f"snapshot is stale: {k} recorded {was}, Darm-Guard {now['darm_guard_commit']} reports {is_}")
ALLOWED = {"claims": {fig["claims"], fig["complete"]}, "guarantees": {fig["guarantees"]},
           "mutations": {fig["mutations"]}, "effect sites": {fig["effect_sites"]}}
notes = []   # other mentions whose number differs from the snapshot: possibly stale, for review
for f in sorted(glob.glob("paper/*.md")):
    for i, line in enumerate(open(f), 1):
        for m in re.finditer(W + r"\s+(claims|guarantees|mutations|effect sites)\b", line, re.I):
            n = num(m.group(1))
            if n is not None and n > 2 and n not in ALLOWED[m.group(2).lower()]:
                notes.append(f"{f}:{i}: {m.group(0)} (the snapshot says {sorted(ALLOWED[m.group(2).lower()])})")
for b in bad:
    print("FIGURE", b)
for n in notes:
    print("NOTE  ", n)
print(f"paper figures: {len(SENTENCES) - len([b for b in bad if not b.startswith('snapshot')])}/{len(SENTENCES)} "
      f"sentences match the snapshot of Darm-Guard {fig['darm_guard_commit']}"
      + ("" if "--guard" not in sys.argv else ("; snapshot current" if not any(b.startswith("snapshot") for b in bad)
                                               else "; snapshot STALE")))
sys.exit(1 if bad else 0)
