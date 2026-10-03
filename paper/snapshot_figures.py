#!/usr/bin/env python3
"""Record Darm-Guard's figures, as its scripts/stats.py reports them, with the
Darm-Guard commit, in paper/figures.json. Refreshing the snapshot is a
deliberate act. Usage: paper/snapshot_figures.py --guard PATH"""
import json, os, re, subprocess, sys
g = sys.argv[sys.argv.index("--guard") + 1] if "--guard" in sys.argv else os.path.expanduser("~/darm-guard")

def guard_figures(path):
    s = json.loads(subprocess.run([sys.executable, "scripts/stats.py", "--json"], cwd=path,
                                  capture_output=True, text=True, check=True).stdout)
    claims, = re.match(r"\d+/(\d+)", s["claims fully cited"]).groups()
    complete, = re.match(r"(\d+)/", s["theorem and runtime evidence"]).groups()
    guarantees, = re.match(r"\d+/(\d+)", s["guarantees backed"]).groups()
    b = dict((k, int(v)) for v, k in re.findall(r"(\d+) (\w+)", s["bridges"]))
    sites, = re.match(r"(\d+) found", s["effect sites"]).groups()
    return {"darm_guard_commit": s["commit"], "claims": int(claims), "complete": int(complete),
            "guarantees": int(guarantees), "construction": b.get("construction", 0),
            "proved": b.get("proved", 0), "tested": b.get("tested", 0),
            "effect_sites": int(sites), "mutations": int(s["mutations"])}

if __name__ == "__main__":
    f = guard_figures(g)
    json.dump(f, open("paper/figures.json", "w"), indent=1)
    print("paper/figures.json:", f)
