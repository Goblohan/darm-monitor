#!/usr/bin/env bash
# Build the GRBS library BY NAME and require exit 0. The default target
# (DarmMonitor) does not include GRBS, so a bare `lake build` never
# compiles GRBS roots; that gap let 1e91cfe through with broken files.
set -o pipefail
# Locally (not in CI), default to one Lean thread: a full build with Lean's
# default parallelism can exhaust a small machine's memory (3.8 GB under WSL).
if [ -z "$CI" ] && [ -z "$LEAN_NUM_THREADS" ]; then export LEAN_NUM_THREADS=1; fi
lake build GRBS > /tmp/gate_grbs.txt 2>&1
code=$?
if [ "$code" -ne 0 ]; then
  echo "GATE FAILED: lake build GRBS exited $code"
  grep -E "^error|error:" /tmp/gate_grbs.txt | head -10
  if grep -q "not enough memory\|resource exhausted" /tmp/gate_grbs.txt; then
    echo "(out of memory: this is not a proof failure; free memory or set LEAN_NUM_THREADS=1 and retry)"
  fi
  exit 1
fi
echo "build ok: $(tail -1 /tmp/gate_grbs.txt)"
if [ -f paper/check_citations.py ]; then
  python3 paper/check_citations.py > /tmp/gate_paper.txt 2>&1 || { echo "GATE FAILED: the paper cites theorems that do not exist"; grep MISSING /tmp/gate_paper.txt | head -10; exit 1; }
fi
echo "GATE PASSED: every GRBS root builds, and every theorem the paper cites exists"
