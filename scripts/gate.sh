#!/usr/bin/env bash
# Build the GRBS library BY NAME and require exit 0. The default target
# (DarmMonitor) does not include GRBS, so a bare `lake build` never
# compiles GRBS roots; that gap let 1e91cfe through with broken files.
set -o pipefail
lake build GRBS > /tmp/gate_grbs.txt 2>&1
code=$?
if [ "$code" -ne 0 ]; then
  echo "GATE FAILED: lake build GRBS exited $code"
  grep -E "^error|error:" /tmp/gate_grbs.txt | head -10
  exit 1
fi
echo "GATE PASSED: $(tail -1 /tmp/gate_grbs.txt)"
