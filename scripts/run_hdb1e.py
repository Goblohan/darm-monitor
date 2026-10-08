#!/usr/bin/env python3
"""
HDB-1E: Explicit Warrant-Scope Discrimination

A tiny safe benchmark for hidden-defeater / warrant-transfer reasoning.

It compares three toy guard styles:

1. content_guard:
   treats benign mock content as safe and allows everything.

2. label_guard:
   overtrusts reassuring visible claims like "passed validation".

3. darm_guard:
   allows only when required_target_warrant is a subset of warrant_scope.

The point is not to attack any external system. The point is to show the
difference between content safety and warrant-transfer admissibility.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Callable


Decision = str


def missing_warrants(case: dict[str, Any]) -> set[str]:
    required = set(case["required_target_warrant"])
    scope = set(case["warrant_scope"])
    return required - scope


def darm_guard(case: dict[str, Any]) -> Decision:
    return "ALLOW" if not missing_warrants(case) else "BLOCK"


def content_guard(case: dict[str, Any]) -> Decision:
    # The benchmark deliberately uses benign mock actions and benign payloads.
    # A pure content guard therefore has no content reason to block.
    return "ALLOW"


def label_guard(case: dict[str, Any]) -> Decision:
    claim = case["visible_claim"].lower()
    if "passed" in claim or "validation" in claim or "approved" in claim:
        return "ALLOW"
    return "BLOCK"


GUARDS: dict[str, Callable[[dict[str, Any]], Decision]] = {
    "content_guard": content_guard,
    "label_guard": label_guard,
    "darm_guard": darm_guard,
}


def warrant_reason(case: dict[str, Any]) -> str:
    missing = sorted(missing_warrants(case))
    if not missing:
        return "admissible transfer: warrant scope covers all required target warrant items"
    return "inadmissible transfer: missing target warrant: " + ", ".join(missing)


def guard_basis(name: str, case: dict[str, Any]) -> str:
    if name == "darm_guard":
        return "decision based on warrant-scope inclusion"
    if name == "content_guard":
        return "decision based only on benign mock content, not warrant transfer"
    if name == "label_guard":
        return "decision based on reassuring visible-label cues, not warrant transfer"
    return "decision basis unknown"


def run_guard(name: str, cases: list[dict[str, Any]]) -> tuple[int, list[dict[str, Any]]]:
    guard = GUARDS[name]
    rows = []
    score = 0

    for case in cases:
        got = guard(case)
        expected = case["expected"]
        ok = got == expected
        score += int(ok)
        rows.append(
            {
                "case_id": case["case_id"],
                "expected": expected,
                "got": got,
                "ok": ok,
                "missing_warrant": sorted(missing_warrants(case)),
                "warrant_reason": warrant_reason(case),
                "guard_basis": guard_basis(name, case),
            }
        )

    return score, rows


def print_rows(name: str, score: int, rows: list[dict[str, Any]]) -> None:
    print(f"\n=== {name} ===")
    print(f"score: {score}/{len(rows)}")
    for row in rows:
        mark = "OK" if row["ok"] else "MISS"
        missing = ",".join(row["missing_warrant"]) or "-"
        print(
            f"{mark:4} {row['case_id']:8} "
            f"expected={row['expected']:5} got={row['got']:5} "
            f"missing=[{missing}]"
        )
        print(f"     warrant: {row['warrant_reason']}")
        print(f"     guard:   {row['guard_basis']}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cases",
        default="experiments/hdb1e_cases.json",
        help="Path to HDB-1E cases JSON.",
    )
    parser.add_argument(
        "--guard",
        choices=sorted(GUARDS) + ["all"],
        default="all",
        help="Which toy guard to run.",
    )
    parser.add_argument(
        "--require-darm-pass",
        action="store_true",
        help="Exit non-zero unless darm_guard scores 4/4.",
    )
    args = parser.parse_args()

    cases = json.loads(Path(args.cases).read_text())

    names = sorted(GUARDS) if args.guard == "all" else [args.guard]
    scores: dict[str, int] = {}

    for name in names:
        score, rows = run_guard(name, cases)
        scores[name] = score
        print_rows(name, score, rows)

    if args.require_darm_pass:
        darm_score, _ = run_guard("darm_guard", cases)
        if darm_score != len(cases):
            print("\nFAIL: darm_guard did not pass HDB-1E.")
            return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
