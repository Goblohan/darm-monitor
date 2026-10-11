"""Small operational warrant core mirrored by E38OperationalCore.lean.

Facts are labels released by the existing cryptographic verifier, NOT world
truth. The caller owns the policy and the provenance of every supplied fact.
Tests against Lean establish finite conformance, not Python refinement.
"""
from __future__ import annotations


def admit_core(facts: tuple[str, ...], obligations: tuple[tuple[str, ...], ...],
               checks: tuple[bool, ...]) -> bool:
    """A nonempty contract, nonempty rows, and every required fact present.

    Strict bool identity avoids treating arbitrary truthy values as checks.
    Internal typed interface. Wire parsing and cryptography stay outside it.
    """
    available = frozenset(facts)
    return (bool(obligations) and all(c is True for c in checks)
            and all(bool(row) and all(a in available for a in row)
                    for row in obligations))


def normalize_obligations(required, rules):
    """Missing or malformed mappings produce an unsatisfied empty row."""
    rows = []
    for name in sorted(required):
        rule = rules.get(name)
        if (rule is None or rule.channel not in {"source", "target"}
                or not rule.requires or any(type(x) is not str or not x for x in rule.requires)):
            rows.append(())
        else:
            rows.append(tuple(rule.channel + ":" + x for x in rule.requires))
    return tuple(rows)


def normalize_facts(source_claims, target_claims):
    return tuple(sorted("source:" + x for x in source_claims)) + tuple(
        sorted("target:" + x for x in target_claims))
