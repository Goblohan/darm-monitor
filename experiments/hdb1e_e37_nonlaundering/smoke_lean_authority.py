"""Live authoritative Lean smoke test. Requires 'lake' and existing built E38 core.

Not a universal refinement proof. Fails if no positive Lean admission, so a
non-running oracle cannot yield a false success by refusing everything.
"""
import argparse
import json
import sys
from pathlib import Path
from lean_authority import LeanAuthoritativeCore
from correspondence_core import admit_core

CASES = [
    ('positive', ('source:p',), (('source:p',),), (True,), True),
    ('missing-fact', ('source:p',), (('source:q',),), (True,), False),
    ('false-check', ('source:p',), (('source:p',),), (False,), False),
    ('empty-contract', ('source:p',), (), (True,), False),
    ('empty-row', ('source:p',), ((),), (True,), False),
    ('two-rows', ('source:p', 'target:p'), (('source:p',), ('target:p',)), (True,), True),
]


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--repo', required=True)
    args = p.parse_args()
    core = LeanAuthoritativeCore(Path(args.repo))
    results = []
    for name, facts, obligations, checks, expected in CASES:
        lean = core.admit_core(facts, obligations, checks)
        python = admit_core(facts, obligations, checks)
        results.append(dict(case=name, expected=expected, lean=lean, python=python, pass_=lean is expected and python is expected))
    passed = all(x['pass_'] for x in results)
    print(json.dumps({'scope': 'six live typed cases; not universal implementation refinement',
                      'passed':sum(x['pass_'] for x in results),'total':len(results),
                      'status':'PASS' if passed else 'FAIL', 'cases':results}, indent=2))
    return 0 if passed else 1


if __name__ == '__main__':
    sys.exit(main())
