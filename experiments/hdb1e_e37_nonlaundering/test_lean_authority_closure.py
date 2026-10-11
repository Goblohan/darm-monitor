"""Interface tests for fail-closed Lean-backed experimental admission core."""
from __future__ import annotations
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from lean_authority import LeanAuthoritativeCore, validate_domain


class LeanAuthorityInterface(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        oracle = root / 'experiments/hdb1e_e37_nonlaundering/CorrespondenceOracle.lean'
        oracle.parent.mkdir(parents=True)
        oracle.write_text('-- test oracle path')
        self.core = LeanAuthoritativeCore(root)

    def test_valid_typed_domain(self):
        self.assertTrue(validate_domain(('source:p',), (('source:p',),), (True, False)))

    def test_invalid_inputs_refuse_before_oracle(self):
        invalid = [
            (['source:p'], (('source:p',),), (True,)),
            (('source:p',), (["source:p"],), (True,)),
            (('source:p',), (('source:p',),), (1,)),
            (('source:p\\ud800',), (('source:p',),), (True,)),
            (('',), (('source:p',),), (True,)),
            (('source:p',), (('source:p',),), ('true',)),
        ]
        with patch('lean_authority.subprocess.run') as run:
            for args in invalid:
                with self.subTest(args=str(args)):
                    self.assertFalse(self.core.admit_core(*args))
            run.assert_not_called()

    def test_valid_lean_admit_and_refuse(self):
        with patch('lean_authority.subprocess.run') as run:
            run.return_value = subprocess.CompletedProcess([], 0, '[true]\n', '')
            self.assertTrue(self.core.admit_core(('source:p',), (('source:p',),), (True,)))
            run.return_value = subprocess.CompletedProcess([], 0, '[false]\n', '')
            self.assertFalse(self.core.admit_core(('source:p',), (('source:p',),), (True,)))

    def test_fail_closed_on_crash_malformed_timeout(self):
        with patch('lean_authority.subprocess.run') as run:
            for result in [subprocess.CompletedProcess([], 1, '[true]\n', 'error'),
                           subprocess.CompletedProcess([], 0, 'garbage', ''),
                           subprocess.CompletedProcess([], 0, '[1]', ''),
                           subprocess.CompletedProcess([], 0, '[true,true]', '')]:
                run.return_value = result
                self.assertFalse(self.core.admit_core(('source:p',), (('source:p',),), (True,)))
            run.side_effect = subprocess.TimeoutExpired('lean', 20)
            self.assertFalse(self.core.admit_core(('source:p',), (('source:p',),), (True,)))


if __name__ == '__main__':
    unittest.main()
