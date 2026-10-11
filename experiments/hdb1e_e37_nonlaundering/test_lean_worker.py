"""Interface/transport adversarial tests using a FAKE worker (not Lean tests)."""
from __future__ import annotations
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from lean_authority import LeanAuthoritativeCore
from lean_worker import LeanPersistentWorker, LeanWorkerError

FAKE = r'''
import json,sys,time
mode=sys.argv[1]
if mode=='silent':
    time.sleep(5)
    sys.exit(0)
if mode=='wrongready':
    print(json.dumps({'ready':'wrong'}),flush=True)
    sys.exit(0)
print(json.dumps({'ready':'e38-lean-worker-v1'}),flush=True)
for raw in sys.stdin:
    x=json.loads(raw)
    if mode=='silentdecision':
        time.sleep(5)
        continue
    if mode=='crash':
        sys.exit(3)
    if mode=='malformed':
        print('garbage',flush=True)
        continue
    if mode=='replay':
        x['token']='wrong-token'
    if mode=='false':
        answer=False
    else:
        answer=True
    print(json.dumps({'token':x['token'],'answers':[answer]}),flush=True)
'''


class PersistentWorkerTransportTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        path = self.root / 'experiments/hdb1e_e37_nonlaundering/CorrespondenceWorker.lean'
        path.parent.mkdir(parents=True)
        path.write_text('-- fake Lean source for process mock')

    def worker(self, mode):
        real_popen = subprocess.Popen
        def fake_popen(*_args, **kwargs):
            return real_popen([sys.executable, '-u', '-c', FAKE, mode], **kwargs)
        patcher = patch('lean_worker.subprocess.Popen', side_effect=fake_popen)
        patcher.start()
        self.addCleanup(patcher.stop)
        worker = LeanPersistentWorker(self.root, startup_timeout=(0.2 if mode=="silent" else 3.0), request_timeout=0.5)
        self.addCleanup(worker.close)
        return worker

    def test_positive_then_positive(self):
        w = self.worker('true')
        w.start()
        self.assertEqual(w.last_status, 'READY')
        self.assertTrue(w.admit_core(('a',), (('a',),), (True,)))
        self.assertTrue(w.admit_core(('b',), (('b',),), (True,)))
        self.assertEqual(w.last_status, 'ADMIT')

    def test_lean_refusal(self):
        w = self.worker('false')
        w.start()
        self.assertFalse(w.admit_core(('a',), (('a',),), (True,)))
        self.assertEqual(w.last_status, 'LEAN_REFUSED')

    def test_invalid_input_refuses(self):
        w = self.worker('true')
        w.start()
        self.assertFalse(w.admit_core(['a'], (('a',),), (True,)))
        self.assertTrue(w.admit_core(('a',), (('a',),), (True,)))

    def test_replay_token_kills_worker(self):
        w = self.worker('replay')
        w.start()
        self.assertFalse(w.admit_core(('a',), (('a',),), (True,)))
        self.assertTrue(w.last_status.startswith('EXECUTION_FAILED'))
        self.assertFalse(w.admit_core(('a',), (('a',),), (True,)))

    def test_malformed_response_kills_worker(self):
        w = self.worker('malformed')
        w.start()
        self.assertFalse(w.admit_core(('a',), (('a',),), (True,)))
        self.assertTrue(w.last_status.startswith('EXECUTION_FAILED'))

    def test_worker_crash_kills_worker(self):
        w = self.worker('crash')
        w.start()
        self.assertFalse(w.admit_core(('a',), (('a',),), (True,)))
        self.assertTrue(w.last_status.startswith('EXECUTION_FAILED'))

    def test_worker_deadline(self):
        w = self.worker('silentdecision')
        w.start()
        self.assertFalse(w.admit_core(('a',), (('a',),), (True,)))
        self.assertTrue(w.last_status.startswith('EXECUTION_FAILED'))

    def test_readiness_deadline(self):
        w = self.worker('silent')
        with self.assertRaises(LeanWorkerError):
            w.start()
        self.assertEqual(w.last_status, 'STARTUP_FAILED')

    def test_bad_readiness(self):
        w = self.worker('wrongready')
        with self.assertRaises(LeanWorkerError):
            w.start()
        self.assertEqual(w.last_status, 'STARTUP_FAILED')

    def test_no_auto_restart(self):
        w = self.worker('true')
        w.start()
        w.close()
        self.assertFalse(w.admit_core(('a',), (('a',),), (True,)))
        with self.assertRaises(LeanWorkerError):
            w.start()

    def test_lean_authority_uses_worker(self):
        w = self.worker('true')
        from lean_authority import LeanAuthoritativeCore
        # The actual LeanAuthoritativeCore constructor independently starts
        # a worker; this test mocks the worker type to exercise that route.
        with patch('lean_worker.LeanPersistentWorker', return_value=w):
            core = LeanAuthoritativeCore(self.root, persistent=True)
        self.assertTrue(core.admit_core(('a',), (('a',),), (True,)))
        core.close()


if __name__ == '__main__':
    unittest.main()
