"""Opt-in, single-owner Lean oracle worker with separate startup/read deadlines.

Refuses on every transport error and never invokes the Python reference
predicate. This is NOT a CPython refinement proof or hardened execution sandbox.

Linux/WSL only. Toolchain/source integrity and process isolation are external
assumptions. A crashed worker is permanently closed; restart requires explicitly
creating a new worker and completing a fresh readiness handshake.
"""
from __future__ import annotations

import json
import os
import secrets
import select
import signal
import subprocess
import threading
import time
from pathlib import Path

from lean_authority import (MAX_BYTES, validate_domain)

PROTOCOL = "e38-lean-worker-v1"
MAX_LINE = 4096


class LeanWorkerError(RuntimeError):
    pass


class LeanPersistentWorker:
    def __init__(self, root: str | Path, *, startup_timeout: float = 120.0,
                 request_timeout: float = 8.0):
        self.root = Path(root).resolve()
        self.oracle = self.root / "experiments/hdb1e_e37_nonlaundering/CorrespondenceWorker.lean"
        if not (0 < startup_timeout <= 300 and 0 < request_timeout <= 60):
            raise ValueError("invalid-worker-deadlines")
        self.startup_timeout = startup_timeout
        self.request_timeout = request_timeout
        self._proc = None
        self._read_buffer = bytearray()
        self._lock = threading.Lock()
        self._owner_pid = os.getpid()
        self.last_status = "NOT_STARTED"

    def __enter__(self):
        self.start()
        return self

    def __exit__(self, *_exc):
        self.close()

    def _readline(self, deadline: float) -> bytes:
        assert self._proc is not None
        fd = self._proc.stdout.fileno()
        while True:
            offset = self._read_buffer.find(b"\n")
            if offset >= 0:
                line = bytes(self._read_buffer[:offset])
                del self._read_buffer[:offset+1]
                return line
            if len(self._read_buffer) > MAX_LINE:
                raise LeanWorkerError("oversize-output")
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise LeanWorkerError("deadline-exceeded")
            readable, _, _ = select.select([fd], [], [], remaining)
            if not readable:
                raise LeanWorkerError("deadline-exceeded")
            data = os.read(fd, 2048)
            if not data:
                raise LeanWorkerError("oracle-eof")
            self._read_buffer.extend(data)

    @staticmethod
    def _parse(line: bytes) -> dict:
        if len(line) > MAX_LINE:
            raise LeanWorkerError("oversize-output")
        try:
            obj = json.loads(line.decode("utf-8"))
        except (UnicodeError, ValueError) as exc:
            raise LeanWorkerError("malformed-output") from exc
        if type(obj) is not dict:
            raise LeanWorkerError("unexpected-output-shape")
        return obj

    def start(self):
        with self._lock:
            if os.getpid() != self._owner_pid:
                raise LeanWorkerError("forked-worker-handle")
            if self._proc is not None or self.last_status != "NOT_STARTED":
                raise LeanWorkerError("worker-already-started-or-closed")
            if not self.oracle.is_file():
                self.last_status = "UNAVAILABLE"
                raise LeanWorkerError("worker-source-missing")
            self.last_status = "STARTING"
            try:
                self._proc = subprocess.Popen(
                    ["lake", "env", "lean", "--run", str(self.oracle)],
                    cwd=self.root, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                    stderr=subprocess.DEVNULL, bufsize=0, start_new_session=True)
                ready = self._parse(self._readline(time.monotonic() + self.startup_timeout))
                if ready != {"ready": PROTOCOL}:
                    raise LeanWorkerError("readiness-handshake-invalid")
                if self._proc.poll() is not None:
                    raise LeanWorkerError("worker-exited-after-handshake")
                self.last_status = "READY"
            except (OSError, ValueError, LeanWorkerError) as exc:
                self._stop_locked("STARTUP_FAILED")
                raise LeanWorkerError("startup-failed") from exc

    def _stop_locked(self, status: str):
        proc = self._proc
        self._proc = None
        self.last_status = status
        self._read_buffer.clear()
        if proc is None:
            return
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
        for stream in (proc.stdin, proc.stdout):
            try:
                stream.close()
            except OSError:
                pass
        try:
            proc.wait(timeout=3)
        except subprocess.TimeoutExpired:
            pass

    def close(self):
        with self._lock:
            if os.getpid() != self._owner_pid:
                # Forked processes may not own this process group.
                self._proc = None
                self.last_status = "FORKED"
                return
            self._stop_locked("CLOSED")

    def admit_core(self, facts, obligations, checks) -> bool:
        if not validate_domain(facts, obligations, checks):
            self.last_status = "INVALID_INPUT"
            return False
        with self._lock:
            if os.getpid() != self._owner_pid or self._proc is None or self.last_status not in ("READY", "ADMIT", "LEAN_REFUSED", "INVALID_INPUT"):
                self.last_status = "UNAVAILABLE"
                return False
            token = secrets.token_hex(16)
            payload = json.dumps({"token": token, "cases": [
                {"facts": facts, "obligations": obligations, "checks": checks}
            ]}, ensure_ascii=True, separators=(",", ":")).encode("ascii") + b"\n"
            if len(payload) > MAX_BYTES:
                self.last_status = "INVALID_INPUT"
                return False
            try:
                if self._proc.poll() is not None:
                    raise LeanWorkerError("worker-exited")
                self._proc.stdin.write(payload)
                self._proc.stdin.flush()
                response = self._parse(self._readline(time.monotonic() + self.request_timeout))
                if set(response) != {"token", "answers"} or response["token"] != token:
                    raise LeanWorkerError("response-token-or-shape-mismatch")
                answers = response["answers"]
                if type(answers) is not list or len(answers) != 1 or type(answers[0]) is not bool:
                    raise LeanWorkerError("invalid-decision-output")
                admitted = answers[0]
                self.last_status = "ADMIT" if admitted else "LEAN_REFUSED"
                return admitted
            except (OSError, ValueError, TypeError, LeanWorkerError) as exc:
                self._stop_locked("EXECUTION_FAILED:" + str(exc))
                return False
