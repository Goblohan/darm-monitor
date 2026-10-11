"""EXPERIMENTAL strict E38 relying-consumer profile.

Requires independently challenged exact-head witness and executable Lean
admission for the normalized, verified warrant core. It authenticates a
snapshot; it DOES NOT authorize/execute effects, mediate other consumers,
prove CPython execution, or establish production witness independence.
"""
from __future__ import annotations

from typing import Callable

from correspondence_runtime import PinnedRelianceVerifier, TrustedReliance
from guard_monotonic_bridge import MonotonicWitnessStore
from lean_authority import LeanAuthoritativeCore
from verifier import Policy, Verdict
from witness_exact_head import ExactHeadOnlineGate


class StrictRelianceGate:
    """Consumer must exclusively use this profile at its relying boundary.

    Keys, policy, target and witness transport must be provisioned by the
    consumer, not selected from any agent request. Lean runner/filesystem
    integrity is an external platform assumption.
    """
    def __init__(self, policy: Policy, trusted: TrustedReliance,
                 store: MonotonicWitnessStore, lean_core: LeanAuthoritativeCore,
                 fetch_challenge: Callable[[bytes], bytes]):
        if type(lean_core) is not LeanAuthoritativeCore:
            raise ValueError("genuine-lean-executor-required")
        pinned = PinnedRelianceVerifier(policy, trusted, store,
                                        admission_core=lean_core.admit_core)
        self._gate = ExactHeadOnlineGate(pinned, fetch_challenge)

    def decide_json(self, request: bytes, now: int, attestation: bytes,
                    content: bytes, audit: bytes, checkpoints: bytes) -> Verdict:
        """Admit only when trusted-witness head, Guard evidence and Lean all agree.

        The return's action_authorized field is a request observation, NOT
        an independently verified right to execute an effect. Consumers must
        separately enforce effect authority and complete mediation.
        """
        try:
            return self._gate.decide_json(
                request, now, attestation, content, audit, checkpoints)
        except (OSError, TimeoutError, ValueError, TypeError, RuntimeError,
                UnicodeError, RecursionError):
            return Verdict(False, ("strict:verification-error",), (), (), False)
