import AgentSandbox.ActionSurface

namespace AgentSandbox

/-! # Conformance — Tool-Surface Attestation

Before the sandbox is considered **DARM-governed**, the runtime must prove its
tool surface is a subset of the verified profile. This module formalizes that
attestation check.

If the runtime exposes an effect that DARM does not know about, the deployment
is **invalid** — not merely "that call was blocked." This prevents the partial-
deployment trap where some tools are governed and others bypass DARM entirely.

Operational rule: `RuntimeTools ⊆ VerifiedActions` must hold at initialization.
Violation → `DEPLOYMENT_INVALID` → fail-closed. -/

/-- Runtime-reported tool surface. This is **untrusted** input to the attestation.
    The runtime could lie; the attestation is a consistency check, not proof. -/
structure RuntimeManifest where
  exposedMethods : Finset String
  deriving Repr

/-- Verified DARM profile surface. Every method the profile knows how to govern.
    This set is derived from `ActionId` and the adapter's `classify` mapping. -/
def verifiedSurface : Finset String :=
  {"GET /file", "POST /file", "GET /artifactory", "POST /artifactory",
   "LIST /artifactory", "CAPTURE /screen", "GET /http", "EXEC /shell",
   "POST /email", "APPEND /audit", "MODIFY /audit"}

/-- Attestation predicate: the runtime's exposed methods must be a subset of
    the verified surface. If this fails, the deployment is invalid. -/
def attestationResult (manifest : RuntimeManifest) : Prop :=
  manifest.exposedMethods ⊆ verifiedSurface

/-- If attestation fails, there exists a concrete method that the runtime
    exposes but DARM does not know how to govern. -/
theorem attestation_failure_implies_invalid (manifest : RuntimeManifest)
    (h : ¬attestationResult manifest) :
    ∃ method, method ∈ manifest.exposedMethods ∧ method ∉ verifiedSurface := by
  simp [attestationResult] at h
  exact h

/-- A **stronger** attestation: the runtime's exposed methods must be **exactly**
    the verified surface (no more, no less). This prevents both:
    - Undetected new tools (runtime has more than DARM knows)
    - Missing tool claims (runtime claims fewer, hiding shadow paths) -/
def strongAttestationResult (manifest : RuntimeManifest) : Prop :=
  manifest.exposedMethods = verifiedSurface

/-- Strong attestation implies weak attestation. -/
theorem strong_implies_weak (manifest : RuntimeManifest)
    (h : strongAttestationResult manifest) : attestationResult manifest := by
  simp [strongAttestationResult, attestationResult] at h ⊢
  exact Finset.subset_of_eq h

-- ============================================================================
-- HASH-BOUND ATTESTATION (for CI/CD)
-- ============================================================================

/-- The attestation hash binds the runtime manifest to the profile source.
    In CI: `Hash(RuntimeManifest.json)` is compared against `Hash(verifiedSurface)`.
    Mismatch → deployment invalidation. -/
def attestationHashMismatch (runtimeHash : String) (profileHash : String) : Bool :=
  runtimeHash != profileHash

end AgentSandbox
