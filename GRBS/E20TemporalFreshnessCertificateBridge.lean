/-
  E20 — TEMPORAL FRESHNESS CERTIFICATE BRIDGE

  Integration experiment:

  E16 provides the formal temporal-freshness proposition.

  E20 tests a stronger bridge than manually supplying an E18 Boolean:

    formal proposition
        ↓
    proof/certificate when the proposition holds
        ↓
    executable decidable result
        ↓
    E18 failure/admission classifier

  The certificate and executable result are deliberately kept distinct.

  This does NOT claim that the finite temporal model corresponds to
  arbitrary physical-world temporal dynamics. That correspondence
  remains an explicit external premise.
-/

import GRBS.E16TemporalFreshness
import GRBS.E18AssuranceFailureWitness

namespace GRBS.E20TemporalFreshnessCertificateBridge

open GRBS.E16TemporalFreshness
open GRBS.E18AssuranceFailureWitness

/--
A proof-carrying freshness certificate for a particular state trajectory
and observation/decision pair.
-/
structure FreshnessCertificate
    (stateFn : Time → St)
    (obs decision : Time) : Prop where
  proof : Fresh obs decision stateFn

/--
The stale E16 model cannot produce a freshness certificate.
-/
theorem stale_model_has_no_freshness_certificate :
    Not (Nonempty (FreshnessCertificate stateAt observedAt decidedAt)) := by
  intro h
  rcases h with ⟨certificate⟩
  exact freshness_fails certificate.proof

/--
The stable E16 model can produce a freshness certificate.

This certificate is constructed from the actual freshness proposition,
rather than from a manually supplied Boolean.
-/
theorem stableFreshnessCertificate :
    FreshnessCertificate stateAtStable observedAt decidedAt := by
  constructor
  simp [Fresh, stateAtStable]

/--
Executable decision procedure for temporal freshness.

The implementation exposes the underlying equality directly so that
the executable checker and the formal Fresh proposition have the same
mathematical content.
-/
def freshnessCheck
    (stateFn : Time → St)
    (obs decision : Time) : Bool :=
  decide (stateFn obs = stateFn decision)

/--
The executable freshness checker is extensionally equivalent to the
formal Fresh proposition for every state trajectory and time pair.
-/
theorem freshness_check_iff
    (stateFn : Time → St)
    (obs decision : Time) :
    freshnessCheck stateFn obs decision = true ↔
      Fresh obs decision stateFn := by
  simp [freshnessCheck, Fresh]

/--
The stale E16 model is rejected by the executable freshness check.
-/
theorem stale_freshness_check :
    freshnessCheck stateAt observedAt decidedAt = false := by
  native_decide

/--
The stable E16 model is accepted by the executable freshness check.
-/
theorem stable_freshness_check :
    freshnessCheck stateAtStable observedAt decidedAt = true := by
  native_decide

/--
The executable freshness result agrees with the formal stale case.
-/
theorem stale_check_matches_formal_failure :
    freshnessCheck stateAt observedAt decidedAt = false
    ∧ Not (Fresh observedAt decidedAt stateAt) := by
  exact ⟨stale_freshness_check, freshness_fails⟩

/--
The executable freshness result agrees with the formally constructed
stable certificate.
-/
theorem stable_check_matches_certificate :
    freshnessCheck stateAtStable observedAt decidedAt = true
    ∧ FreshnessCertificate stateAtStable observedAt decidedAt := by
  exact ⟨stable_freshness_check, stableFreshnessCertificate⟩

/--
The stale executable freshness result flows directly into E18 and
produces the typed temporal-freshness failure witness.
-/
theorem stale_model_rejected_as_temporal_failure :
    evaluateTransfer
      { observationHolds := true
        domainHolds := true
        authorityHolds := true
        freshnessHolds := freshnessCheck stateAt observedAt decidedAt
        semanticHolds := true } =
      TransferResult.rejected
        { kind := FailureKind.temporalFreshness
          evidence := FailureEvidence.temporalFreshness temporalEvidence
          description := "observation expired before decision" } := by
  rw [stale_freshness_check]
  rfl

/--
The stable executable freshness result flows directly into E18.
With the remaining conditions satisfied, the transfer is admitted.
-/
theorem stable_model_admitted_when_other_conditions_hold :
    evaluateTransfer
      { observationHolds := true
        domainHolds := true
        authorityHolds := true
        freshnessHolds := freshnessCheck stateAtStable observedAt decidedAt
        semanticHolds := true } =
      TransferResult.admitted := by
  rw [stable_freshness_check]
  rfl

/--
Aggregate E20 result.

The stale model:
  formal failure
      ↕
  executable false
      ↓
  typed E18 rejection

The stable model:
  formal certificate
      ↕
  executable true
      ↓
  E18 admission
-/
theorem e20_temporal_freshness_certificate_bridge :
    Not (Nonempty (FreshnessCertificate stateAt observedAt decidedAt))
    ∧ freshnessCheck stateAt observedAt decidedAt = false
    ∧ evaluateTransfer
        { observationHolds := true
          domainHolds := true
          authorityHolds := true
          freshnessHolds := freshnessCheck stateAt observedAt decidedAt
          semanticHolds := true } =
        TransferResult.rejected
          { kind := FailureKind.temporalFreshness
            evidence := FailureEvidence.temporalFreshness temporalEvidence
            description := "observation expired before decision" }
    ∧ FreshnessCertificate stateAtStable observedAt decidedAt
    ∧ freshnessCheck stateAtStable observedAt decidedAt = true
    ∧ evaluateTransfer
        { observationHolds := true
          domainHolds := true
          authorityHolds := true
          freshnessHolds := freshnessCheck stateAtStable observedAt decidedAt
          semanticHolds := true } =
        TransferResult.admitted := by
  exact ⟨
    stale_model_has_no_freshness_certificate,
    stale_freshness_check,
    stale_model_rejected_as_temporal_failure,
    stableFreshnessCertificate,
    stable_freshness_check,
    stable_model_admitted_when_other_conditions_hold
  ⟩

end GRBS.E20TemporalFreshnessCertificateBridge
