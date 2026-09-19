/-
  E19 — EXECUTABLE COVERAGE → FAILURE CLASSIFIER

  Integration experiment:

  E16a provides an executable finite-domain causal-coverage checker.
  E18 provides the typed ODATS failure classifier.

  E19 tests whether the executable domain-coverage result can actually
  flow into the E18 classification layer.

  This does NOT claim that the finite model represents arbitrary physical
  hardware. That correspondence remains an explicit external premise.
-/

import GRBS.E16aFiniteCausalDomain
import GRBS.E18AssuranceFailureWitness

namespace GRBS.E19ExecutableCoverageToFailureClassifier

open GRBS.E16aFiniteCausalDomain
open GRBS.E18AssuranceFailureWitness

/--
The original E16a model has an executable causal-coverage failure.
Feed that result directly into the E18 domain condition.
-/
theorem uncovered_model_rejected_as_domain_failure :
    evaluateTransfer
      { observationHolds := true
        domainHolds := checkCoverage causeableBool modeledBool
        authorityHolds := true
        freshnessHolds := true
        semanticHolds := true } =
      TransferResult.rejected
        { kind := FailureKind.domainCompleteness
          evidence := FailureEvidence.domainCompleteness domainEvidence
          description := "domain completeness failed" } := by
  rw [checker_detects_gap]
  rfl

/--
The repaired E16a model has executable causal coverage.
When the remaining ODATS conditions hold, E18 admits the transfer.
-/
theorem repaired_model_admitted_when_other_conditions_hold :
    evaluateTransfer
      { observationHolds := true
        domainHolds := checkCoverage causeableBool modeledFixedBool
        authorityHolds := true
        freshnessHolds := true
        semanticHolds := true } =
      TransferResult.admitted := by
  rw [checker_confirms_fix]
  rfl

/--
Aggregate E19 result: the executable coverage checker is connected to
the E18 failure/admission interface in both the failing and repaired
finite-domain cases.
-/
theorem e19_executable_coverage_composes_with_failure_classifier :
    evaluateTransfer
      { observationHolds := true
        domainHolds := checkCoverage causeableBool modeledBool
        authorityHolds := true
        freshnessHolds := true
        semanticHolds := true } =
      TransferResult.rejected
        { kind := FailureKind.domainCompleteness
          evidence := FailureEvidence.domainCompleteness domainEvidence
          description := "domain completeness failed" }
    ∧
    evaluateTransfer
      { observationHolds := true
        domainHolds := checkCoverage causeableBool modeledFixedBool
        authorityHolds := true
        freshnessHolds := true
        semanticHolds := true } =
      TransferResult.admitted := by
  constructor
  · exact uncovered_model_rejected_as_domain_failure
  · exact repaired_model_admitted_when_other_conditions_hold

end GRBS.E19ExecutableCoverageToFailureClassifier
