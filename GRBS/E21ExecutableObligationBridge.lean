/-
  E21 — GENERIC EXECUTABLE OBLIGATION BRIDGE

  Abstraction experiment:

  E19 and E20 establish concrete executable bridges for:
    - causal domain coverage
    - temporal freshness

  E21 asks whether the common structure can be represented once:

      formal obligation P
             ↕
      executable Bool checker

  The central contract is:

      check = true ↔ P

  This is an abstraction of the formal-to-executable correspondence.
  It does NOT establish physical-world correspondence or enforcement
  correspondence.
-/

import E16aFiniteCausalDomain
import E16TemporalFreshness
import E20TemporalFreshnessCertificateBridge

namespace GRBS.E21ExecutableObligationBridge

open GRBS.E16aFiniteCausalDomain
open GRBS.E16TemporalFreshness
open GRBS.E20TemporalFreshnessCertificateBridge

/--
A generic bridge between a formal assurance proposition and an
executable Boolean checker.

The correspondence theorem is part of the bridge itself rather than
being an external assertion about the checker.
-/
structure ExecutableObligationBridge (P : Prop) where
  check : Bool
  correspondence : check = true ↔ P

/--
If an executable obligation checker returns true, the formal
obligation follows from the bridge correspondence.
-/
theorem check_true_implies_obligation
    {P : Prop}
    (bridge : ExecutableObligationBridge P)
    (hcheck : bridge.check = true) :
    P :=
  bridge.correspondence.mp hcheck

/--
If the formal obligation holds, the executable checker must return
true.
-/
theorem obligation_implies_check_true
    {P : Prop}
    (bridge : ExecutableObligationBridge P)
    (hP : P) :
    bridge.check = true :=
  bridge.correspondence.mpr hP

/--
If the executable checker returns false, the formal obligation does
not hold.
-/
theorem check_false_implies_not_obligation
    {P : Prop}
    (bridge : ExecutableObligationBridge P)
    (hcheck : bridge.check = false) :
    Not P := by
  intro hP
  have htrue : bridge.check = true :=
    obligation_implies_check_true bridge hP
  simp [hcheck] at htrue

/--
The E20 temporal freshness checker is an instance of the generic
obligation bridge.
-/
def temporalFreshnessBridge :
    ExecutableObligationBridge
      (Fresh observedAt decidedAt stateAt) :=
  { check := freshnessCheck stateAt observedAt decidedAt
    correspondence := freshness_check_iff stateAt observedAt decidedAt }

/--
The stale E20 model therefore gives a formally failed obligation
through the generic bridge.
-/
theorem temporal_stale_obligation_fails :
    temporalFreshnessBridge.check = false
    ∧ Not (Fresh observedAt decidedAt stateAt) := by
  constructor
  · exact stale_freshness_check
  · exact check_false_implies_not_obligation
      temporalFreshnessBridge
      stale_freshness_check

/--
The E20 stable model can likewise be represented by the generic
bridge.
-/
def stableTemporalFreshnessBridge :
    ExecutableObligationBridge
      (Fresh observedAt decidedAt stateAtStable) :=
  { check := freshnessCheck stateAtStable observedAt decidedAt
    correspondence := freshness_check_iff stateAtStable observedAt decidedAt }

/--
The stable formal obligation and executable checker agree.
-/
theorem temporal_stable_obligation_holds :
    stableTemporalFreshnessBridge.check = true
    ∧ Fresh observedAt decidedAt stateAtStable := by
  constructor
  · exact stable_freshness_check
  · exact stableFreshnessCertificate.proof

/--
The repaired E16a causal-coverage checker is represented by the same
generic bridge.

Unlike the deliberately broken model, both the executable checker and
the formal causal-coverage obligation hold here. This makes the
correspondence non-vacuous.
-/
def causalCoverageFixedBridge :
    ExecutableObligationBridge CausalCoverageFixed :=
  { check := checkCoverage causeableBool modeledFixedBool
    correspondence := by
      constructor
      · intro _
        exact coverage_fixed_holds
      · intro _
        exact checker_confirms_fix }

/--
The repaired finite causal model therefore agrees at both levels:
the executable checker succeeds and the formal obligation holds.
-/
theorem causal_coverage_fixed_obligation_holds :
    causalCoverageFixedBridge.check = true
    ∧ CausalCoverageFixed := by
  constructor
  · exact checker_confirms_fix
  · exact coverage_fixed_holds

/--
The original E16a model remains an explicit negative witness, but it is
not used as an executable/formal correspondence bridge. It records the
distinction between a failed obligation and a repaired obligation.
-/
theorem causal_coverage_original_model_fails :
    checkCoverage causeableBool modeledBool = false
    ∧ Not CausalCoverage := by
  constructor
  · exact checker_detects_gap
  · exact coverage_fails

/--
The generic bridge captures both directions demonstrated by the
temporal and causal experiments:

  stale temporal model  -> executable failure + formal failure
  stable temporal model -> executable success + formal satisfaction
  broken causal model   -> executable failure + formal failure
  repaired causal model -> executable success + formal satisfaction
-/
theorem e21_generic_obligation_bridge :
    temporalFreshnessBridge.check = false
    ∧ Not (Fresh observedAt decidedAt stateAt)
    ∧ stableTemporalFreshnessBridge.check = true
    ∧ Fresh observedAt decidedAt stateAtStable
    ∧ causalCoverageFixedBridge.check = true
    ∧ CausalCoverageFixed
    ∧ checkCoverage causeableBool modeledBool = false
    ∧ Not CausalCoverage := by
  exact ⟨
    stale_freshness_check,
    freshness_fails,
    stable_freshness_check,
    stableFreshnessCertificate.proof,
    checker_confirms_fix,
    coverage_fixed_holds,
    checker_detects_gap,
    coverage_fails
  ⟩

end GRBS.E21ExecutableObligationBridge
