/-
  E22 — PARAMETERIZED EXECUTABLE PREDICATE BRIDGE

  E21 established the instance-level contract:

      check = true ↔ P

  E22 generalizes this to executable predicates over an input domain:

      check x = true ↔ P x

  Temporal freshness is naturally represented this way.

  Finite causal coverage has a different logical shape: it is a
  universal property over a finite transition domain. E22 therefore
  represents its pointwise transition predicate separately rather than
  incorrectly identifying the pointwise predicate with the universal
  coverage obligation.

  This remains a formal-to-executable correspondence only. It does
  not establish physical-world correspondence or enforcement
  correspondence.
-/

import GRBS.E16aFiniteCausalDomain
import GRBS.E16TemporalFreshness
import GRBS.E20TemporalFreshnessCertificateBridge
import GRBS.E21ExecutableObligationBridge

namespace GRBS.E22ParameterizedExecutablePredicateBridge

open GRBS.E16aFiniteCausalDomain
open GRBS.E16TemporalFreshness
open GRBS.E20TemporalFreshnessCertificateBridge
open GRBS.E21ExecutableObligationBridge

/--
A parameterized bridge between an executable Boolean predicate and a
formal predicate over the same input domain.
-/
structure ExecutablePredicateBridge (α : Type) (P : α → Prop) where
  check : α → Bool
  correspondence : ∀ x, check x = true ↔ P x

/--
Executable success implies the corresponding formal predicate.
-/
theorem check_true_implies_predicate
    {α : Type}
    {P : α → Prop}
    (bridge : ExecutablePredicateBridge α P)
    (x : α)
    (hcheck : bridge.check x = true) :
    P x :=
  (bridge.correspondence x).mp hcheck

/--
Formal satisfaction implies executable success.
-/
theorem predicate_implies_check_true
    {α : Type}
    {P : α → Prop}
    (bridge : ExecutablePredicateBridge α P)
    (x : α)
    (hP : P x) :
    bridge.check x = true :=
  (bridge.correspondence x).mpr hP

/--
Executable failure implies formal failure.
-/
theorem check_false_implies_not_predicate
    {α : Type}
    {P : α → Prop}
    (bridge : ExecutablePredicateBridge α P)
    (x : α)
    (hcheck : bridge.check x = false) :
    Not (P x) := by
  intro hP
  have htrue : bridge.check x = true :=
    predicate_implies_check_true bridge x hP
  simp [hcheck] at htrue

/--
The temporal freshness input domain.
-/
structure FreshnessInput where
  stateFn : GRBS.E16TemporalFreshness.Time →
    GRBS.E16TemporalFreshness.St
  obs : GRBS.E16TemporalFreshness.Time
  decision : GRBS.E16TemporalFreshness.Time

def freshPredicate (x : FreshnessInput) : Prop :=
  GRBS.E16TemporalFreshness.Fresh
    x.obs x.decision x.stateFn

def freshCheck (x : FreshnessInput) : Bool :=
  GRBS.E20TemporalFreshnessCertificateBridge.freshnessCheck
    x.stateFn x.obs x.decision

/--
E20's general freshness correspondence is an instance of the
parameterized predicate bridge.
-/
def temporalPredicateBridge :
    ExecutablePredicateBridge FreshnessInput freshPredicate :=
  { check := freshCheck
    correspondence := by
      intro x
      exact
        GRBS.E20TemporalFreshnessCertificateBridge.freshness_check_iff
          x.stateFn x.obs x.decision }

/--
The stale temporal input.
-/
def staleFreshnessInput : FreshnessInput :=
  { stateFn := GRBS.E16TemporalFreshness.stateAt
    obs := GRBS.E16TemporalFreshness.observedAt
    decision := GRBS.E16TemporalFreshness.decidedAt }

/--
The stable temporal input.
-/
def stableFreshnessInput : FreshnessInput :=
  { stateFn := GRBS.E16TemporalFreshness.stateAtStable
    obs := GRBS.E16TemporalFreshness.observedAt
    decision := GRBS.E16TemporalFreshness.decidedAt }

/--
The stale temporal input is rejected at both levels.
-/
theorem stale_parameterized_bridge_fails :
    temporalPredicateBridge.check staleFreshnessInput = false
    ∧ Not (freshPredicate staleFreshnessInput) := by
  constructor
  · exact
      GRBS.E20TemporalFreshnessCertificateBridge.stale_freshness_check
  · exact
      GRBS.E16TemporalFreshness.freshness_fails

/--
The stable temporal input is accepted at both levels.
-/
theorem stable_parameterized_bridge_holds :
    temporalPredicateBridge.check stableFreshnessInput = true
    ∧ freshPredicate stableFreshnessInput := by
  constructor
  · exact
      GRBS.E20TemporalFreshnessCertificateBridge.stable_freshness_check
  · exact
      GRBS.E20TemporalFreshnessCertificateBridge.stableFreshnessCertificate.proof

/--
The same parameterized correspondence applies to every freshness
input, not merely the two concrete E20 examples.
-/
theorem temporal_parameterized_correspondence
    (x : FreshnessInput) :
    temporalPredicateBridge.check x = true ↔
      freshPredicate x :=
  temporalPredicateBridge.correspondence x

/--
The causal transition domain.
-/
structure CausalTransitionInput where
  source : GRBS.E16aFiniteCausalDomain.St
  target : GRBS.E16aFiniteCausalDomain.St

/--
Pointwise causal coverage for the original model.
-/
def causalCoveragePredicate (x : CausalTransitionInput) : Prop :=
  GRBS.E16aFiniteCausalDomain.causeableP
      x.source x.target
    →
  GRBS.E16aFiniteCausalDomain.modeledP
      x.source x.target

/--
Executable pointwise checker for the original causal model.
-/
def causalCoverageCheck (x : CausalTransitionInput) : Bool :=
  !GRBS.E16aFiniteCausalDomain.causeableBool x.source x.target ||
    GRBS.E16aFiniteCausalDomain.modeledBool x.source x.target

/--
The pointwise causal checker has the same executable/formal
correspondence shape.
-/
def causalTransitionBridge :
    ExecutablePredicateBridge
      CausalTransitionInput
      causalCoveragePredicate :=
  { check := causalCoverageCheck
    correspondence := by
      intro x
      rcases x with ⟨source, target⟩
      cases source <;> cases target <;>
        constructor <;> intro h <;>
        simp [causalCoverageCheck, causalCoveragePredicate,
          GRBS.E16aFiniteCausalDomain.causeableP,
          GRBS.E16aFiniteCausalDomain.modeledP,
          GRBS.E16aFiniteCausalDomain.causeableBool,
          GRBS.E16aFiniteCausalDomain.modeledBool] at h ⊢ }

/--
The original uncovered transition s0 → s2 is rejected at both levels.
-/
def originalCausalTransition : CausalTransitionInput :=
  { source := GRBS.E16aFiniteCausalDomain.St.s0
    target := GRBS.E16aFiniteCausalDomain.St.s2 }

theorem original_causal_transition_fails :
    causalTransitionBridge.check originalCausalTransition = false
    ∧ Not (causalCoveragePredicate originalCausalTransition) := by
  constructor
  · native_decide
  · intro h
    have hcause :
        GRBS.E16aFiniteCausalDomain.causeableP
          GRBS.E16aFiniteCausalDomain.St.s0
          GRBS.E16aFiniteCausalDomain.St.s2 :=
      rfl
    have hmodel := h hcause
    simp [originalCausalTransition,
      GRBS.E16aFiniteCausalDomain.modeledP,
      GRBS.E16aFiniteCausalDomain.modeledBool] at hmodel

/--
The repaired causal transition predicate.
-/
def causalCoverageFixedPredicate (x : CausalTransitionInput) : Prop :=
  GRBS.E16aFiniteCausalDomain.causeableP
      x.source x.target
    →
  GRBS.E16aFiniteCausalDomain.modeledFixedP
      x.source x.target

/--
Executable pointwise checker for the repaired causal model.
-/
def causalCoverageFixedCheck (x : CausalTransitionInput) : Bool :=
  !GRBS.E16aFiniteCausalDomain.causeableBool x.source x.target ||
    GRBS.E16aFiniteCausalDomain.modeledFixedBool x.source x.target

/--
The repaired pointwise causal checker has the same parameterized
correspondence contract.
-/
def causalFixedTransitionBridge :
    ExecutablePredicateBridge
      CausalTransitionInput
      causalCoverageFixedPredicate :=
  { check := causalCoverageFixedCheck
    correspondence := by
      intro x
      rcases x with ⟨source, target⟩
      cases source <;> cases target <;>
        constructor <;> intro h <;>
        simp [causalCoverageFixedCheck, causalCoverageFixedPredicate,
          GRBS.E16aFiniteCausalDomain.causeableP,
          GRBS.E16aFiniteCausalDomain.modeledFixedP,
          GRBS.E16aFiniteCausalDomain.causeableBool,
          GRBS.E16aFiniteCausalDomain.modeledFixedBool] at h ⊢ }

/--
The repaired s0 → s2 transition is accepted at both levels.
-/
def repairedCausalTransition : CausalTransitionInput :=
  { source := GRBS.E16aFiniteCausalDomain.St.s0
    target := GRBS.E16aFiniteCausalDomain.St.s2 }

theorem repaired_causal_transition_holds :
    causalFixedTransitionBridge.check repairedCausalTransition = true
    ∧ causalCoverageFixedPredicate repairedCausalTransition := by
  constructor
  · native_decide
  · intro hcause
    rfl

/--
E22 establishes the reusable pointwise abstraction while preserving
the distinct universal shape of finite causal coverage.
-/
theorem e22_parameterized_bridge :
    temporalPredicateBridge.check staleFreshnessInput = false
    ∧ Not (freshPredicate staleFreshnessInput)
    ∧ temporalPredicateBridge.check stableFreshnessInput = true
    ∧ freshPredicate stableFreshnessInput
    ∧ causalTransitionBridge.check originalCausalTransition = false
    ∧ Not (causalCoveragePredicate originalCausalTransition)
    ∧ causalFixedTransitionBridge.check repairedCausalTransition = true
    ∧ causalCoverageFixedPredicate repairedCausalTransition := by
  exact ⟨
    stale_parameterized_bridge_fails.1,
    stale_parameterized_bridge_fails.2,
    stable_parameterized_bridge_holds.1,
    stable_parameterized_bridge_holds.2,
    original_causal_transition_fails.1,
    original_causal_transition_fails.2,
    repaired_causal_transition_holds.1,
    repaired_causal_transition_holds.2
  ⟩

end GRBS.E22ParameterizedExecutablePredicateBridge
