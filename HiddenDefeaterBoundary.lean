import HiddenDefeater

namespace GRBS.HiddenDefeaterBoundary

open GRBS.HiddenDefeater

/-
  Boundary-level version of the hidden defeater experiment.

  Source boundary:
    format-test environment

  Target boundary:
    safety-critical deployment

  The visible claim remains true:
    System A passed the test.

  But the source warrant does not transfer to the target reliance claim.
-/

inductive Boundary where
  | formatTest
  | safetyDeployment
deriving DecidableEq, Repr

/-- A claim locally holds when the visible passed-test atom is present. -/
def localClaimHolds (I : Info) : Prop :=
  contains I Atom.passedSafetyTest

/--
  A warrant exists in the source boundary if the system passed the test.
  This is intentionally weak: it only warrants the local claim.
-/
def sourceWarrant (B : Boundary) (I : Info) : Prop :=
  B = Boundary.formatTest ∧ localClaimHolds I

/--
  A target deployment warrant requires the passed-test atom
  and also requires that the hidden format-only defeater is absent.
-/
def targetWarrant (B : Boundary) (I : Info) : Prop :=
  B = Boundary.safetyDeployment ∧ relies I

/--
  Transfer is admissible only when the fuller information state still supports
  target reliance.
-/
def admissibleTransfer (Ip Ir : Info) : Prop :=
  relies Ip ∧ relies Ir

/--
  Confidence transfer means the visible state induces reliance.
-/
def confidenceTransfers (Ip : Info) : Prop :=
  relies Ip

/--
  Deceptive transfer:
  confidence transfers from the visible state, but admissible warrant transfer fails
  under the fuller state.
-/
def deceptiveTransfer (Ip Ir : Info) : Prop :=
  confidenceTransfers Ip ∧ ¬ admissibleTransfer Ip Ir

theorem visible_has_source_warrant :
    sourceWarrant Boundary.formatTest visible := by
  constructor
  · rfl
  · exact visible_contains_passed_test

theorem full_has_no_target_warrant :
    ¬ targetWarrant Boundary.safetyDeployment full := by
  intro h
  exact does_not_rely_on_full h.2

theorem confidence_transfers_from_visible :
    confidenceTransfers visible := by
  exact relies_on_visible

theorem transfer_not_admissible_visible_to_full :
    ¬ admissibleTransfer visible full := by
  intro h
  exact does_not_rely_on_full h.2

theorem deceptive_transfer_exists :
    deceptiveTransfer visible full := by
  constructor
  · exact confidence_transfers_from_visible
  · exact transfer_not_admissible_visible_to_full

/-
  DARM-shaped compression:

  There exists a case where a local source warrant exists,
  target warrant fails under fuller information,
  yet confidence transfers from the visible slice.
-/
theorem source_warrant_without_target_warrant_with_confidence :
    sourceWarrant Boundary.formatTest visible ∧
    ¬ targetWarrant Boundary.safetyDeployment full ∧
    confidenceTransfers visible := by
  constructor
  · exact visible_has_source_warrant
  · constructor
    · exact full_has_no_target_warrant
    · exact confidence_transfers_from_visible

end GRBS.HiddenDefeaterBoundary
