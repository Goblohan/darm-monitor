import R5AssuranceConservation
import R4bAuthoritySubstitution

namespace GRBS.R4bCorrespondence

open GRBS.R4bAuthoritySubstitution
open GRBS.R5AssuranceConservation

def R4bSourceDomain : Tr → Prop :=
  fun t => tracesUnder Auth.enforcing t

def R4bTargetDomain : Tr → Prop :=
  fun t => tracesUnder Auth.permissive t

def R4bProperty : Tr → Prop :=
  G

def R4bDeltaObligation : Prop :=
  DeltaObligation Tr R4bSourceDomain R4bTargetDomain R4bProperty

theorem r4b_delta_obligation_iff_authority_obligation :
    R4bDeltaObligation ↔
      AuthSubstitutionObligation
        G Auth.enforcing Auth.permissive tracesUnder := by
  constructor
  · intro h t ht2 hnot1
    exact h t ⟨ht2, hnot1⟩
  · intro h t hdelta
    exact h t hdelta.1 hdelta.2

theorem r4b_violation_is_delta :
    Delta
      Tr
      R4bSourceDomain
      R4bTargetDomain
      Tr.violation := by
  constructor
  · trivial
  · intro h
    exact Tr.noConfusion h

theorem r4b_delta_obligation_fails :
    ¬ R4bDeltaObligation := by
  intro h
  exact h Tr.violation
    ⟨trivial, fun h => Tr.noConfusion h⟩

theorem r4b_is_undischarged_r5_delta :
    Delta
      Tr
      R4bSourceDomain
      R4bTargetDomain
      Tr.violation
    ∧ ¬ R4bDeltaObligation := by
  exact ⟨r4b_violation_is_delta, r4b_delta_obligation_fails⟩

theorem r4b_original_failure :
    SafeUnderAuthority G Auth.enforcing tracesUnder
    ∧ Auth.enforcing ≠ Auth.permissive
    ∧ ¬ SafeUnderAuthority G Auth.permissive tracesUnder
    ∧ ¬ AuthSubstitutionObligation
        G Auth.enforcing Auth.permissive tracesUnder :=
  unsupported_authority_substitution

theorem r4b_matches_r5_pattern :
    Delta
      Tr
      R4bSourceDomain
      R4bTargetDomain
      Tr.violation
    ∧ ¬ R4bDeltaObligation
    ∧ SafeUnderAuthority G Auth.enforcing tracesUnder
    ∧ Auth.enforcing ≠ Auth.permissive
    ∧ ¬ SafeUnderAuthority G Auth.permissive tracesUnder
    ∧ ¬ AuthSubstitutionObligation
        G Auth.enforcing Auth.permissive tracesUnder := by
  exact ⟨
    r4b_violation_is_delta,
    r4b_delta_obligation_fails,
    safe_under_enforcing,
    authority_differs,
    not_safe_under_permissive,
    obligation_not_dischargeable
  ⟩

end GRBS.R4bCorrespondence
