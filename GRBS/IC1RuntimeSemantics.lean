import Mathlib

namespace GRBS.IC1RuntimeSemantics

/-!
IC-1A — Exact Runtime Semantics of DARM Guard v0.1.0

This module does NOT claim that the Python implementation is
formally verified. It formalizes the observable authorization
kernel extracted from darm_guard/checker.py, which rejects on:
  1. expired credential
  2. unknown requested tool
  3. requested tool outside credential and policy authority
-/

/-- Abstract input to the v0.1.0 runtime checker. -/
structure RuntimeInput where
  credential : Finset String
  policy : Finset String
  requested : Finset String
  expired : Bool
  deriving DecidableEq

/-- The Python delta computation: requested_tools - credential.tools -/
def delta (x : RuntimeInput) : Finset String :=
  x.requested \ x.credential

/-- The Python unknown_tools computation. -/
def unknownTools (x : RuntimeInput) : Finset String :=
  (x.requested \ x.policy) \ x.credential

/-- The tools producing an authority failure in the Python checker. -/
def authorityFailures (x : RuntimeInput) : Finset String :=
  delta x \ x.policy

/-- Exact rendering of the three failure classes in check_transfer. -/
def checkerAdmissible (x : RuntimeInput) : Prop :=
  ¬ x.expired ∧
  unknownTools x = ∅ ∧
  authorityFailures x = ∅

/-- Simplified runtime authorization condition. -/
def runtimeAdmissible (x : RuntimeInput) : Prop :=
  ¬ x.expired ∧
  x.requested ⊆ x.credential ∪ x.policy

instance (x : RuntimeInput) : Decidable (runtimeAdmissible x) := by
  unfold runtimeAdmissible
  infer_instance

/-- The executable form of the runtime decision. -/
def runtimeCheck (x : RuntimeInput) : Bool :=
  decide (runtimeAdmissible x)

/-- Empty observation-failure set iff full coverage by credential or policy. -/
theorem unknownTools_empty_iff
    (x : RuntimeInput) :
    unknownTools x = ∅ ↔
      x.requested ⊆ x.credential ∪ x.policy := by
  rw [Finset.union_comm]
  simp [unknownTools]

/-- Empty authority-failure set iff every delta tool is policy-authorized. -/
theorem authorityFailures_empty_iff
    (x : RuntimeInput) :
    authorityFailures x = ∅ ↔
      delta x ⊆ x.policy := by
  simp [authorityFailures]

/-- The three Python failure tests collapse to one inclusion condition. -/
theorem checkerAdmissible_iff_runtimeAdmissible
    (x : RuntimeInput) :
    checkerAdmissible x ↔ runtimeAdmissible x := by
  constructor
  · rintro ⟨hFresh, hUnknown, _hAuthority⟩
    exact ⟨hFresh, (unknownTools_empty_iff x).mp hUnknown⟩
  · rintro ⟨hFresh, hScope⟩
    refine ⟨hFresh, (unknownTools_empty_iff x).mpr hScope, ?_⟩
    apply (authorityFailures_empty_iff x).mpr
    intro t ht
    simp only [delta, Finset.mem_sdiff] at ht
    rcases Finset.mem_union.mp (hScope ht.1) with htCred | htPolicy
    · exact absurd htCred ht.2
    · exact htPolicy

/-- Executable success iff the formal runtime predicate. -/
theorem runtimeCheck_true_iff
    (x : RuntimeInput) :
    runtimeCheck x = true ↔ runtimeAdmissible x := by
  simp [runtimeCheck]

/-- Executable success iff the exact Python failure-based semantics. -/
theorem runtimeCheck_true_iff_checkerAdmissible
    (x : RuntimeInput) :
    runtimeCheck x = true ↔ checkerAdmissible x := by
  rw [runtimeCheck_true_iff]
  exact (checkerAdmissible_iff_runtimeAdmissible x).symm

/-- Runtime rejection iff the authorization condition fails. -/
theorem runtimeCheck_false_iff
    (x : RuntimeInput) :
    runtimeCheck x = false ↔ ¬ runtimeAdmissible x := by
  simp [runtimeCheck]

/-- Any accepted request lies within credential or policy authority. -/
theorem accepted_request_subset_authority
    (x : RuntimeInput)
    (h : runtimeCheck x = true) :
    x.requested ⊆ x.credential ∪ x.policy := by
  exact (runtimeCheck_true_iff x).mp h |>.2

end GRBS.IC1RuntimeSemantics
