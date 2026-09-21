import Mathlib

namespace GRBS.IC1RuntimeSemantics

/-!
IC-1A — Exact Runtime Semantics of DARM Guard v0.1.0

This module does NOT claim that the Python implementation is
formally verified.

It formalizes the observable authorization kernel extracted from
darm_guard/checker.py.

The Python checker receives:

  credential.tools
  policy.authorized_tools
  requested_tools
  now

and rejects on:

  1. expired credential
  2. unknown requested tool
  3. requested tool outside credential and policy authority

The purpose of this module is to establish the exact mathematical
semantics of that runtime decision before attempting any refinement
to the richer DARM transfer calculus.
-/

/-- Abstract input to the v0.1.0 runtime checker. -/
structure RuntimeInput where
  credential : Finset String
  policy : Finset String
  requested : Finset String
  expired : Bool
  deriving DecidableEq

/-- The Python `delta` computation:
    requested_tools - credential.tools
-/
def delta (x : RuntimeInput) : Finset String :=
  x.requested \ x.credential

/-- The Python `unknown_tools` computation:
    requested_tools - policy.authorized_tools - credential.tools

    Since the two subtractions are set difference, this is
    equivalent to requested - (policy ∪ credential).
-/
def unknownTools (x : RuntimeInput) : Finset String :=
  x.requested \ x.policy \ x.credential

/-- The tools producing an authority failure in the Python checker. -/
def authorityFailures (x : RuntimeInput) : Finset String :=
  x.delta \ x.policy

/-- Exact logical rendering of the three failure classes used by
    `check_transfer`.
-/
def checkerAdmissible (x : RuntimeInput) : Prop :=
  ¬ x.expired ∧
  x.unknownTools = ∅ ∧
  x.authorityFailures = ∅

/-- Simplified runtime authorization condition. -/
def runtimeAdmissible (x : RuntimeInput) : Prop :=
  ¬ x.expired ∧
  x.requested ⊆ x.credential ∪ x.policy

/-- The executable form of the runtime decision. -/
def runtimeCheck (x : RuntimeInput) : Bool :=
  decide (runtimeAdmissible x)

/-- Empty observation-failure set is equivalent to complete coverage
    of the requested tools by credential or policy authority.
-/
theorem unknownTools_empty_iff
    (x : RuntimeInput) :
    x.unknownTools = ∅ ↔
      x.requested ⊆ x.credential ∪ x.policy := by
  simp [unknownTools]
  aesop

/-- Empty authority-failure set is equivalent to every credential delta
    being policy-authorized.
-/
theorem authorityFailures_empty_iff
    (x : RuntimeInput) :
    x.authorityFailures = ∅ ↔
      x.delta ⊆ x.policy := by
  simp [authorityFailures]

/-- The three explicit Python failure tests collapse to the single
    authorization inclusion condition.
-/
theorem checkerAdmissible_iff_runtimeAdmissible
    (x : RuntimeInput) :
    checkerAdmissible x ↔ runtimeAdmissible x := by
  constructor
  · intro h
    rcases h with ⟨hFresh, hUnknown, hAuthority⟩
    constructor
    · exact hFresh
    · exact (unknownTools_empty_iff x).mp hUnknown
  · intro h
    rcases h with ⟨hFresh, hScope⟩
    constructor
    · exact hFresh
    · exact (unknownTools_empty_iff x).mpr hScope
    · apply (authorityFailures_empty_iff x).mpr
      intro t ht
      have htReq : t ∈ x.requested := by
        exact ht.1
      have htNotCred : t ∉ x.credential := by
        exact ht.2
      have htUnion : t ∈ x.credential ∪ x.policy :=
        hScope htReq
      rcases htUnion with htCred | htPolicy
      · exact False.elim (htNotCred htCred)
      · exact htPolicy

/-- Executable success is equivalent to the formal runtime predicate. -/
theorem runtimeCheck_true_iff
    (x : RuntimeInput) :
    runtimeCheck x = true ↔ runtimeAdmissible x := by
  simp [runtimeCheck]

/-- Executable success is therefore equivalent to the exact Python
    failure-based checker semantics.
-/
theorem runtimeCheck_true_iff_checkerAdmissible
    (x : RuntimeInput) :
    runtimeCheck x = true ↔ checkerAdmissible x := by
  rw [runtimeCheck_true_iff]
  exact (checkerAdmissible_iff_runtimeAdmissible x).symm

/-- Runtime rejection is equivalent to failure of the simplified
    authorization condition.
-/
theorem runtimeCheck_false_iff
    (x : RuntimeInput) :
    runtimeCheck x = false ↔ ¬ runtimeAdmissible x := by
  simp [runtimeCheck]

/-- Any accepted request is contained in the union of credential
    authority and policy authority.
-/
theorem accepted_request_subset_authority
    (x : RuntimeInput)
    (h : runtimeCheck x = true) :
    x.requested ⊆ x.credential ∪ x.policy := by
  exact (runtimeCheck_true_iff x).mp h |>.2

end GRBS.IC1RuntimeSemantics
