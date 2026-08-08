import DarmMonitor.Entitlement

/-
  MinimalityA2 — `capInvariant` is necessary for Lemma 7.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT THIS ADDS. `Assumptions.lean`'s registered status asks for the A2 column
  of the minimality matrix to be made real. `Basic.execution_confined_by_cap_bound`
  (Lemma 7) says every executable action consumes a capability inside the
  external bound, GIVEN `capInvariant`. This exhibits a state where that
  hypothesis fails and the conclusion fails with it.

  THE COUNTERMODEL. `capInvariant allowedCapLimit s` is `s.cap ⊆ allowedCapLimit`.
  Take a state holding a capability the bound does not permit, an action
  requiring exactly that capability, and the policy containing it:

      allowedCapLimit = {false}       -- the bound permits only `false`
      s.cap           = {true}        -- but the state holds `true`
      requires _      = true          -- the action needs `true`
      s.opState       = .active       -- so allowedActions filters by cap

  Then `canExecute` holds — the action is in the policy and its capability is
  held — while `requires a = true ∉ {false}`. The conclusion of Lemma 7 is
  false, and the only hypothesis missing is `capInvariant`.

  WHY THIS MATTERS AND IS NOT TRIVIAL. Before capability gating, `cap` was
  write-only: `capInvariant` constrained a field nothing read, so it could not
  have been necessary for any behavioural statement. Lemma 7 is the theorem
  that became statable once gating made `cap` causally live, and this cell
  confirms the hypothesis it rests on is load-bearing rather than inherited
  decoration.
-/

namespace DARM
namespace MinimalityA2

/-! ## The countermodel -/

/-- The offending state: holds capability `true`, which the bound below
    excludes. -/
def badState : State Bool Bool :=
  { cap := {true}
    policy := {true}
    opState := .active
    lastExecuted := none }

/-- The external bound permits only `false`. -/
def tightBound : Finset Bool := {false}

/-- Every action requires capability `true`. -/
def needsTrue : Bool → Bool := fun _ => true

/-- **`capInvariant` is necessary for Lemma 7.**

    All of Lemma 7's other ingredients hold — the action is executable — and its
    conclusion fails. So the theorem cannot be proved without `capInvariant`,
    which is what an N-cell asserts.

    Stated as a conjunction so the witness is self-contained: executable, bound
    violated, conclusion false. -/
theorem capInvariant_necessary_for_confinement :
    canExecute needsTrue badState true
      ∧ ¬ capInvariant tightBound badState
      ∧ needsTrue true ∉ tightBound := by
  refine ⟨?_, ?_, ?_⟩
  · -- executable: in the policy, and its capability is held
    unfold canExecute allowedActions badState needsTrue
    simp
  · -- the bound is violated: `true ∈ cap` but `true ∉ tightBound`
    unfold capInvariant badState tightBound
    simp
  · -- and the conclusion of Lemma 7 is false here
    unfold needsTrue tightBound
    simp

/-! ## Registered status

  DONE: the A2 cell. `capInvariant` is necessary for
  `execution_confined_by_cap_bound` — drop it and the conclusion fails at the
  witness above.

  WHAT THIS DOES NOT CLAIM. Only that the hypothesis is load-bearing for THIS
  theorem. A2 in the assumption registry is the external capability bound as a
  deployment property; this says the kernel's use of it is not decorative, not
  that any real deployment maintains it.

  Cells now proved: A5 non-negativity (N), safety for transport (N), agent
  hypothesis for coherence (N), mass-positivity (NOT-N), A1 independence (I),
  A1 not necessary for coherence (NOT-N), A1 necessary for entitlement (N via
  `entitlement_vacuous_without_A1`), and this one. Nine, against a matrix that
  wants considerably more.
-/

end MinimalityA2
end DARM

#print axioms DARM.MinimalityA2.capInvariant_necessary_for_confinement
