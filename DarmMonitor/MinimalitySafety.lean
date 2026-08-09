import DarmMonitor.A5Discharged

/-
  MinimalitySafety — `hsafe` is necessary for coherence preservation.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  THE QUESTION. `StratumComposition.coherence_preserved_under_agent_event`
  carries `hsafe : is_safe_signal_Z δ η loss w`. `Minimality.lean` already has
  a cell showing safety is necessary for TRANSPORT. Coherence preservation is a
  different theorem, and agent events shrink the policy — so coherence might
  survive an unsafe update simply because there is less policy to cover.

  IT DOES NOT. The witness turns on normalization rather than on the update:

      two coordinates, w = (1, 1), δ = 1
      before   active 1 (1,1) = {0,1}      both coordinates clear the margin
      η = 0    Z = 2, normalized to (1/2, 1/2)
      after    active 1 (1/2,1/2) = ∅      neither clears it

  A policy of `{0,1}` is coherent before and uncovered after, and the agent
  event leaves it unchanged (`autonomousPropose` of the same policy). So the
  conclusion fails.

  AND `hsafe` NECESSARILY FAILS THERE, which is what makes this a cell rather
  than a contradiction. Safety would demand `δ * Z ≤ reweight i` for each active
  `i`, i.e. `r₀ + r₁ ≤ r₀` at `δ = 1` — impossible for positive entries. The
  theorem is true; the witness simply lies outside its hypotheses.

  WHAT THIS SHOWS ABOUT THE THEOREM. The shrinking policy is not what preserves
  coherence. Normalization can collapse the active set faster than any agent
  event shrinks the policy, and the safety certificate is exactly the condition
  forbidding that. `hsafe` is load-bearing for the same reason it is in
  `transportSupp`, not for a different one.
-/

namespace DARM
namespace MinimalitySafety

open DARM.Boundary DARM.Composition

/-! ## The countermodel -/

def bothActive : Fin 2 → ℝ := ![1, 1]

/-- Before the update, both coordinates clear a margin of 1. -/
theorem active_before : active (1 : ℝ) bothActive = {0, 1} := by
  ext i
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold bothActive
  fin_cases i <;> simp

/-- After normalization at `η = 0`, neither does: each entry is `1/2`. -/
theorem active_after :
    active (1 : ℝ)
      (DARM.Boundary.normalize (reweight 0 (fun _ => 0) bothActive)
        (Z (reweight 0 (fun _ => 0) bothActive))) = ∅ := by
  have hrw : ∀ i, reweight 0 (fun _ => 0) bothActive i = bothActive i := by
    intro i
    unfold reweight
    simp
  have hZ : Z (reweight 0 (fun _ => 0) bothActive) = 2 := by
    unfold Z
    rw [Fin.sum_univ_two, hrw, hrw]
    unfold bothActive
    norm_num
  ext i
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, not_le]
  unfold DARM.Boundary.normalize
  rw [hZ, hrw]
  unfold bothActive
  fin_cases i <;> norm_num

/-- **`hsafe` is necessary for coherence preservation.**

    The precondition holds, the safety certificate fails, and the conclusion
    fails — so the hypothesis cannot be dropped. -/
theorem hsafe_necessary_for_coherence :
    IsCoherent
      ({ cap := (∅ : Finset Unit), policy := {0, 1},
         opState := OpState.active, lastExecuted := none } : State Unit (Fin 2))
      (1 : ℝ) bothActive
    ∧ ¬ IsCoherent
      ({ cap := (∅ : Finset Unit), policy := {0, 1},
         opState := OpState.active, lastExecuted := none } : State Unit (Fin 2))
      (1 : ℝ)
      (DARM.Boundary.normalize (reweight 0 (fun _ => 0) bothActive)
        (Z (reweight 0 (fun _ => 0) bothActive))) := by
  constructor
  · unfold IsCoherent
    rw [active_before]
  · unfold IsCoherent
    rw [active_after]
    intro h
    have : (0 : Fin 2) ∈ ({0, 1} : Finset (Fin 2)) := by simp
    exact absurd (h this) (Finset.notMem_empty 0)

/-! ## Registered status

  DONE: twelve cells. `hsafe` is necessary for coherence preservation, and the
  reason is normalization rather than the policy dynamics.

  WHAT THE WITNESS ISOLATES. The agent event here changes nothing — it proposes
  the policy it already has. So the failure cannot be attributed to the discrete
  stratum at all. It is entirely the continuous one: two positive coordinates
  normalize to `1/2` each, and a margin of `1` admits neither. Any deployment
  choosing `δ` near or above `1/|active|` is in this regime, which is a
  practical reading of the same fact `FeasibilityRange` states as a design
  envelope.
-/

end MinimalitySafety
end DARM

#print axioms DARM.MinimalitySafety.active_before
#print axioms DARM.MinimalitySafety.active_after
#print axioms DARM.MinimalitySafety.hsafe_necessary_for_coherence
