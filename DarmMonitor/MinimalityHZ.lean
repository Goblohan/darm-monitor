import DarmMonitor.StratumComposition

/-!
  MinimalityHZ — `hZ` is necessary for coherence preservation.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  When `Z (reweight η loss w) = 0`, the normalizer is zero, `normalize _ 0`
  is the ZERO VECTOR (`x / 0 = 0`), and the active set of the zero vector at
  a positive margin is EMPTY (`active δ 0 = { i : δ ≤ 0 } = ∅` for `δ > 0`).
  So coherence's conclusion collapses to `newPolicy ⊆ ∅`; any agent event
  leaving a NONEMPTY policy refutes it.

  WITNESS: n = 2, w = (1,-1), η = 0, δ = 1, loss = 0, policy = {0},
  event = autonomousPropose {0}. Z = 0 (hZ false), hsafe/hcoh/hAgent hold,
  post-event policy {0} not ⊆ active 1 0 = ∅.

  `hZ` here forbids the active set collapsing to ∅ via a zero normalizer —
  erasing the space covering the policy rather than preserving it. Distinct
  from the `safe_signal_equiv` role.
-/

namespace DARM
namespace MinimalityHZ

open DARM.Composition

/-! ## The countermodel -/

def w2 : Fin 2 → ℝ := ![1, -1]

/-- `Z` of the reweighted (η = 0, so unchanged) witness is zero. -/
theorem Z_witness_zero :
    Boundary.Z (Boundary.reweight 0 (![0, 0] : Fin 2 → ℝ) w2) = 0 := by
  simp [Boundary.Z, Boundary.reweight, w2, Fin.sum_univ_two]

/-- Before the update, coordinate 0 is the only active one. -/
theorem active_before : Boundary.active (1 : ℝ) w2 = {0} := by
  ext i
  simp only [Boundary.active, Finset.mem_filter, Finset.mem_univ, true_and, w2]
  fin_cases i
  · simp
  · norm_num

/-- After the update, the active set is empty. -/
theorem active_after :
    Boundary.active (1 : ℝ)
      (Boundary.normalize (Boundary.reweight 0 (![0, 0] : Fin 2 → ℝ) w2)
        (Boundary.Z (Boundary.reweight 0 (![0, 0] : Fin 2 → ℝ) w2))) = ∅ := by
  rw [Z_witness_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  simp only [Boundary.active, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  unfold Boundary.normalize at hi
  simp only [div_zero] at hi
  linarith

/-! ## `hZ` is necessary -/

/-- **`hZ` necessary for coherence preservation.** -/
theorem hZ_necessary_for_coherence :
    ∃ (s : State Unit (Fin 2)) (δ η : ℝ) (loss w : Fin 2 → ℝ)
      (e : Event Unit (Fin 2) Bool),
      actor e = Actor.agent ∧
      Boundary.is_safe_signal_Z δ η loss w ∧
      IsCoherent s δ w ∧
      ¬ (0 < Boundary.Z (Boundary.reweight η loss w)) ∧
      ¬ IsCoherent (step (fun _ : Fin 2 => ()) (∅ : Finset Unit)
            (fun b : Bool => b = true) s e) δ
          (Boundary.normalize (Boundary.reweight η loss w)
            (Boundary.Z (Boundary.reweight η loss w))) := by
  refine ⟨{ cap := ∅, policy := {0}, opState := OpState.active, lastExecuted := none },
          1, 0, ![0, 0], w2, Event.autonomousPropose {0}, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro i hi
    rw [active_before] at hi
    simp only [Finset.mem_singleton] at hi
    subst hi
    rw [Z_witness_zero]
    simp [Boundary.reweight, w2]
  · show ({0} : Finset (Fin 2)) ⊆ Boundary.active 1 w2
    rw [active_before]
  · rw [Z_witness_zero]
    norm_num
  · unfold IsCoherent
    simp only [step, Finset.Subset.refl, if_true]
    rw [active_after]
    intro hsub
    exact absurd (hsub (Finset.mem_singleton_self 0)) (Finset.notMem_empty 0)

#print axioms Z_witness_zero
#print axioms active_before
#print axioms active_after
#print axioms hZ_necessary_for_coherence

end MinimalityHZ
end DARM
