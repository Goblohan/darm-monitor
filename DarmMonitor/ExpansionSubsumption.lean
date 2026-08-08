import DarmMonitor.MinimalityZ

/-
  ExpansionSubsumption — the η = 0 witness is implied by the η ≠ 0 one.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHAT THIS RECORDS. `StrictExpansion.strict_expansion_witness` and
  `NontrivialExpansion.nontrivial_reweight_strict_expansion` are proved
  independently, in separate modules, with separate witnesses. But their
  statements are not independent:

      strict_expansion_witness       ∃ δ η loss w,  0 < Z ∧ safe ∧ active ⊂ active'
      nontrivial_..._expansion       ∃ δ η loss w,  η ≠ 0 ∧ loss ≠ 0 ∧ reweight ≠ w
                                                    ∧ 0 < Z ∧ safe ∧ active ⊂ active'

  The second carries every conjunct of the first and three more. So it implies
  the first outright, and the proof is destructuring — no arithmetic.

  WHY THIS IS WORTH STATING RATHER THAN DELETING. The weaker theorem is not
  redundant as documentation: it establishes non-vacuity at `η = 0`, where the
  update is pure renormalization and the expansion cannot be attributed to the
  exponential at all. That is a different fact about the model from "some
  nontrivial reweighting expands", even though the STATEMENT is weaker.

  What was missing was the arrow between them. Two witnesses looked like two
  independent results; one implies the other, and now that is visible.
-/

namespace DARM
namespace ExpansionSubsumption

open DARM.Boundary

/-- **The nontrivial witness implies the η = 0 witness.**

    Destructuring only: drop the three extra conjuncts and what remains is
    exactly `strict_expansion_witness`'s statement. -/
theorem strict_expansion_of_nontrivial :
    (∃ (δ η : ℝ) (loss w : Fin 2 → ℝ),
      0 < Z (reweight η loss w) ∧
      is_safe_signal_Z δ η loss w ∧
      active δ w ⊂
        active δ (DARM.Boundary.normalize (reweight η loss w)
          (Z (reweight η loss w)))) := by
  obtain ⟨δ, η, loss, w, _hη, _hloss, _hrw, hZ, hsafe, hexp⟩ :=
    DARM.NontrivialExpansion.nontrivial_reweight_strict_expansion
  exact ⟨δ, η, loss, w, hZ, hsafe, hexp⟩

/-! ## Registered status

  DONE: the implication is stated. `strict_expansion_witness` follows from
  `nontrivial_reweight_strict_expansion` by dropping conjuncts.

  WHAT THIS DOES NOT RECOMMEND. Deleting `StrictExpansion.lean`. Its witness
  uses `η = 0`, where `reweight` is pure renormalization — so it shows the
  active set can strictly grow with NO exponential reweighting at all. The
  statement is weaker; the fact is different. Keeping both is right, and what
  was missing was only the arrow.

  A GENERAL POINT this suggests. Two theorems proved separately, each with its
  own witness, can stand in an implication nobody has written down. That is not
  visible from either module's registered status, because each describes only
  itself. Whether other pairs in this repository are similarly related has not
  been checked.
-/

end ExpansionSubsumption
end DARM

#print axioms DARM.ExpansionSubsumption.strict_expansion_of_nontrivial
