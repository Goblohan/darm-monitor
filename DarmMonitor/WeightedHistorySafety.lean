import DarmMonitor.HistorySafety
import DarmMonitor.StratumComposition

/-!
# DARM Weighted History Safety

A weighted history state combines the existing history-dependent governance
state with the current continuous authority weight vector.

The action domain is specialized to `Fin n`, matching the continuous
coherence layer.
-/

namespace DARM

structure WeightedHistoryState
    {CapId : Type} (n : ℕ) where
  historyState : HistorySafety.HistoryState
    (CapId := CapId)
    (ActionId := Fin n)
  weight : Fin n → ℝ

def WeightedCoherent
    {CapId : Type} {n : ℕ}
    (δ : ℝ)
    (hs : WeightedHistoryState (CapId := CapId) n) : Prop :=
  Composition.IsCoherent hs.historyState.state δ hs.weight

theorem weighted_coherence_iff
    {CapId : Type} {n : ℕ}
    (δ : ℝ)
    (hs : WeightedHistoryState (CapId := CapId) n) :
    WeightedCoherent δ hs ↔
      Composition.IsCoherent hs.historyState.state δ hs.weight := by
  rfl

#print axioms weighted_coherence_iff
#print axioms WeightedCoherent

end DARM