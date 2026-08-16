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


/-- The event-sensitive weight transition. Agent and external (suspend) events
    carry the Z-safe continuous update `w ↦ normalize (reweight η loss w) (Z …)`,
    exactly as `coherence_preserved_under_agent_event` and
    `coherence_preserved_under_suspend` require. A human ratification event
    leaves the weight unchanged, exactly as `guarded_ratification_preserves_coherence`
    requires. This makes the weight evolution part of the formal model rather than
    an implicit parameter. -/
noncomputable def nextWeight
    {CapId Token : Type} {n : ℕ}
    (η : ℝ) (loss w : Fin n → ℝ)
    (e : Event CapId (Fin n) Token) :
    Fin n → ℝ :=
  match actor e with
  | Actor.human => w
  | _ => Boundary.normalize (Boundary.reweight η loss w)
           (Boundary.Z (Boundary.reweight η loss w))


/-- The per-step monitor admissibility condition. The adversarial policy may
    propose ANY event; the reference monitor admits it only under the boundary
    condition that its event class requires to preserve coherence.

    - A ratification event must satisfy the ratification guard `p ⊆ active δ w`
      (this is exactly `GuardedRatification`, and the unguarded case genuinely
      breaks coherence — see `HistorySafety.unguarded_ratification_counterexample`).
    - Every other event (agent action, capability expansion, execution,
      suspension) carries the Z-safe continuous update, so it must satisfy the
      monitor's scalar certificate `is_safe_signal_Z` together with positivity
      of the partition function — exactly the hypotheses
      `coherence_preserved_under_agent_event` and
      `coherence_preserved_under_suspend` require.

    The policy is not restricted. The monitor is. That is the DARM boundary. -/
def admissibleEvent
    {CapId Token : Type} {n : ℕ}
    (δ η : ℝ) (loss w : Fin n → ℝ)
    (e : Event CapId (Fin n) Token) : Prop :=
  match e with
  | Event.authenticatedRatification _ p =>
      Ratification.GuardedRatification δ w p
  | _ =>
      0 < Boundary.Z (Boundary.reweight η loss w) ∧
        Boundary.is_safe_signal_Z δ η loss w


/-- **The monitored one-step coherence theorem.** Given a coherent state at
    weight `w` and an event admitted by the monitor, the stepped state is
    coherent at the transitioned weight `nextWeight η loss w e`. Every event
    class is discharged by its existing single-step coherence theorem:
    agent events and suspension by the Z-safe continuous-update theorems,
    ratification by the guarded-ratification theorem. This is the composition
    interface: it threads `w ↦ nextWeight … e` while preserving coherence, so a
    trajectory induction can carry the evolving weight as part of its state. -/
theorem monitored_step_preserves_coherence
    {CapId Token : Type} {n : ℕ}
    [DecidableEq CapId] [DecidableEq Token]
    (requires : Fin n → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop) [DecidablePred validToken]
    (s : State CapId (Fin n)) (e : Event CapId (Fin n) Token)
    (δ η : ℝ) (loss w : Fin n → ℝ)
    (hcoh : Composition.IsCoherent s δ w)
    (hadm : admissibleEvent δ η loss w e) :
    Composition.IsCoherent
      (step requires allowedCapLimit validToken s e) δ
      (nextWeight η loss w e) := by
  cases e with
  | autonomousPropose p =>
      simp only [nextWeight, actor, admissibleEvent] at hadm ⊢
      obtain ⟨hZ, hsafe⟩ := hadm
      exact Composition.coherence_preserved_under_agent_event
        requires allowedCapLimit validToken s _ δ η loss w rfl hZ hsafe hcoh
  | autonomousExpandCap c =>
      simp only [nextWeight, actor, admissibleEvent] at hadm ⊢
      obtain ⟨hZ, hsafe⟩ := hadm
      exact Composition.coherence_preserved_under_agent_event
        requires allowedCapLimit validToken s _ δ η loss w rfl hZ hsafe hcoh
  | authenticatedRatification t p =>
      simp only [nextWeight, actor] at ⊢
      simp only [admissibleEvent] at hadm
      exact Ratification.guarded_ratification_preserves_coherence
        requires allowedCapLimit validToken s t p δ w hcoh hadm
  | externalSuspend =>
      simp only [nextWeight, actor, admissibleEvent] at hadm ⊢
      obtain ⟨hZ, hsafe⟩ := hadm
      exact Composition.coherence_preserved_under_suspend
        requires allowedCapLimit validToken s δ η loss w hZ hsafe
  | execute a =>
      simp only [nextWeight, actor, admissibleEvent] at hadm ⊢
      obtain ⟨hZ, hsafe⟩ := hadm
      exact Composition.coherence_preserved_under_agent_event
        requires allowedCapLimit validToken s _ δ η loss w rfl hZ hsafe hcoh

#print axioms monitored_step_preserves_coherence

/-- One step of a weighted history trajectory: the history-dependent policy
    selects an event from the observed history, the reference monitor applies
    it, the weight transitions by `nextWeight`, and the observation history is
    extended. -/
noncomputable def weightedHistoryStep
    {CapId Token : Type} {n : ℕ}
    [DecidableEq CapId] [DecidableEq (Fin n)] [DecidableEq Token]
    (requires : Fin n → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop) [DecidablePred validToken]
    (η : ℝ) (loss : Fin n → ℝ)
    (policy : HistorySafety.HistoryPolicy CapId (Fin n) Token)
    (hs : WeightedHistoryState (CapId := CapId) n) :
    WeightedHistoryState (CapId := CapId) n :=
  let e := HistorySafety.generateEvent policy hs.historyState.history
  let s' := step requires allowedCapLimit validToken hs.historyState.state e
  { historyState :=
      { state := s'
        history := hs.historyState.history.concat
          (HistorySafety.observe s') }
    weight := nextWeight η loss hs.weight e }

/-- A finite weighted trajectory generated by iterating the history-dependent
    policy, threading both the governance state and the evolving weight. -/
noncomputable def generateWeightedTrajectory
    {CapId Token : Type} {n : ℕ}
    [DecidableEq CapId] [DecidableEq (Fin n)] [DecidableEq Token]
    (requires : Fin n → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop) [DecidablePred validToken]
    (η : ℝ) (loss : Fin n → ℝ)
    (policy : HistorySafety.HistoryPolicy CapId (Fin n) Token)
    : Nat → WeightedHistoryState (CapId := CapId) n →
      WeightedHistoryState (CapId := CapId) n
  | 0, hs => hs
  | k + 1, hs =>
      generateWeightedTrajectory requires allowedCapLimit validToken η loss policy k
        (weightedHistoryStep requires allowedCapLimit validToken η loss policy hs)


/-- **Coherence is preserved across a finite adaptive-adversarial trajectory,
    provided the monitor admits every step.** The history-dependent policy is
    entirely unrestricted — it may select any event from the whole observed
    history, adversarially. Coherence at the evolving weight is nonetheless
    preserved at every point of the generated trajectory, on the sole condition
    that each event the policy proposes is admitted by the reference monitor
    (`admissibleEvent`): the ratification guard where it ratifies, the Z-safe
    certificate where it updates the weight.

    This is the trajectory-level composition of `monitored_step_preserves_coherence`.
    The hypothesis `hstep` supplies, for the event selected at each reachable
    trajectory state, the monitor's admissibility condition at that state's
    current weight. The unrestricted-without-the-guard case is genuinely unsafe:
    see `HistorySafety.unguarded_ratification_counterexample`. The adversary is
    not restricted; the monitor is. -/
theorem generateWeightedTrajectory_preserves_coherence
    {CapId Token : Type} {n : ℕ}
    [DecidableEq CapId] [DecidableEq Token]
    (requires : Fin n → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop) [DecidablePred validToken]
    (η : ℝ) (loss : Fin n → ℝ)
    (δ : ℝ)
    (policy : HistorySafety.HistoryPolicy CapId (Fin n) Token)
    (k : ℕ)
    (hs : WeightedHistoryState (CapId := CapId) n)
    (hstep : ∀ (hj : WeightedHistoryState (CapId := CapId) n),
      admissibleEvent δ η loss hj.weight
        (HistorySafety.generateEvent policy hj.historyState.history))
    (hcoh : WeightedCoherent δ hs) :
    WeightedCoherent δ
      (generateWeightedTrajectory requires allowedCapLimit validToken η loss policy k hs) := by
  induction k generalizing hs with
  | zero => simpa [generateWeightedTrajectory] using hcoh
  | succ m ih =>
      rw [generateWeightedTrajectory]
      apply ih
      show WeightedCoherent δ
        (weightedHistoryStep requires allowedCapLimit validToken η loss policy hs)
      unfold WeightedCoherent weightedHistoryStep
      exact monitored_step_preserves_coherence
        requires allowedCapLimit validToken
        hs.historyState.state
        (HistorySafety.generateEvent policy hs.historyState.history)
        δ η loss hs.weight hcoh (hstep hs)

#print axioms generateWeightedTrajectory_preserves_coherence
end DARM
