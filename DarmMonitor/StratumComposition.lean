import DarmMonitor.Basic
import DarmMonitor.BoundaryMargin

/-
  StratumComposition — coherence between the discrete policy engine
  (DarmMonitor/Basic.lean) and the continuous boundary-margin layer
  (DarmMonitor/BoundaryMargin.lean).

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`. Do not describe as verified before both.

  DESIGN NOTE — why this is not an algebraic simulation.
  An earlier candidate bridge mapped discrete states to weight vectors via
  `interp`, demanding `interp (worldStep s a) = reweight … (interp s)`.
  That is degenerate: `worldStep _ .actA = .stateA` is constant in `s`, while
  `reweight η loss` multiplies coordinatewise by `exp (-η * loss i) > 0` and is
  therefore injective. An injective map composed with `interp` is constant only
  if `interp` is constant. So state-independent signal synthesis admits no
  non-degenerate algebraic bridge. (Registered as Negative Result 2. The
  obstruction is specific to state-INDEPENDENT `sig`; allowing `sig` to depend
  on the source state dissolves it.)

  The bridge here is set-theoretic instead: both strata already speak about
  `Finset (Fin n)`. Discrete `policy` and continuous `active δ w` are the same
  type once `ActionId := Fin n`. No real arithmetic enters `Basic.lean`; the
  monitor stays computable and the continuous layer keeps the analysis.

  ARCHITECTURAL CONSTRAINT (deliberate): `policy` is NOT derived from `w`.
  Deriving it would force the reference monitor to evaluate `Real.exp` to
  answer "is this action permitted", making `Basic.step` noncomputable.
  The two fields stay independent and are related by a coherence predicate.
-/

namespace DARM.Composition

open DARM.Boundary

variable {n : ℕ} {CapId Token : Type}
  [DecidableEq CapId] [DecidableEq Token]

/-- **Coherence.** Every action the discrete monitor currently permits is
    backed by a weight coordinate at or above the margin floor `δ`.

    Inclusion, not equality: the continuous layer may hold active coordinates
    the policy does not yet permit (capacity in reserve). The forbidden
    direction is a permitted action with no support behind it. -/
def IsCoherent (s : State CapId (Fin n)) (δ : ℝ) (w : Fin n → ℝ) : Prop :=
  s.policy ⊆ active δ w

/-- **Composition theorem.** Coherence is preserved by any agent event paired
    with a Z-safe continuous update.

    The chain is three inclusions:
      policy(t+1) ⊆ policy(t)      -- step_agent_policy_monotone
                  ⊆ active(t)      -- hypothesis
                  ⊆ active(t+1)    -- transportSupp

    Note the strata move in OPPOSITE directions and this is what makes the
    statement hold: the agent can only shrink policy, a safe update can only
    preserve or grow the active set. There is no sandwich — no upper bound on
    active(t+1) is recovered. The claim is one-directional: the continuous
    layer drops nothing the discrete layer permitted. -/
theorem coherence_preserved_under_agent_event
    (requires : Fin n → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop) [DecidablePred validToken]
    (s : State CapId (Fin n)) (e : Event CapId (Fin n) Token)
    (δ η : ℝ) (loss w : Fin n → ℝ)
    (hAgent : actor e = Actor.agent)
    (hZ : 0 < Z (reweight η loss w))
    (hsafe : is_safe_signal_Z δ η loss w)
    (hcoh : IsCoherent s δ w) :
    IsCoherent (step requires allowedCapLimit validToken s e) δ
      (normalize (reweight η loss w) (Z (reweight η loss w))) := by
  unfold IsCoherent at hcoh ⊢
  have h_shrink : (step requires allowedCapLimit validToken s e).policy ⊆ s.policy :=
    step_agent_policy_monotone requires allowedCapLimit validToken s e hAgent
  have h_transport : active δ w
      ⊆ active δ (normalize (reweight η loss w) (Z (reweight η loss w))) :=
    transportSupp δ η loss w hZ hsafe
  exact (h_shrink.trans hcoh).trans h_transport

/-- External suspension also preserves coherence, trivially: policy becomes ∅.
    Stated separately because `externalSuspend` is not an agent event and so
    is not covered by the theorem above. -/
theorem coherence_preserved_under_suspend
    (requires : Fin n → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop) [DecidablePred validToken]
    (s : State CapId (Fin n))
    (δ η : ℝ) (loss w : Fin n → ℝ)
    (hZ : 0 < Z (reweight η loss w))
    (hsafe : is_safe_signal_Z δ η loss w) :
    IsCoherent (step requires allowedCapLimit validToken s Event.externalSuspend) δ
      (normalize (reweight η loss w) (Z (reweight η loss w))) := by
  unfold IsCoherent
  simp only [step]
  exact Finset.empty_subset _

/-! ## Registered limitation

  Coherence is preserved by every agent event and by external suspension.
  It is NOT preserved by `authenticatedRatification`, which assigns
  `policy := newPolicy` outright with no constraint relating `newPolicy` to
  the weight vector. A ratifier can therefore grant authority the continuous
  layer does not support.

  This is a precise localization, not a gap in the proof: the single operation
  that can break coherence is the one whose holder assumption A4 states the
  agent can causally influence without bound (see DarmMonitor/Influence.lean,
  `not_noninterfering_all`).

  OPEN: whether a constrained ratification rule — one requiring
  `newPolicy ⊆ active δ w` at ratification time — is (a) provable to preserve
  coherence, and (b) acceptable, since it makes the human's authority
  contingent on a machine-computed bound.
-/

end DARM.Composition

#print axioms DARM.Composition.coherence_preserved_under_agent_event
#print axioms DARM.Composition.coherence_preserved_under_suspend
