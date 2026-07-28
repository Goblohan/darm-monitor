import DarmMonitor.Reachability
import DarmMonitor.Influence

/-
  Assumptions — A1–A4 as Lean objects rather than docstring prose.

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`.

  WHY THIS MODULE EXISTS. The Dependency Atlas proposes a Minimal Assumption
  Basis Matrix: for each theorem, which of A1–A4 are necessary, sufficient, or
  independent. That matrix is not checkable while the assumptions live in
  comments. No theorem in the kernel currently takes A1–A4 as hypotheses, so
  no cell of the matrix can be proved or refuted. This module starts turning
  them into predicates that theorems can actually depend on.

  AN ASSUMPTION IS ONLY USEFUL IF IT IS BOTH SATISFIABLE AND REFUTABLE.
  If it holds in every model, no "necessary" cell can ever be proved, since a
  drop-countermodel cannot exist. If it holds in none, every theorem
  conditioned on it is vacuous. Each assumption below is therefore accompanied
  by both a witness and a countermodel.

  STATUS OF THE FOUR:

    A2  FORMALIZED HERE, with necessity proved.
        Not the boundedness condition the Atlas proposes — that hypothesis
        appears nowhere in the kernel. The condition that is actually
        load-bearing, and already present ad hoc in six modules as `hZ`/`hw`,
        is non-negativity with positive total mass.

    A4  FORMALIZED HERE, as a condition rather than a property.
        The Atlas states A4 as "causal isolation holds", but Influence.lean
        proves `not_noninterfering_all`: it does NOT hold in that model.
        Conditioning theorems on a refuted hypothesis makes them vacuous. The
        usable form is the deployment-relative `NoninterferingFrom`, which
        Influence.lean's own docstring identifies as the weaker and more
        useful property. Dropped: the Atlas's probabilistic phrasing
        P(S' | Obs, Latent) = P(S' | Obs). Nothing in this development is
        probabilistic; the noninterference here is deterministic constancy.

    A1  PROVISIONAL — see section 3. `DecidableEq CapId` is vacuous, since
        `Classical.dec` supplies it for every type, so no drop-countermodel
        can exist and no A1 necessity cell is provable as stated.

    A3  NOT AN ASSUMPTION. `step : State → Event → State` being a function
        already encodes determinism and serialization. There is nothing to
        assume and nothing to drop. It is a modelling commitment and belongs
        in the README, not in a minimality matrix. Promote it only if
        interleaved execution is ever modelled.
-/

namespace DARM
namespace Assumptions

open DARM.Boundary

/-! ## 1. A2 — Well-formed weight vectors

  The measure-theoretic precondition for the continuous stratum: mass is
  non-negative and the total is strictly positive. -/

/-- **A2.** Weights are non-negative and carry positive total mass. -/
structure WellFormedWeights {n : ℕ} (w : Fin n → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ w i
  massPos : 0 < Z w

/-- A2 is satisfiable. -/
theorem A2_satisfiable : ∃ w : Fin 1 → ℝ, WellFormedWeights w := by
  refine ⟨fun _ => 1, ⟨fun i => by norm_num, ?_⟩⟩
  simp [Z]

/-- The capacity bound of `Reachability`, restated as a consequence of A2.
    This is the re-parameterization pattern: the assumption is now an object
    the theorem depends on, not a remark. -/
theorem capacity_bound_of_A2
    {n : ℕ} (δ : ℝ) (v : Fin n → ℝ) (h : WellFormedWeights v) :
    ((active δ (DARM.Boundary.normalize v (Z v))).card : ℝ) * δ ≤ 1 :=
  DARM.Reachability.active_card_mul_delta_le_one δ v h.nonneg h.massPos

/-- **A2 necessity — the non-negativity half is load-bearing.**

    Dropping `nonneg` while keeping `massPos` breaks the capacity bound.
    Witness: `v = (10, 10, 10, -29)` has total mass exactly 1, so the negative
    coordinate cancels the surplus and three coordinates sit far above the
    margin floor `δ = 1/2`. The bound would require `3 * (1/2) ≤ 1`.

    This is what makes A2 a real assumption rather than bookkeeping: there is
    a model where it fails and the theorem fails with it. -/
theorem A2_nonneg_necessary :
    ∃ (δ : ℝ) (v : Fin 4 → ℝ),
      0 < Z v ∧
      1 < ((active δ (DARM.Boundary.normalize v (Z v))).card : ℝ) * δ := by
  have hZ : Z (![10, 10, 10, -29] : Fin 4 → ℝ) = 1 := by
    simp [Z, Fin.sum_univ_four]
    norm_num
  refine ⟨1/2, ![10, 10, 10, -29], ?_, ?_⟩
  · rw [hZ]; norm_num
  · rw [hZ]
    have hsub : ({0, 1, 2} : Finset (Fin 4))
        ⊆ active (1/2 : ℝ) (DARM.Boundary.normalize (![10, 10, 10, -29] : Fin 4 → ℝ) 1) := by
      intro i hi
      fin_cases hi <;>
        simp [active, DARM.Boundary.normalize] <;>
        norm_num
    have hcard : 3 ≤ (active (1/2 : ℝ)
        (DARM.Boundary.normalize (![10, 10, 10, -29] : Fin 4 → ℝ) 1)).card := by
      have h0 : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
      calc 3 = ({0, 1, 2} : Finset (Fin 4)).card := h0.symm
        _ ≤ _ := Finset.card_le_card hsub
    have h3 : (3 : ℝ) ≤ ((active (1/2 : ℝ)
        (DARM.Boundary.normalize (![10, 10, 10, -29] : Fin 4 → ℝ) 1)).card : ℝ) := by
      exact_mod_cast hcard
    linarith

/-! ## 2. A4 — Causal isolation of the ratification channel

  Stated as the deployment-relative noninterference condition from
  `Influence.lean`, not as the claim that isolation holds. -/

/-- **A4.** From initial state `s₀`, the ratifier's verdict does not vary
    across anything the agent can cause. This is `NoninterferingFrom`, which
    `noninterferingFrom_iff_constant_on_reachable_image` characterizes as
    constancy of `r ∘ obs` on the reachable image. -/
def CausallyIsolated (s₀ : DARM.A4.WorldState)
    (obs : DARM.A4.WorldState → DARM.A4.Observation)
    (r : DARM.A4.Observation → DARM.A4.Ratification) : Prop :=
  DARM.A4.NoninterferingFrom s₀ obs r

/-- A4 is satisfiable: a ratifier that ignores observations is trivially
    isolated. Degenerate, but it establishes the assumption is not empty. -/
theorem A4_satisfiable :
    ∃ (r : DARM.A4.Observation → DARM.A4.Ratification),
      CausallyIsolated .neutral DARM.A4.obs r := by
  refine ⟨fun _ => .reject, ?_⟩
  intro s _ a₁ a₂
  rfl

/-- A4 is a genuine restriction: it fails for the modelled channel. This is
    `not_noninterfering_from_neutral`, restated at the assumption level.

    Consequence for the matrix: any theorem listing A4 in its minimal basis is
    conditional on a hypothesis the reference model does not satisfy. That is
    legitimate — but it must be stated, not glossed. -/
theorem A4_fails_for_modelled_channel :
    ¬ CausallyIsolated .neutral DARM.A4.obs DARM.A4.ratify :=
  DARM.A4.not_noninterfering_from_neutral

/-! ## 3. A1 — provisional

  `DecidableEq CapId` cannot serve as an assumption in a minimality calculus:
  `Classical.dec` provides it for every type, so it holds in every model and
  no drop-countermodel exists.

  Two honest replacements, neither yet formalized:

    (a) TOKEN NON-TRIVIALITY: `∃ t, ¬ validToken t`. Non-vacuous and
        droppable. The drop-countermodel already exists in the kernel —
        `Ratification.ratification_breaks_coherence` uses `fun _ => True`,
        i.e. a token predicate satisfying nothing. Cheap, but thin as a
        formalization of "unforgeability".

    (b) CAPABILITY GATING: make `cap` causally live by having
        `allowedActions` intersect with capability-derived actions. This is
        the substantive version, and it would simultaneously fix a known
        defect: `cap` is currently written by `step` and read by nothing, so
        `step_preserves_capInvariant` constrains state that has no effect on
        behaviour. Requires editing `Basic.lean` and re-earning its seven
        axiom traces.

  Open decision. Until it is made, no A1 column of the matrix is meaningful.
-/

/-! ## Registered status

  DONE:    A2 formalized, satisfiable, and proved necessary for the capacity
           bound. A4 formalized as a condition, shown satisfiable and shown
           to fail for the modelled channel.

  NEXT:    Re-parameterize the existing kernel theorems on A2 where they
           currently carry `hZ`/`hw` inline — StratumComposition, all three
           Ratification results, both expansion witnesses. Mechanical, and it
           makes the A2 column of the matrix real.

  OPEN:    A1 (decision above). Every "necessary" cell other than
           A2/capacity. Necessity requires one drop-countermodel per cell;
           none of the others exist yet, and the matrix should not assert
           them until they do.
-/

end Assumptions
end DARM

#print axioms DARM.Assumptions.A2_satisfiable
#print axioms DARM.Assumptions.capacity_bound_of_A2
#print axioms DARM.Assumptions.A2_nonneg_necessary
#print axioms DARM.Assumptions.A4_satisfiable
#print axioms DARM.Assumptions.A4_fails_for_modelled_channel
