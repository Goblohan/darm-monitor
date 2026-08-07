import DarmMonitor.Reachability
import DarmMonitor.Influence

/-
  Assumptions — A1–A4 as Lean objects rather than docstring prose.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

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

  NUMBERING — CORRECTED. An earlier version of this module labelled the
  weight condition "A2". That collided: `Basic.lean` has registered A1–A4
  since the first commit, and its A2 is the EXTERNAL CAPABILITY BOUND, not a
  condition on weights. `Basic.lean`'s registry is canonical here; the
  Dependency Atlas renumbers A1 and A2 and is the document that must be
  amended. The weight condition is therefore A5 — a fifth assumption that
  appeared in no registry, though six modules already carry it inline as
  `hZ`/`hw`.

    A1  FORMALIZED HERE (section 3). Token unforgeability, per `Basic.lean`.
        Not the Atlas's `DecidableEq CapId`, which is vacuous: `Classical.dec`
        supplies it for every type, so no drop-countermodel can exist.

    A2  NOT IN THIS MODULE. The external capability bound is now behaviourally
        real via the gating in `Basic.lean`; its content is Lemma 7,
        `execution_confined_by_cap_bound`.

    A5  FORMALIZED HERE (section 1), with necessity proved. Non-negativity
        with positive total mass — the precondition the continuous stratum
        actually runs on.

    A4  FORMALIZED HERE, as a condition rather than a property.
        The Atlas states A4 as "causal isolation holds", but Influence.lean
        proves `not_noninterfering_all`: it does NOT hold in that model.
        Conditioning theorems on a refuted hypothesis makes them vacuous. The
        usable form is the deployment-relative `NoninterferingFrom`, which
        Influence.lean's own docstring identifies as the weaker and more
        useful property. Dropped: the Atlas's probabilistic phrasing
        P(S' | Obs, Latent) = P(S' | Obs). Nothing in this development is
        probabilistic; the noninterference here is deterministic constancy.

    A3  NOT AN ASSUMPTION. `step : State → Event → State` being a function
        already encodes determinism and serialization. There is nothing to
        assume and nothing to drop. It is a modelling commitment and belongs
        in the README, not in a minimality matrix. Promote it only if
        interleaved execution is ever modelled.
-/

namespace DARM
namespace Assumptions

open DARM.Boundary

/-! ## 1. A5 — Well-formed weight vectors

  The measure-theoretic precondition for the continuous stratum: mass is
  non-negative and the total is strictly positive. -/

/-- **A5.** Weights are non-negative and carry positive total mass. -/
structure WellFormedWeights {n : ℕ} (w : Fin n → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ w i
  massPos : 0 < Z w

/-- A5 is satisfiable. -/
theorem A5_satisfiable : ∃ w : Fin 1 → ℝ, WellFormedWeights w := by
  refine ⟨fun _ => 1, ⟨fun i => by norm_num, ?_⟩⟩
  simp [Z]

/-- The capacity bound of `Reachability`, restated as a consequence of A5.
    This is the re-parameterization pattern: the assumption is now an object
    the theorem depends on, not a remark. -/
theorem capacity_bound_of_A5
    {n : ℕ} (δ : ℝ) (v : Fin n → ℝ) (h : WellFormedWeights v) :
    ((active δ (DARM.Boundary.normalize v (Z v))).card : ℝ) * δ ≤ 1 :=
  DARM.Reachability.active_card_mul_delta_le_one δ v h.nonneg h.massPos

/-- **A5 necessity — the non-negativity half is load-bearing.**

    Dropping `nonneg` while keeping `massPos` breaks the capacity bound.
    Witness: `v = (10, 10, 10, -29)` has total mass exactly 1, so the negative
    coordinate cancels the surplus and three coordinates sit far above the
    margin floor `δ = 1/2`. The bound would require `3 * (1/2) ≤ 1`.

    This is what makes A5 a real assumption rather than bookkeeping: there is
    a model where it fails and the theorem fails with it. -/
theorem A5_nonneg_necessary :
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

/-! ## 3. A1 — Token unforgeability

  `Basic.lean`'s A1: `validToken` is opaque, and nothing in the kernel shows
  the agent cannot produce a token satisfying it. Formalized as the existence
  of at least one invalid token — the minimal condition under which
  "authentication" distinguishes anything. -/

/-- **A1.** Not every token is accepted. -/
def TokenUnforgeable {Token : Type} (validToken : Token → Prop) : Prop :=
  ∃ t, ¬ validToken t

/-- A1 is satisfiable. -/
theorem A1_satisfiable : TokenUnforgeable (fun b : Bool => b = true) :=
  ⟨false, by simp⟩

/-- A1 fails for the trivial predicate `fun _ => True`, which is exactly the
    one `Ratification.ratification_breaks_coherence` uses. -/
theorem A1_fails_for_trivial_predicate :
    ¬ TokenUnforgeable (fun _ : Unit => True) := by
  rintro ⟨t, ht⟩
  exact ht trivial

/-- **A1 is INDEPENDENT of coherence preservation — an "I" cell, proved.**

    One might expect the ratification counterexample to be an artifact of the
    degenerate token predicate. It is not. Here tokens are unforgeable (A1
    holds, `false` is rejected) and the ratifier presents a genuinely valid
    token — and coherence still breaks.

    So the defect is in policy semantics, not authentication. No strengthening
    of A1 repairs it; only the guard of
    `Ratification.guarded_ratification_preserves_coherence` does. -/
theorem A1_insufficient_for_coherence :
    ∃ (s : State Unit (Fin 1)) (δ : ℝ) (w : Fin 1 → ℝ)
      (t : Bool) (p : Finset (Fin 1)),
      TokenUnforgeable (fun b : Bool => b = true) ∧
      (t = true) ∧
      DARM.Composition.IsCoherent s δ w ∧
      ¬ DARM.Composition.IsCoherent
          (step (fun _ : Fin 1 => ()) (∅ : Finset Unit)
            (fun b : Bool => b = true) s
            (Event.authenticatedRatification t p)) δ w := by
  refine ⟨{ cap := ∅, policy := ∅, opState := OpState.active, lastExecuted := none },
          1, (fun _ => 0), true, {0}, A1_satisfiable, rfl, ?_, ?_⟩
  · exact Finset.empty_subset _
  · intro h
    have hmem : (0 : Fin 1) ∈ active (1 : ℝ) (fun _ : Fin 1 => (0 : ℝ)) := by
      apply h
      simp [step]
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    linarith

/-! ## Registered status

  DONE:    A1 formalized, satisfiable, and proved INDEPENDENT of coherence
           preservation. A2 discharged in `Basic.lean` via capability gating
           (Lemma 7). A4 formalized as a condition, shown satisfiable and
           shown to fail for the modelled channel. A5 formalized, satisfiable,
           and proved necessary for the capacity bound.
           A3 is not an assumption; see the header.

  NEXT:    Re-parameterize the existing kernel theorems on A5 where they
           currently carry `hZ`/`hw` inline — StratumComposition, all three
           Ratification results, both expansion witnesses. Mechanical, and it
           makes the A2 column of the matrix real.

  OPEN:    OPEN:    Every "necessary" cell other than
           A2/capacity. Necessity requires one drop-countermodel per cell;
           none of the others exist yet, and the matrix should not assert
           them until they do.
-/

end Assumptions
end DARM

#print axioms DARM.Assumptions.A5_satisfiable
#print axioms DARM.Assumptions.capacity_bound_of_A5
#print axioms DARM.Assumptions.A5_nonneg_necessary
#print axioms DARM.Assumptions.A4_satisfiable
#print axioms DARM.Assumptions.A4_fails_for_modelled_channel
#print axioms DARM.Assumptions.A1_satisfiable
#print axioms DARM.Assumptions.A1_fails_for_trivial_predicate
#print axioms DARM.Assumptions.A1_insufficient_for_coherence
