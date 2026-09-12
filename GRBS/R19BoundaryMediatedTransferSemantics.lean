/-
R19: Boundary-Mediated Transfer Semantics

PURPOSE

This module gives DARM assurance transfer an independently defined semantic
interpretation. The semantic layer is deliberately not defined in terms of
`DARMTransferAdmissible`.

The purpose is to distinguish:

  1. semantic preservation of a guarantee across a transition boundary,
  2. structural coverage of guarantee-relevant dependencies,
  3. semantic discharge of those dependencies.

DARM transfer admissibility can then be related to semantic transfer only
through explicit adequacy assumptions.

The result is intentionally conditional. GRBS is not treated as a semantic
safety theorem by itself.

SEMANTIC SHAPE

A boundary-mediated transfer consists of:

  * a source state satisfying the source guarantee;
  * a target transition relation;
  * an enforcement predicate identifying transitions mediated by the
    applicable enforcement locus;
  * preservation of the target property across every mediated transition.

This module does not claim that the semantic model captures physical reality.
Such a claim would require a separate refinement argument.

ARCHITECTURAL ROLE

The intended architecture is:

  semantic source assurance
          |
          v
  boundary-mediated transition semantics
          |
          v
  target semantic assurance

DARM's structural transfer conditions are related to this semantic layer only
through explicit adequacy hypotheses.
-/

namespace GRBS.R19BoundaryMediatedTransferSemantics

/-- A semantic system consists of states and a transition relation. -/
structure SemanticSystem where
  State : Type
  Step : State → State → Prop

/--
A guarantee property over semantic states.

The guarantee is intentionally represented independently of the DARM `Frame`.
-/
structure SemanticGuarantee (S : SemanticSystem) where
  property : S.State → Prop

/--
A semantic boundary identifies the transitions that are actually mediated
by the enforcement locus under consideration.
-/
structure SemanticBoundary (S : SemanticSystem) where
  mediated : S.State → S.State → Prop

/--
A semantic transfer relation requires every relevant source-to-target step
to be mediated by the boundary.
-/
def BoundaryMediatedStep
    (S : SemanticSystem)
    (B : SemanticBoundary S)
    (x y : S.State) : Prop :=
  S.Step x y ∧ B.mediated x y

/--
Semantic preservation of a guarantee across all boundary-mediated steps.

The source and target states may differ. What matters is preservation of
the target property along every mediated transition.
-/
def SemanticallyPreserves
    (S : SemanticSystem)
    (G : SemanticGuarantee S)
    (B : SemanticBoundary S) : Prop :=
  ∀ x y,
    BoundaryMediatedStep S B x y →
    G.property x →
    G.property y

/--
A semantic source assurance.
-/
def SemanticSourceAssured
    (S : SemanticSystem)
    (G : SemanticGuarantee S)
    (source : S.State → Prop) : Prop :=
  ∀ x, source x → G.property x

/--
A semantic target assurance.
-/
def SemanticTargetAssured
    (S : SemanticSystem)
    (G : SemanticGuarantee S)
    (target : S.State → Prop) : Prop :=
  ∀ x, target x → G.property x

/--
A source-to-target transition is semantically admissible when:

  * the target states arise from mediated transitions,
  * the source state satisfies the source condition,
  * the guarantee is preserved by those mediated transitions.

This definition is independent of DARM's structural transfer calculus.
-/
def SemanticallyMediatedTransfer
    (S : SemanticSystem)
    (G : SemanticGuarantee S)
    (B : SemanticBoundary S)
    (source target : S.State → Prop) : Prop :=
  (∀ x y,
      source x →
      BoundaryMediatedStep S B x y →
      target y) ∧
  SemanticallyPreserves S G B

/--
Semantic transfer produces target assurance when the source is assured and
the mediated transition relation is adequate for the target condition.
-/
theorem semantic_transfer_preserves_assurance
    (S : SemanticSystem)
    (G : SemanticGuarantee S)
    (B : SemanticBoundary S)
    (source target : S.State → Prop)
    (hSource : SemanticSourceAssured S G source)
    (hTransfer : SemanticallyMediatedTransfer S G B source target)
    (hOrigin :
      ∀ y, target y →
        ∃ x, source x ∧ BoundaryMediatedStep S B x y) :
    SemanticTargetAssured S G target := by
  intro y hy
  rcases hTransfer with ⟨_, hPreserve⟩
  rcases hOrigin y hy with ⟨x, hxSource, hxStep⟩
  exact hPreserve x y hxStep (hSource x hxSource)

/--
Adequacy of a structural dependency representation for a semantic system.

Every semantic transition relevant to the guarantee must be represented by
at least one assurance-relevant dependency.
-/
def DependencyRepresentation
    (D : Type)
    (source target : D → Prop)
    (transitionRelevant : D → Prop) : Prop :=
  ∀ d, transitionRelevant d → source d ∨ target d

/--
Adequacy of a boundary coverage relation.

Every dependency that is semantically relevant to the guarantee is covered
by the semantic boundary.
-/
def BoundaryCoverageAdequate
    (D : Type)
    (relevant : D → Prop)
    (covered : D → Prop) : Prop :=
  ∀ d, relevant d → covered d

/--
Semantic discharge adequacy.

Covered dependencies must actually establish the semantic preservation
property required by the guarantee.
-/
def SemanticDischargeAdequate
    (D : Type)
    (covered : D → Prop)
    (discharge : D → Prop) : Prop :=
  ∀ d, covered d → discharge d

/--
R19's central correspondence schema.

DARM's structural transfer conditions are not themselves semantic transfer.
They become sufficient for semantic transfer only when explicit adequacy
conditions connect:

  structural dependency representation
       ->
  boundary coverage
       ->
  semantic discharge
       ->
  mediated transition preservation.
-/
def DARMToSemanticAdequacy
    (D : Type)
    (relevant covered discharge : D → Prop)
    (semanticPreservation : Prop) : Prop :=
  BoundaryCoverageAdequate D relevant covered ∧
  SemanticDischargeAdequate D covered discharge ∧
  (∀ d, discharge d → semanticPreservation)

/--
A minimal negative result: boundary mediation cannot be inferred merely
from the existence of a semantic guarantee.

This keeps semantic truth separate from transfer admissibility.
-/
theorem semantic_guarantee_does_not_imply_mediation :
    ∃ (S : SemanticSystem)
      (G : SemanticGuarantee S)
      (B : SemanticBoundary S)
      (x y : S.State),
      G.property x ∧
      BoundaryMediatedStep S B x y ∧
      ¬ G.property y := by
  let S : SemanticSystem :=
    { State := Bool
      Step := fun x y => x = false ∧ y = true }

  let G : SemanticGuarantee S :=
    { property := fun x => x = false }

  let B : SemanticBoundary S :=
    { mediated := fun _ _ => True }

  refine ⟨S, G, B, false, true, ?_, ?_, ?_⟩
  · rfl
  · constructor
    · constructor <;> rfl
    · trivial
  · simp [G]

end GRBS.R19BoundaryMediatedTransferSemantics
