import IC1AbstractionGap
import R21RepairAdequacy

namespace GRBS.R22RuntimeSemanticCorrespondence

open GRBS.R21RepairAdequacy

/--
A complete semantic invocation contains the tool identity and its argument.
-/
structure RuntimeInvocation where
  tool : Nat
  argument : Nat

/--
The actual authorization observation exposed by DARM Guard's integration
wrapper: only the tool identity reaches `guard.check`.
-/
def guardObservation (r : RuntimeInvocation) : Nat :=
  r.tool

/--
A deliberately simple semantic authorization condition.

The particular predicate is not the claim. Its purpose is to demonstrate
that argument-dependent authorization cannot be recovered from the
tool-only observation.
-/
def semanticAuthorized (r : RuntimeInvocation) : Prop :=
  r.argument = 0

/--
The guard observation identifies two invocations whenever they use the
same tool, even when their arguments differ.
-/
theorem same_tool_same_guard_observation
    (r₁ r₂ : RuntimeInvocation)
    (hTool : r₁.tool = r₂.tool) :
    guardObservation r₁ = guardObservation r₂ := by
  exact hTool

/--
There are semantically different invocations that collapse to the same
authorization observation.
-/
theorem runtime_semantic_observation_collapse :
    ∃ r₀ r₁ : RuntimeInvocation,
      r₀ ≠ r₁ ∧
      guardObservation r₀ = guardObservation r₁ ∧
      (semanticAuthorized r₀ ↔ ¬ semanticAuthorized r₁) := by
  let r₀ : RuntimeInvocation := ⟨1, 0⟩
  let r₁ : RuntimeInvocation := ⟨1, 1⟩

  refine ⟨r₀, r₁, ?_, ?_, ?_⟩

  · intro h
    have hArg : r₀.argument = r₁.argument := by
      simpa [r₀, r₁] using congrArg RuntimeInvocation.argument h
    simp [r₀, r₁] at hArg

  · rfl

  · simp [semanticAuthorized, r₀, r₁]

/--
No predicate over the actual guard observation can exactly recover this
argument-dependent semantic authorization predicate.
-/
theorem no_observation_only_authorizer :
    ¬ ∃ f : Nat → Prop,
      ∀ r : RuntimeInvocation,
        f (guardObservation r) ↔ semanticAuthorized r := by
  intro h
  rcases h with ⟨f, hf⟩

  let r₀ : RuntimeInvocation := ⟨1, 0⟩
  let r₁ : RuntimeInvocation := ⟨1, 1⟩

  have h₀ : f 1 ↔ semanticAuthorized r₀ := by
    simpa [r₀, guardObservation] using hf r₀

  have h₁ : f 1 ↔ semanticAuthorized r₁ := by
    simpa [r₁, guardObservation] using hf r₁

  have hSemantic : semanticAuthorized r₀ ↔ semanticAuthorized r₁ :=
    h₀.symm.trans h₁

  simp [semanticAuthorized, r₀, r₁] at hSemantic

end GRBS.R22RuntimeSemanticCorrespondence

namespace GRBS.R22RuntimeSemanticCorrespondence

/--
General information-loss theorem.

If two complete invocations have the same guard observation but a
semantic property distinguishes them, then no predicate over the guard
observation alone can exactly recover that semantic property.
-/
theorem observation_collision_blocks_exact_semantic_classification
    {R O : Type}
    (observe : R → O)
    (P : R → Prop)
    (r₀ r₁ : R)
    (hObs : observe r₀ = observe r₁)
    (hSep : P r₀ ↔ ¬ P r₁) :
    ¬ ∃ f : O → Prop,
      ∀ r : R, f (observe r) ↔ P r := by
  intro h
  rcases h with ⟨f, hf⟩

  have h0 : f (observe r₀) ↔ P r₀ := hf r₀
  have h1 : f (observe r₁) ↔ P r₁ := hf r₁

  have hSame : f (observe r₀) ↔ f (observe r₁) := by
    simp [hObs]

  have hSemantic : P r₀ ↔ P r₁ := by
    exact h0.symm.trans (hSame.trans h1)

  have hNotP1_iff : ¬ P r₁ ↔ ¬ P r₀ := by
    constructor
    · intro hNotP1 hP0
      exact hNotP1 (hSemantic.mp hP0)
    · intro hNotP0 hP1
      exact hNotP0 (hSemantic.mpr hP1)

  have hSelf : P r₀ ↔ ¬ P r₀ :=
    hSep.trans hNotP1_iff

  have hNotP0 : ¬ P r₀ := by
    intro hP0
    exact (hSelf.mp hP0) hP0

  exact hNotP0 (hSelf.mpr hNotP0)

/--
The actual DARM Guard observation boundary therefore cannot exactly
classify every argument-dependent semantic authorization predicate that
distinguishes the two concrete invocations used above.
-/
theorem darm_guard_argument_boundary_is_information_incomplete :
    ¬ ∃ f : Nat → Prop,
      ∀ r : RuntimeInvocation,
        f (guardObservation r) ↔ semanticAuthorized r := by
  let r₀ : RuntimeInvocation := ⟨1, 0⟩
  let r₁ : RuntimeInvocation := ⟨1, 1⟩

  have hObs : guardObservation r₀ = guardObservation r₁ := by
    rfl

  have hSep :
      semanticAuthorized r₀ ↔ ¬ semanticAuthorized r₁ := by
    simp [semanticAuthorized, r₀, r₁]

  exact observation_collision_blocks_exact_semantic_classification
    guardObservation
    semanticAuthorized
    r₀
    r₁
    hObs
    hSep

end GRBS.R22RuntimeSemanticCorrespondence

#print axioms GRBS.R22RuntimeSemanticCorrespondence.runtime_semantic_observation_collapse
#print axioms GRBS.R22RuntimeSemanticCorrespondence.no_observation_only_authorizer
#print axioms GRBS.R22RuntimeSemanticCorrespondence.observation_collision_blocks_exact_semantic_classification
#print axioms GRBS.R22RuntimeSemanticCorrespondence.darm_guard_argument_boundary_is_information_incomplete

namespace GRBS.R22RuntimeSemanticCorrespondence

/--
A runtime admission is semantically bypassing when the runtime admits an
invocation that the semantic authorization predicate rejects.
-/
def SemanticBypass
    {R : Type}
    (runtimeAdmitted : R → Prop)
    (semanticAuthorized : R → Prop)
    (r : R) : Prop :=
  runtimeAdmitted r ∧ ¬ semanticAuthorized r

/--
The current tool-level runtime admits any invocation of an authorized tool.
This deliberately models only the authorization information exposed by
the current DARM Guard integration boundary.
-/
def toolLevelAdmitted (r : RuntimeInvocation) : Prop :=
  r.tool = 1

/--
Concrete R22 semantic policy:
tool 1 is authorized only when its argument is zero.
-/
def r22SemanticAuthorized (r : RuntimeInvocation) : Prop :=
  r.tool = 1 ∧ r.argument = 0

/--
The concrete invocation (tool 1, argument 1) is admitted by the
tool-level boundary while being semantically unauthorized.
-/
theorem r22_semantic_bypass_witness :
    SemanticBypass
      toolLevelAdmitted
      r22SemanticAuthorized
      ⟨1, 1⟩ := by
  constructor
  · rfl
  · simp [r22SemanticAuthorized]

end GRBS.R22RuntimeSemanticCorrespondence

#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_semantic_bypass_witness

namespace GRBS.R22RuntimeSemanticCorrespondence

/--
The old runtime representation exposes only tool identity.
-/
def oldRuntimeRepresentation (r : RuntimeInvocation) : Nat :=
  r.tool

/--
The refined runtime representation preserves tool identity while adding
the invocation argument.
-/
def refinedRuntimeRepresentation (r : RuntimeInvocation) : Nat × Nat :=
  (r.tool, r.argument)

/--
Projection from the refined representation back to the old representation.
-/
def projectRefinedRuntime : Nat × Nat → Nat :=
  Prod.fst

/--
The R22 refinement preserves the old runtime identity exactly.
-/
theorem r22_representation_refines :
    GRBS.R21RepairAdequacy.RepresentationRefines
      oldRuntimeRepresentation
      refinedRuntimeRepresentation
      projectRefinedRuntime := by
  intro r
  rfl

/--
The refinement is strict: the old representation identifies the two
invocations, while the refined representation distinguishes them.
-/
theorem r22_refinement_is_strict :
    oldRuntimeRepresentation ⟨1, 0⟩ =
      oldRuntimeRepresentation ⟨1, 1⟩ ∧
    refinedRuntimeRepresentation ⟨1, 0⟩ ≠
      refinedRuntimeRepresentation ⟨1, 1⟩ := by
  constructor
  · rfl
  · intro h
    have hArg : (0 : Nat) = 1 :=
      congrArg Prod.snd h
    simp at hArg

end GRBS.R22RuntimeSemanticCorrespondence

namespace GRBS.R22RuntimeSemanticCorrespondence

/--
The refined runtime representation contains exactly the information
needed by the concrete R22 semantic authorization predicate.
-/
theorem refined_representation_recovers_r22_authorization :
    ∀ r : RuntimeInvocation,
      r22SemanticAuthorized r ↔
        refinedRuntimeRepresentation r = (1, 0) := by
  intro r
  constructor
  · intro h
    rcases h with ⟨hTool, hArg⟩
    simp [refinedRuntimeRepresentation, hTool, hArg]
  · intro h
    have hTool : r.tool = 1 := by
      have h := congrArg Prod.fst h
      simpa [refinedRuntimeRepresentation] using h
    have hArg : r.argument = 0 := by
      have h := congrArg Prod.snd h
      simpa [refinedRuntimeRepresentation] using h
    exact ⟨hTool, hArg⟩

/--
The refined representation admits an exact classifier for the concrete
R22 semantic authorization predicate.
-/
theorem refined_representation_has_exact_semantic_classifier :
    ∃ f : Nat × Nat → Prop,
      ∀ r : RuntimeInvocation,
        f (refinedRuntimeRepresentation r) ↔
          r22SemanticAuthorized r := by
  refine ⟨fun x => x = (1, 0), ?_⟩
  intro r
  exact (refined_representation_recovers_r22_authorization r).symm

end GRBS.R22RuntimeSemanticCorrespondence

#print axioms GRBS.R22RuntimeSemanticCorrespondence.refined_representation_recovers_r22_authorization
#print axioms GRBS.R22RuntimeSemanticCorrespondence.refined_representation_has_exact_semantic_classifier

namespace GRBS.R22RuntimeSemanticCorrespondence

/--
The refined representation separates the semantically authorized and
semantically unauthorized members of the concrete R22 tool domain.
-/
theorem refined_representation_separates_r22_authorization :
    refinedRuntimeRepresentation ⟨1, 0⟩ ≠
      refinedRuntimeRepresentation ⟨1, 1⟩ ∧
    r22SemanticAuthorized ⟨1, 0⟩ ∧
    ¬ r22SemanticAuthorized ⟨1, 1⟩ := by
  constructor
  · intro h
    have hArg : (0 : Nat) = 1 :=
      congrArg Prod.snd h
    simp at hArg
  constructor
  · simp [r22SemanticAuthorized]
  · simp [r22SemanticAuthorized]

/--
The representation refinement removes the concrete R22 observation
collision responsible for the semantic classification failure.
-/
theorem r22_refinement_removes_observation_collision :
    oldRuntimeRepresentation ⟨1, 0⟩ =
      oldRuntimeRepresentation ⟨1, 1⟩ ∧
    refinedRuntimeRepresentation ⟨1, 0⟩ ≠
      refinedRuntimeRepresentation ⟨1, 1⟩ := by
  exact r22_refinement_is_strict

/--
The concrete R22 semantic bypass is eliminated at the representation
level once the refined representation is used for authorization.
-/
theorem refined_r22_authorization_rejects_bypass :
    ¬ (
      (refinedRuntimeRepresentation ⟨1, 1⟩ = (1, 0)) ∧
      ¬ r22SemanticAuthorized ⟨1, 1⟩
    ) := by
  intro h
  rcases h with ⟨hRep, hNotAuth⟩
  have hAuth : r22SemanticAuthorized ⟨1, 1⟩ :=
    (refined_representation_recovers_r22_authorization ⟨1, 1⟩).mpr hRep
  exact hNotAuth hAuth

end GRBS.R22RuntimeSemanticCorrespondence

#print axioms GRBS.R22RuntimeSemanticCorrespondence.refined_representation_separates_r22_authorization
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_refinement_removes_observation_collision
#print axioms GRBS.R22RuntimeSemanticCorrespondence.refined_r22_authorization_rejects_bypass

namespace GRBS.R22RuntimeSemanticCorrespondence

/--
A refined runtime decision is semantically sound when every invocation
admitted by the refined representation satisfies the semantic
authorization predicate.
-/
def RefinedRuntimeSemanticSound
    (admitDecision : Nat × Nat → Prop)
    (semanticAuthorized : RuntimeInvocation → Prop) : Prop :=
  ∀ r,
    admitDecision (refinedRuntimeRepresentation r) →
      semanticAuthorized r

/--
The concrete R22 semantic classifier admits exactly the representation
corresponding to tool 1 with argument 0.
-/
def r22RefinedAdmit (x : Nat × Nat) : Prop :=
  x = (1, 0)

/--
The concrete refined classifier is semantically sound.
-/
theorem r22_refined_classifier_is_semantically_sound :
    RefinedRuntimeSemanticSound
      r22RefinedAdmit
      r22SemanticAuthorized := by
  intro r hAdmit
  exact
    (refined_representation_recovers_r22_authorization r).mpr hAdmit

/--
The old tool-level admission predicate is not semantically sound for
the concrete R22 semantic authorization policy.
-/
theorem r22_old_runtime_admission_is_not_semantically_sound :
    ¬ RefinedRuntimeSemanticSound
        (fun x : Nat × Nat => x.1 = 1)
        r22SemanticAuthorized := by
  intro hSound
  let hUnsafe : RuntimeInvocation := ⟨1, 1⟩
  have hAdmitted :
      (fun x : Nat × Nat => x.1 = 1)
        (refinedRuntimeRepresentation hUnsafe) := by
    simp [hUnsafe, refinedRuntimeRepresentation]
  have hAuthorized :
      r22SemanticAuthorized hUnsafe :=
    hSound hUnsafe hAdmitted
  simp [hUnsafe, r22SemanticAuthorized] at hAuthorized


/--
The refinement therefore changes the semantic status of the concrete
bypass witness: the old representation admits it, while the refined
semantic classifier rejects it.
-/
theorem r22_refinement_repairs_semantic_soundness :
    RefinedRuntimeSemanticSound
        r22RefinedAdmit
        r22SemanticAuthorized ∧
    ¬ RefinedRuntimeSemanticSound
        (fun x : Nat × Nat => x.1 = 1)
        r22SemanticAuthorized := by
  constructor
  · exact r22_refined_classifier_is_semantically_sound
  · exact r22_old_runtime_admission_is_not_semantically_sound

end GRBS.R22RuntimeSemanticCorrespondence

#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_refined_classifier_is_semantically_sound
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_old_runtime_admission_is_not_semantically_sound
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_refinement_repairs_semantic_soundness

namespace GRBS.R22RuntimeSemanticCorrespondence

/--
A runtime authorization predicate corresponds to the refined semantic
classifier when it makes exactly the same admission decision for every
runtime invocation.
-/
def RuntimeAuthorizationCorrespondence
    (runtimeAdmit : RuntimeInvocation → Prop)
    (refinedAdmit : Nat × Nat → Prop) : Prop :=
  ∀ r,
    runtimeAdmit r ↔
      refinedAdmit (refinedRuntimeRepresentation r)

/--
A runtime authorization implementation is semantically sound when every
runtime-admitted invocation satisfies the semantic authorization predicate.
-/
def RuntimeSemanticSound
    (runtimeAdmit : RuntimeInvocation → Prop)
    (semanticAuthorized : RuntimeInvocation → Prop) : Prop :=
  ∀ r,
    runtimeAdmit r →
      semanticAuthorized r

/--
Implementation correspondence with the refined classifier transfers the
refined classifier's semantic soundness to the runtime authorization
predicate.
-/
theorem runtime_correspondence_transfers_semantic_soundness
    (runtimeAdmit : RuntimeInvocation → Prop)
    (hCorrespondence :
      RuntimeAuthorizationCorrespondence
        runtimeAdmit
        r22RefinedAdmit) :
    RuntimeSemanticSound
      runtimeAdmit
      r22SemanticAuthorized := by
  intro r hRuntime
  have hRefined :
      r22RefinedAdmit (refinedRuntimeRepresentation r) :=
    (hCorrespondence r).mp hRuntime
  exact
    r22_refined_classifier_is_semantically_sound r hRefined

/--
The current tool-level runtime admission predicate does not correspond
to the refined semantic classifier.
-/
theorem current_tool_level_admission_lacks_refined_correspondence :
    ¬ RuntimeAuthorizationCorrespondence
        (fun r : RuntimeInvocation => r.tool = 1)
        r22RefinedAdmit := by
  intro hCorrespondence
  let rUnsafe : RuntimeInvocation := ⟨1, 1⟩
  have hRuntime :
      (fun r : RuntimeInvocation => r.tool = 1) rUnsafe := by
    simp [rUnsafe]
  have hRefined :
      r22RefinedAdmit (refinedRuntimeRepresentation rUnsafe) :=
    (hCorrespondence rUnsafe).mp hRuntime
  simp [rUnsafe, r22RefinedAdmit, refinedRuntimeRepresentation] at hRefined

/--
For the concrete R22 policy, semantic soundness of the runtime therefore
requires a correspondence obligation that the current tool-level
admission predicate does not satisfy.
-/
theorem r22_runtime_soundness_requires_refined_correspondence :
    RuntimeAuthorizationCorrespondence
        (fun r : RuntimeInvocation => r.tool = 1)
        r22RefinedAdmit →
      RuntimeSemanticSound
        (fun r : RuntimeInvocation => r.tool = 1)
        r22SemanticAuthorized := by
  intro hCorrespondence
  exact
    runtime_correspondence_transfers_semantic_soundness
      (fun r : RuntimeInvocation => r.tool = 1)
      hCorrespondence

end GRBS.R22RuntimeSemanticCorrespondence

#print axioms GRBS.R22RuntimeSemanticCorrespondence.runtime_correspondence_transfers_semantic_soundness
#print axioms GRBS.R22RuntimeSemanticCorrespondence.current_tool_level_admission_lacks_refined_correspondence
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_runtime_soundness_requires_refined_correspondence

namespace GRBS.R22RuntimeSemanticCorrespondence

/--
R22-G models a minimal stateful composition:
`set_argument` changes the semantic argument state, after which
`demo` consumes that state.
-/
structure ComposedState where
  argument : Nat

/--
The two runtime operations used in the compositional countermodel.
-/
inductive ComposedTool where
  | setArgument
  | demo
deriving DecidableEq

/--
The current tool-level authorization model authorizes both operations
independently.
-/
def toolIndividuallyAuthorized : ComposedTool → Prop
  | .setArgument => True
  | .demo => True

/--
The semantic authorization policy permits the demo effect only when
the resulting argument is zero.
-/
def composedSemanticAuthorized (s : ComposedState) : Prop :=
  s.argument = 0

/--
The semantic state transition induced by `set_argument(1)`.
-/
def setArgumentTransition
    (_s : ComposedState) : ComposedState :=
  { argument := 1 }

/--
The semantic effect produced by invoking `demo` against the current
state is represented by the state itself.
-/
def demoEffectAuthorized (s : ComposedState) : Prop :=
  composedSemanticAuthorized s

/--
Both component operations are individually authorized.
-/
theorem r22_composed_tools_individually_authorized :
    toolIndividuallyAuthorized .setArgument ∧
    toolIndividuallyAuthorized .demo := by
  constructor <;> trivial

/--
Starting from the safe state, the individually authorized
`set_argument(1)` transition reaches the semantically unauthorized
state required by the R22-G countermodel.
-/
theorem r22_composition_reaches_unauthorized_state :
    let initial : ComposedState := { argument := 0 }
    let afterSet := setArgumentTransition initial
    toolIndividuallyAuthorized .setArgument ∧
    toolIndividuallyAuthorized .demo ∧
    ¬ composedSemanticAuthorized afterSet := by
  dsimp [setArgumentTransition, composedSemanticAuthorized,
    toolIndividuallyAuthorized]
  constructor
  · trivial
  constructor
  · trivial
  · decide

/--
The second individually authorized operation can therefore be invoked
at a state that violates the semantic authorization condition.
-/
theorem r22_composed_semantic_bypass :
    let initial : ComposedState := { argument := 0 }
    let afterSet := setArgumentTransition initial
    toolIndividuallyAuthorized .setArgument ∧
    toolIndividuallyAuthorized .demo ∧
    ¬ demoEffectAuthorized afterSet := by
  exact r22_composition_reaches_unauthorized_state

/--
Individual tool authorization does not imply authorization of the
composed semantic effect.
-/
theorem individual_authorization_does_not_imply_composed_semantic_authorization :
    ¬ (
      ∀ s : ComposedState,
        toolIndividuallyAuthorized .setArgument →
        toolIndividuallyAuthorized .demo →
        composedSemanticAuthorized (setArgumentTransition s)
    ) := by
  intro h
  let initial : ComposedState := { argument := 0 }
  have hAuthorized :
      composedSemanticAuthorized (setArgumentTransition initial) :=
    h initial trivial trivial
  simp [setArgumentTransition, composedSemanticAuthorized] at hAuthorized

end GRBS.R22RuntimeSemanticCorrespondence

#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_composed_tools_individually_authorized
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_composition_reaches_unauthorized_state
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_composed_semantic_bypass
#print axioms GRBS.R22RuntimeSemanticCorrespondence.individual_authorization_does_not_imply_composed_semantic_authorization

namespace GRBS.R22RuntimeSemanticCorrespondence

/--
R22-H embeds the compositional countermodel into the R20 semantic
system interface.
-/
def r22SemanticSystem : GRBS.R20DARMToSemanticCorrespondence.SemanticSystem where
  State := ComposedState
  Step := fun x y =>
    x.argument = 0 ∧ y.argument = 1

/--
The semantic guarantee used by the R22-H instantiation.
The authorized semantic state is precisely argument zero.
-/
def r22SemanticGuarantee :
    GRBS.R20DARMToSemanticCorrespondence.SemanticGuarantee
      r22SemanticSystem where
  property := composedSemanticAuthorized

/--
The R22 semantic boundary mediates no semantic transition.
This deliberately isolates the mediation obligation from the
representation and realization obligations tested below.
-/
def r22SemanticBoundary :
    GRBS.R20DARMToSemanticCorrespondence.SemanticBoundary
      r22SemanticSystem where
  mediated := fun _ _ => False

/--
A single dependency represents the composed semantic effect.
-/
inductive R22Dependency where
  | composedDemo
deriving DecidableEq

/--
Realization of the composed dependency into the semantic system.
-/
def r22Realize :
    GRBS.R20DARMToSemanticCorrespondence.SemanticRealization
      R22Dependency
      r22SemanticSystem :=
  fun d =>
    match d with
    | .composedDemo =>
        {
          dependency := d
          source := { argument := 0 }
          target := { argument := 1 }
        }

/--
The composed dependency is relevant to the semantic transition.
-/
def r22Relevant
    (d :
      GRBS.R20DARMToSemanticCorrespondence.SemanticDependency
        R22Dependency
        r22SemanticSystem.State) : Prop :=
  d.dependency = .composedDemo

/--
The R22 composed transition is causeable in the semantic model.
-/
def r22Causeable :
    GRBS.R20DARMToSemanticCorrespondence.SemanticCauseableTransition
      r22SemanticSystem.State :=
  fun x y =>
    x.argument = 0 ∧ y.argument = 1

 /--
The composed transition crosses the semantic guarantee boundary:
the source state satisfies the semantic authorization guarantee,
while the target state does not.
-/
theorem r22_composition_crosses_semantic_guarantee :
    let source : ComposedState := { argument := 0 }
    let target : ComposedState := { argument := 1 }
    r22SemanticGuarantee.property source ∧
      ¬ r22SemanticGuarantee.property target := by
  simp [r22SemanticGuarantee, composedSemanticAuthorized]

/--
The R22 composed transition is realized exactly by the composed
dependency, establishing the relevant causal-domain coverage.
-/
theorem r22_composition_has_r20_causal_coverage :
    GRBS.R20DARMToSemanticCorrespondence.RelevantRealizationCausalCoverage
      r22SemanticSystem
      r22SemanticBoundary
      r22Realize
      r22Relevant
      r22Causeable := by
  intro x y hCauseable
  cases x with
  | mk xarg =>
      cases y with
      | mk yarg =>
          have hx : xarg = 0 := hCauseable.1
          have hy : yarg = 1 := hCauseable.2
          subst xarg
          subst yarg
          exact ⟨.composedDemo, rfl, rfl, rfl⟩


 /--
The relevant composed dependency is not transition-adequate in the
R20 semantic realization interface because its realized transition
is not boundary-mediated.
-/
theorem r22_composed_realization_is_not_transition_adequate :
    ¬ GRBS.R20DARMToSemanticCorrespondence.RelevantRealizationsTransitionAdequate
      r22SemanticSystem
      r22SemanticBoundary
      r22Realize
      r22Relevant := by
  intro hAdequate
  have hTransition :=
    hAdequate .composedDemo (by rfl)
  exact hTransition.2

/--
Despite causal-domain coverage, the composed dependency is not
boundary-mediated because the semantic boundary rejects the
unauthorized transition.
-/
theorem r22_composition_is_not_semantic_realization_adequate :
    ¬ GRBS.R20DARMToSemanticCorrespondence.SemanticRealizationAdequate
      r22SemanticSystem
      r22SemanticGuarantee
      r22SemanticBoundary
      r22Realize
      r22Relevant
      (fun _ => True) := by
  intro hAdequate
  exact
    r22_composed_realization_is_not_transition_adequate
      hAdequate.2.1

theorem r22_composition_lacks_semantic_mediation :
    ¬ GRBS.R20DARMToSemanticCorrespondence.SemanticMediatedCausalCoverage
      r22SemanticSystem
      r22SemanticBoundary
      r22Realize
      r22Relevant
      r22Causeable := by
  intro hCoverage
  let x : ComposedState := { argument := 0 }
  let y : ComposedState := { argument := 1 }
  have hCauseable : r22Causeable x y := by
    simp [r22Causeable, x, y]
  rcases hCoverage x y hCauseable with
    ⟨d, hRelevant, hMediated, hSource, hTarget⟩
  have hFalse : False := hMediated.2
  exact hFalse

/--
R22-J introduces an explicitly transition-valued request.

Unlike RuntimeInvocation, this object records both semantic endpoints.
The old representation exposes only the tool identity. The refined
representation preserves that identity while adding the transition
endpoints needed by the R20 semantic realization layer.
-/
structure R22TransitionRequest where
  tool : ComposedTool
  source : ComposedState
  target : ComposedState

def oldTransitionRepresentation
    (r : R22TransitionRequest) : ComposedTool :=
  r.tool

def refinedTransitionRepresentation
    (r : R22TransitionRequest) :
    ComposedTool × ComposedState × ComposedState :=
  (r.tool, r.source, r.target)

def projectRefinedTransition :
    ComposedTool × ComposedState × ComposedState → ComposedTool :=
  fun x => x.1

theorem r22_transition_representation_refines :
    GRBS.R21RepairAdequacy.RepresentationRefines
      oldTransitionRepresentation
      refinedTransitionRepresentation
      projectRefinedTransition := by
  intro r
  rfl

theorem r22_transition_refinement_preserves_endpoints :
    ∀ r : R22TransitionRequest,
      (refinedTransitionRepresentation r).2.1 = r.source ∧
      (refinedTransitionRepresentation r).2.2 = r.target := by
  intro r
  constructor <;> rfl

/--
R22-J realization of the refined transition representation.

The realization preserves the transition dependency and exposes exactly
the source and target states carried by the refined representation.
This establishes representation-to-transition correspondence without
yet asserting boundary mediation.
-/
def r22RefinedTransitionRealize :
    GRBS.R20DARMToSemanticCorrespondence.SemanticRealization
      (ComposedTool × ComposedState × ComposedState)
      r22SemanticSystem :=
  fun d =>
    {
      dependency := d
      source := d.2.1
      target := d.2.2
    }

theorem r22_refined_transition_realization_is_faithful :
    GRBS.R20DARMToSemanticCorrespondence.RealizationFaithful
      r22RefinedTransitionRealize := by
  intro d
  rfl

def r22RefinedTransitionRelevant
    (d :
      GRBS.R20DARMToSemanticCorrespondence.SemanticDependency
        (ComposedTool × ComposedState × ComposedState)
        r22SemanticSystem.State) : Prop :=
  d.dependency.1 = .demo

theorem r22_refined_transition_is_relevant :
    r22RefinedTransitionRelevant
      (r22RefinedTransitionRealize
        (.demo, { argument := 0 }, { argument := 1 })) := by
  rfl

theorem r22_refined_transition_realization_recovers_endpoints :
    (r22RefinedTransitionRealize
      (.demo, { argument := 0 }, { argument := 1 })).source =
        ({ argument := 0 } : ComposedState) ∧
    (r22RefinedTransitionRealize
      (.demo, { argument := 0 }, { argument := 1 })).target =
        ({ argument := 1 } : ComposedState) := by
  constructor <;> rfl

/--
Faithful realization of the refined transition representation does not
imply R20 transition adequacy. The realized transition can be exactly
the intended semantic transition while remaining outside the mediated
boundary.
-/
theorem r22_refined_realization_is_not_transition_adequate :
    ¬ GRBS.R20DARMToSemanticCorrespondence.RelevantRealizationsTransitionAdequate
      r22SemanticSystem
      r22SemanticBoundary
      r22RefinedTransitionRealize
      r22RefinedTransitionRelevant := by
  intro hAdequate

  have hTransition :=
    hAdequate
      (.demo, { argument := 0 }, { argument := 1 })
      (by rfl)

  exact hTransition.2

end GRBS.R22RuntimeSemanticCorrespondence

#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_transition_representation_refines
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_transition_refinement_preserves_endpoints
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_refined_transition_realization_is_faithful
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_refined_transition_is_relevant
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_refined_transition_realization_recovers_endpoints
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_refined_realization_is_not_transition_adequate
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_composition_crosses_semantic_guarantee
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_composition_has_r20_causal_coverage
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_composed_realization_is_not_transition_adequate
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_composition_is_not_semantic_realization_adequate
#print axioms GRBS.R22RuntimeSemanticCorrespondence.r22_composition_lacks_semantic_mediation
