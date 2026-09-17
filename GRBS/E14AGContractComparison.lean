import GRBS
import AGBypass
import GRBS.E13CausalSemanticCorrespondence
import GRBS.R20DARMToSemanticCorrespondence

namespace GRBS
namespace E14AGContractComparison

open AGBypass
open E13CausalSemanticCorrespondence
open R20DARMToSemanticCorrespondence

/--
E14-A:
Test whether the existing behavioral AG judgment entails
effect-representation completeness.

The AGBypass S2 witness exposes only `Tr.ok` through the
interface-visible trace relation, while its physical substrate
contains a live `d0` path to `Tr.violated`.
-/

def e14Assumption : AGAssumption :=
  fun _ => True

def e14Causeable :
    CauseableTransition AGBypass.Witness.Tr :=
  fun s s' =>
    ∃ d : AGBypass.Witness.Ch,
      AGBypass.Witness.S2.physicalStep d s' ∧
      s = AGBypass.Witness.Tr.ok

/-- Empty effect representation: no physical transition is represented. -/
def e14Represents :
    Represents AGBypass.Witness.Ch AGBypass.Witness.Tr :=
  fun _ _ _ => False

/--
The existing behavioral AG judgment is satisfied.

Every interface-visible trace of S2 is `ok`, and the guarantee
holds on `ok`.
-/
theorem ag_satisfaction_holds :
    AGSatisfiesAdm
      e14Assumption
      AGBypass.Witness.g
      AGBypass.Witness.S2 := by
  intro e hAdm hA t ht
  exact ht ▸ True.intro

/--
The physical causeable domain contains an unsafe transition.
-/
theorem unsafe_causeable_exists :
    ∃ s s',
      e14Causeable s s' ∧
      ¬ AGBypass.Witness.g s' := by
  obtain ⟨t, hStep, hUnsafe⟩ :=
    AGBypass.Witness.physical_exploit_S2
  refine ⟨AGBypass.Witness.Tr.ok, t, ?_, hUnsafe⟩
  exact ⟨AGBypass.Witness.Ch.d0, hStep, rfl⟩

/--
The existing behavioral AG judgment does not entail
effect-representation completeness.

This is the E14-A counterexample: AG satisfaction holds while
the causeable physical transition domain contains an effect that
has no representation.
-/
theorem ag_does_not_imply_effect_representation :
    AGSatisfiesAdm
      e14Assumption
      AGBypass.Witness.g
      AGBypass.Witness.S2 ∧
    ¬ EffectRepresentationComplete
      e14Causeable
      e14Represents := by
  constructor
  · exact ag_satisfaction_holds
  · intro hComplete
    obtain ⟨s, s', hCauseable, hUnsafe⟩ :=
      unsafe_causeable_exists

    obtain ⟨a, hRepresents⟩ :=
      hComplete s s' hCauseable

    exact hRepresents


/--
E14-B:
An AG judgment becomes sufficient for the causeable domain once an
explicit causal-coverage premise is added.

The coverage premise is deliberately separate from AG satisfaction:
it states that every causeable transition is visible as an
interface trace for every admissible environment satisfying the AG
assumption.

Thus this theorem tests the enriched contract:

  AG satisfaction + causal-domain coverage
    -> safety over the causeable domain.

It does not claim that ordinary AG satisfaction supplies the coverage
premise. E14-A established the contrary.
-/
def AGCauseableCoverage
    {Trace Channel : Type}
    (A : AGAssumption)
    (s : System Trace Channel)
    (causeable : CauseableTransition Trace) : Prop :=
  ∀ s0 s1,
    causeable s0 s1 →
    ∀ e : Environment,
      Admissible s e →
      A e →
      s.interfaceTraces e s1

/--
The enriched AG contract recovers causal safety.
-/
theorem enriched_ag_implies_causeable_safety
    {Trace Channel : Type}
    (A : AGAssumption)
    (g : Guarantee Trace)
    (s : System Trace Channel)
    (causeable : CauseableTransition Trace)
    (hAG : AGSatisfiesAdm A g s)
    (hCoverage : AGCauseableCoverage A s causeable) :
    ∀ s0 s1,
      causeable s0 s1 →
      ∀ e : Environment,
        Admissible s e →
        A e →
        g s1 := by
  intro s0 s1 hCause e hAdm hA
  exact hAG e hAdm hA s1 (hCoverage s0 s1 hCause e hAdm hA)

/--
E14-B applied to a nonempty causeable domain gives safety of every
causeable endpoint under the AG assumptions.
-/
theorem enriched_ag_recovers_causal_safety
    {Trace Channel : Type}
    (A : AGAssumption)
    (g : Guarantee Trace)
    (s : System Trace Channel)
    (causeable : CauseableTransition Trace)
    (hAG : AGSatisfiesAdm A g s)
    (hCoverage : AGCauseableCoverage A s causeable)
    (hEnvironment :
      ∀ e : Environment, Admissible s e → A e) :
    ∀ s0 s1,
      causeable s0 s1 →
      g s1 := by
  intro s0 s1 hCause
  let e : Environment := fun _ => False
  have hAdm : Admissible s e := by
    intro a ha
    exact False.elim ha
  have hA : A e := hEnvironment e hAdm
  exact enriched_ag_implies_causeable_safety
    A g s causeable hAG hCoverage s0 s1 hCause e hAdm hA


/--
E14-C:
An AG formulation can internalize causal coverage if its contract is
explicitly quantified over the causeable domain.

This is deliberately stronger than ordinary `AGSatisfiesAdm`.
It makes the causal-domain obligation part of the contract itself.
The experiment therefore tests whether the missing E14-A premise can
be expressed inside an enriched AG formulation rather than requiring
a distinct logical primitive.
-/
def AGCausalContract
    {Trace Channel : Type}
    (A : AGAssumption)
    (g : Guarantee Trace)
    (s : System Trace Channel)
    (causeable : CauseableTransition Trace) : Prop :=
  AGSatisfiesAdm A g s ∧
  AGCauseableCoverage A s causeable

/--
The enriched AG contract directly entails safety of every causeable
endpoint.

The proof uses only the two components of the enriched contract:
ordinary AG satisfaction and explicit causal coverage.
-/
theorem ag_causal_contract_implies_causeable_safety
    {Trace Channel : Type}
    (A : AGAssumption)
    (g : Guarantee Trace)
    (s : System Trace Channel)
    (causeable : CauseableTransition Trace)
    (hContract : AGCausalContract A g s causeable) :
    ∀ s0 s1,
      causeable s0 s1 →
      ∀ e : Environment,
        Admissible s e →
        A e →
        g s1 := by
  exact enriched_ag_implies_causeable_safety
    A
    g
    s
    causeable
    hContract.1
    hContract.2

/--
E14-C establishes that the missing causal-coverage obligation can be
internalized into an enriched AG contract.

It does not establish that ordinary AG satisfaction already contains
that obligation. E14-A established the contrary.
-/
theorem causal_coverage_is_explicitly_internalizable :
    ∀ (A : AGAssumption)
      (g : Guarantee AGBypass.Witness.Tr)
      (causeable : CauseableTransition AGBypass.Witness.Tr),
      AGCausalContract
        A
        g
        AGBypass.Witness.S2
        causeable →
      ∀ s0 s1,
        causeable s0 s1 →
        ∀ e : Environment,
          Admissible AGBypass.Witness.S2 e →
          A e →
          g s1 := by
  intro A g causeable hContract
  exact ag_causal_contract_implies_causeable_safety
    A
    g
    AGBypass.Witness.S2
    causeable
    hContract


/--
E14-D:
R20 semantic realization adequacy does not by itself imply causal
effect-representation completeness.

This is a non-vacuous countermodel: the sole dependency is relevant,
the realization is faithful to that dependency, the realized transition
is boundary-mediated, and discharge is satisfied. Nevertheless, the
causeable domain contains a transition for which no representation exists.
-/ 
theorem r20_adequacy_does_not_imply_effect_representation :
    ∃
      (D : Type)
      (S : R20DARMToSemanticCorrespondence.SemanticSystem)
      (G : R20DARMToSemanticCorrespondence.SemanticGuarantee S)
      (B : R20DARMToSemanticCorrespondence.SemanticBoundary S)
      (realize :
        R20DARMToSemanticCorrespondence.SemanticRealization D S)
      (relevant :
        R20DARMToSemanticCorrespondence.SemanticDependency D S.State → Prop)
      (discharge : D → Prop)
      (causeable :
        E13CausalSemanticCorrespondence.CauseableTransition S.State),
      R20DARMToSemanticCorrespondence.SemanticRealizationAdequate
        S G B realize relevant discharge ∧
      ¬ E13CausalSemanticCorrespondence.EffectRepresentationComplete
        (Access := D)
        causeable
        (fun _ _ _ => False) := by
  let D := Unit
  let State := Bool

  let S : R20DARMToSemanticCorrespondence.SemanticSystem :=
    { State := State
      Step := fun x y => x = false ∧ y = false }

  let G : R20DARMToSemanticCorrespondence.SemanticGuarantee S :=
    { property := fun _ => True }

  let B : R20DARMToSemanticCorrespondence.SemanticBoundary S :=
    { mediated := fun x y => x = false ∧ y = false }

  let realize :
      R20DARMToSemanticCorrespondence.SemanticRealization D S :=
    fun d =>
      { dependency := d
        source := false
        target := false }

  let relevant :
      R20DARMToSemanticCorrespondence.SemanticDependency D S.State → Prop :=
    fun _ => True

  let discharge : D → Prop :=
    fun _ => True

  let causeable :
      E13CausalSemanticCorrespondence.CauseableTransition S.State :=
    fun x y => x = false ∧ y = true

  refine ⟨
    D,
    S,
    G,
    B,
    realize,
    relevant,
    discharge,
    causeable,
    ?_,
    ?_⟩

  · constructor
    · intro d
      rfl
    constructor
    · intro d hRelevant
      constructor
      · constructor <;> rfl
      · trivial
    · intro d hDischarge hStep hSource
      trivial

  · intro hComplete
    have hRepresents :
        ∃ a : D, False :=
      hComplete false true (by
        constructor <;> rfl)
    exact hRepresents.elim (fun _ hFalse => hFalse)

/--
E14-E:
Effect-representation completeness together with representation-level
complete mediation yields causal coverage.

This is the composition of the two independent obligations:

  1. every causeable effect has a representation;
  2. every represented transition is mediated.

The result is that every causeable transition is itself mediated.
-/
theorem effect_representation_plus_complete_mediation_implies_causal_coverage :
    ∀ {Access State : Type}
      (causeable : CauseableTransition State)
      (represents : Represents Access State)
      (mediated : AccessMediated Access State),
      EffectRepresentationComplete
        causeable
        represents →
      RepresentationCompleteMediation
        represents
        mediated →
      CausalCoverage
        causeable
        (fun s s' =>
          ∃ a,
            represents a s s' ∧
            mediated a s s') := by
  intro Access State causeable represents mediated hRepresentation hMediation
  intro s s' hCauseable
  obtain ⟨a, hRepresents⟩ :=
    hRepresentation s s' hCauseable
  exact ⟨a, hRepresents, hMediation a s s' hRepresents⟩


/--
E14-F:
AG causeable-coverage and E13 effect-representation completeness are
distinct obligations.

A system may expose every causeable endpoint through its AG interface
while having no access-level representation of those effects.
This tests whether E14's enriched AG coverage is already equivalent to
the E13 representation obligation.
-/
theorem ag_causeable_coverage_does_not_imply_effect_representation :
    ∃
      (A : AGAssumption)
      (_g : Guarantee AGBypass.Witness.Tr)
      (s : System AGBypass.Witness.Tr AGBypass.Witness.Ch)
      (causeable : CauseableTransition AGBypass.Witness.Tr)
      (represents : Represents AGBypass.Witness.Ch AGBypass.Witness.Tr),
      AGCauseableCoverage A s causeable ∧
      ¬ EffectRepresentationComplete causeable represents := by
  let A : AGAssumption := fun _ => True

  let s : System AGBypass.Witness.Tr AGBypass.Witness.Ch :=
    { interface := fun _ => True
      interfaceTraces := fun _ _ => True
      physicalStep := AGBypass.Witness.S2.physicalStep
      cov := fun _ => True }

  let causeable : CauseableTransition AGBypass.Witness.Tr :=
    fun s s' => s = AGBypass.Witness.Tr.ok ∧ s' = AGBypass.Witness.Tr.violated

  let represents :
      Represents AGBypass.Witness.Ch AGBypass.Witness.Tr :=
    fun _ _ _ => False

  refine ⟨A, AGBypass.Witness.g, s, causeable, represents, ?_, ?_⟩

  · intro s0 s1 hCause e hAdm hA
    trivial

  · intro hComplete
    have hRepresents :
        ∃ a : AGBypass.Witness.Ch, False :=
      hComplete
        AGBypass.Witness.Tr.ok
        AGBypass.Witness.Tr.violated
        (by
          constructor <;> rfl)
    exact hRepresents.elim (fun _ hFalse => hFalse)



/--
E14-H bridge:
connects an E13 access-level represented and mediated effect to the
AG interface-trace observation model.

This is an explicit cross-layer correspondence. It is not supplied by
E13 effect representation or complete mediation alone.
-/
def E13ToAGTraceBridge
    {Trace Channel : Type}
    (A : AGAssumption)
    (s : System Trace Channel)
    (represents : Represents Channel Trace)
    (mediated : AccessMediated Channel Trace) : Prop :=
  ∀ a s0 s1,
    represents a s0 s1 →
    mediated a s0 s1 →
    ∀ e : Environment,
      Admissible s e →
      A e →
      s.interfaceTraces e s1


/--
E14-G:
E13 effect representation plus complete mediation does not by itself
imply E14 AG causeable coverage.

The E13 obligations can hold for every causeable effect while the AG
interface trace relation exposes none of those effects. Thus a bridge
from access-level representation/mediation to the AG observation model
is an additional obligation.
-/
theorem e13_representation_mediation_does_not_imply_ag_causeable_coverage :
    ∃
      (A : AGAssumption)
      (_g : Guarantee AGBypass.Witness.Tr)
      (s : System AGBypass.Witness.Tr AGBypass.Witness.Ch)
      (causeable : CauseableTransition AGBypass.Witness.Tr)
      (represents :
        Represents
          AGBypass.Witness.Ch
          AGBypass.Witness.Tr)
      (mediated :
        AccessMediated
          AGBypass.Witness.Ch
          AGBypass.Witness.Tr),
      EffectRepresentationComplete causeable represents ∧
      RepresentationCompleteMediation represents mediated ∧
      ¬ AGCauseableCoverage A s causeable := by
  let A : AGAssumption := fun _ => True
  let s : System AGBypass.Witness.Tr AGBypass.Witness.Ch :=
    { interface := fun _ => True
      interfaceTraces := fun _ _ => False
      physicalStep := AGBypass.Witness.S2.physicalStep
      cov := fun _ => True }
  let causeable : CauseableTransition AGBypass.Witness.Tr :=
    fun s s' =>
      s = AGBypass.Witness.Tr.ok ∧
      s' = AGBypass.Witness.Tr.violated
  let represents :
      Represents
        AGBypass.Witness.Ch
        AGBypass.Witness.Tr :=
    fun _ s s' =>
      s = AGBypass.Witness.Tr.ok ∧
      s' = AGBypass.Witness.Tr.violated
  let mediated :
      AccessMediated
        AGBypass.Witness.Ch
        AGBypass.Witness.Tr :=
    fun _ s s' =>
      s = AGBypass.Witness.Tr.ok ∧
      s' = AGBypass.Witness.Tr.violated

  refine ⟨A, AGBypass.Witness.g, s, causeable, represents, mediated, ?_, ?_, ?_⟩

  · intro s0 s1 hCause
    refine ⟨AGBypass.Witness.Ch.d0, ?_⟩
    exact hCause

  · intro a s0 s1 hRepresents
    exact hRepresents

  · intro hCoverage
    have hCause :
        causeable
          AGBypass.Witness.Tr.ok
          AGBypass.Witness.Tr.violated :=
      And.intro rfl rfl

    have hAdmissible :
        Admissible s (fun _ => True) := by
      intro a ha
      trivial

    have hFalse :
        s.interfaceTraces
          (fun _ => True)
          AGBypass.Witness.Tr.violated :=
      hCoverage
        AGBypass.Witness.Tr.ok
        AGBypass.Witness.Tr.violated
        hCause
        (fun _ => True)
        hAdmissible
        trivial

    exact hFalse


/--
E14-H:
Once an explicit E13-to-AG trace correspondence is supplied, E13
effect representation and complete mediation are sufficient to recover
AG causeable coverage.

This isolates the additional cross-layer obligation required to connect
the E13 access/mediation layer to the E14 AG observation layer.
-/
theorem e13_representation_mediation_plus_ag_trace_bridge_implies_ag_causeable_coverage :
    ∀
      {Trace Channel : Type}
      (A : AGAssumption)
      (s : System Trace Channel)
      (causeable : CauseableTransition Trace)
      (represents : Represents Channel Trace)
      (mediated : AccessMediated Channel Trace),
      EffectRepresentationComplete causeable represents →
      RepresentationCompleteMediation represents mediated →
      E13ToAGTraceBridge A s represents mediated →
      AGCauseableCoverage A s causeable := by
  intro Trace Channel A s causeable represents mediated
  intro hRepresentation hMediation hBridge
  intro s0 s1 hCause e hAdm hA
  obtain ⟨a, hRepresents⟩ :=
    hRepresentation s0 s1 hCause
  have hMediated : mediated a s0 s1 :=
    hMediation a s0 s1 hRepresents
  exact hBridge a s0 s1 hRepresents hMediated e hAdm hA



/--
E14-I1:
The E13-to-AG trace bridge alone does not imply AG causeable coverage.
This separates the bridge correspondence from effect representation and
complete mediation.
-/
theorem e13_to_ag_trace_bridge_does_not_imply_ag_causeable_coverage :
    ∃
      (A : AGAssumption)
      (s : System AGBypass.Witness.Tr AGBypass.Witness.Ch)
      (causeable : CauseableTransition AGBypass.Witness.Tr)
      (represents :
        Represents
          AGBypass.Witness.Ch
          AGBypass.Witness.Tr)
      (mediated :
        AccessMediated
          AGBypass.Witness.Ch
          AGBypass.Witness.Tr),
      E13ToAGTraceBridge A s represents mediated ∧
      ¬ AGCauseableCoverage A s causeable := by
  let A : AGAssumption := fun _ => True
  let s : System AGBypass.Witness.Tr AGBypass.Witness.Ch :=
    { interface := fun _ => True
      interfaceTraces := fun _ _ => False
      physicalStep := AGBypass.Witness.S2.physicalStep
      cov := fun _ => True }
  let causeable : CauseableTransition AGBypass.Witness.Tr :=
    fun s s' =>
      s = AGBypass.Witness.Tr.ok ∧
      s' = AGBypass.Witness.Tr.violated
  let represents :
      Represents
        AGBypass.Witness.Ch
        AGBypass.Witness.Tr :=
    fun _ _ _ => False
  let mediated :
      AccessMediated
        AGBypass.Witness.Ch
        AGBypass.Witness.Tr :=
    fun _ _ _ => False
  refine ⟨A, s, causeable, represents, mediated, ?_, ?_⟩
  · intro a s0 s1 hRepresents
    exact False.elim hRepresents
  · intro hCoverage
    have hCause :
        causeable
          AGBypass.Witness.Tr.ok
          AGBypass.Witness.Tr.violated :=
      And.intro rfl rfl
    have hAdmissible :
        Admissible s (fun _ => True) := by
      intro a ha
      trivial
    have hFalse :
        s.interfaceTraces
          (fun _ => True)
          AGBypass.Witness.Tr.violated :=
      hCoverage
        AGBypass.Witness.Tr.ok
        AGBypass.Witness.Tr.violated
        hCause
        (fun _ => True)
        hAdmissible
        trivial
    exact hFalse


/--
E14-I2:
Even with complete effect representation, the E13-to-AG trace bridge
does not imply AG causeable coverage when complete mediation is absent.
This isolates complete mediation as an independent obligation.
-/
theorem e13_to_ag_trace_bridge_plus_effect_representation_does_not_imply_ag_causeable_coverage :
    ∃
      (A : AGAssumption)
      (s : System AGBypass.Witness.Tr AGBypass.Witness.Ch)
      (causeable : CauseableTransition AGBypass.Witness.Tr)
      (represents :
        Represents
          AGBypass.Witness.Ch
          AGBypass.Witness.Tr)
      (mediated :
        AccessMediated
          AGBypass.Witness.Ch
          AGBypass.Witness.Tr),
      E13ToAGTraceBridge A s represents mediated ∧
      EffectRepresentationComplete causeable represents ∧
      ¬ AGCauseableCoverage A s causeable := by
  let A : AGAssumption := fun _ => True
  let s : System AGBypass.Witness.Tr AGBypass.Witness.Ch :=
    { interface := fun _ => True
      interfaceTraces := fun _ _ => False
      physicalStep := AGBypass.Witness.S2.physicalStep
      cov := fun _ => True }
  let causeable : CauseableTransition AGBypass.Witness.Tr :=
    fun s s' =>
      s = AGBypass.Witness.Tr.ok ∧
      s' = AGBypass.Witness.Tr.violated
  let represents :
      Represents
        AGBypass.Witness.Ch
        AGBypass.Witness.Tr :=
    fun _ s0 s1 =>
      s0 = AGBypass.Witness.Tr.ok ∧
      s1 = AGBypass.Witness.Tr.violated
  let mediated :
      AccessMediated
        AGBypass.Witness.Ch
        AGBypass.Witness.Tr :=
    fun _ _ _ => False
  refine ⟨A, s, causeable, represents, mediated, ?_, ?_, ?_⟩
  · intro a s0 s1 hRepresents hMediated
    exact False.elim hMediated
  · intro s0 s1 hCause
    refine ⟨AGBypass.Witness.Ch.d0, ?_⟩
    exact hCause
  · intro hCoverage
    have hCause :
        causeable
          AGBypass.Witness.Tr.ok
          AGBypass.Witness.Tr.violated :=
      And.intro rfl rfl
    have hAdmissible :
        Admissible s (fun _ => True) := by
      intro a ha
      trivial
    have hFalse :
        s.interfaceTraces
          (fun _ => True)
          AGBypass.Witness.Tr.violated :=
      hCoverage
        AGBypass.Witness.Tr.ok
        AGBypass.Witness.Tr.violated
        hCause
        (fun _ => True)
        hAdmissible
        trivial
    exact hFalse




/--
E14-I3:
AG causeable coverage does not establish the full E13-to-AG trace bridge,
even when effect representation and complete mediation hold.

The countermodel contains an additional represented and mediated effect
outside the causeable relation. AG coverage constrains only causeable
effects, while the bridge quantifies over every represented and mediated
effect.
-/
theorem ag_causeable_coverage_plus_e13_obligations_does_not_imply_ag_trace_bridge :
    ∃
      (A : AGAssumption)
      (s : System AGBypass.Witness.Tr AGBypass.Witness.Ch)
      (causeable : CauseableTransition AGBypass.Witness.Tr)
      (represents :
        Represents
          AGBypass.Witness.Ch
          AGBypass.Witness.Tr)
      (mediated :
        AccessMediated
          AGBypass.Witness.Ch
          AGBypass.Witness.Tr),
      AGCauseableCoverage A s causeable ∧
      EffectRepresentationComplete causeable represents ∧
      RepresentationCompleteMediation represents mediated ∧
      ¬ E13ToAGTraceBridge A s represents mediated := by
  let A : AGAssumption := fun _ => True
  let s : System AGBypass.Witness.Tr AGBypass.Witness.Ch :=
    { interface := fun _ => True
      interfaceTraces := fun _ t => t = AGBypass.Witness.Tr.violated
      physicalStep := AGBypass.Witness.S2.physicalStep
      cov := fun _ => True }
  let causeable : CauseableTransition AGBypass.Witness.Tr :=
    fun s0 s1 =>
      s0 = AGBypass.Witness.Tr.ok ∧
      s1 = AGBypass.Witness.Tr.violated
  let represents :
      Represents
        AGBypass.Witness.Ch
        AGBypass.Witness.Tr :=
    fun _ s0 s1 =>
      (s0 = AGBypass.Witness.Tr.ok ∧
        s1 = AGBypass.Witness.Tr.violated) ∨
      (s0 = AGBypass.Witness.Tr.violated ∧
        s1 = AGBypass.Witness.Tr.ok)
  let mediated :
      AccessMediated
        AGBypass.Witness.Ch
        AGBypass.Witness.Tr :=
    fun _ s0 s1 =>
      (s0 = AGBypass.Witness.Tr.ok ∧
        s1 = AGBypass.Witness.Tr.violated) ∨
      (s0 = AGBypass.Witness.Tr.violated ∧
        s1 = AGBypass.Witness.Tr.ok)
  refine ⟨A, s, causeable, represents, mediated, ?_, ?_, ?_, ?_⟩
  · intro s0 s1 hCause e hAdm hA
    exact hCause.2
  · intro s0 s1 hCause
    refine ⟨AGBypass.Witness.Ch.d0, ?_⟩
    exact Or.inl hCause
  · intro a s0 s1 hRepresents
    exact hRepresents
  · intro hBridge
    have hRepresents :
        represents
          AGBypass.Witness.Ch.d0
          AGBypass.Witness.Tr.violated
          AGBypass.Witness.Tr.ok :=
      Or.inr (And.intro rfl rfl)
    have hMediated :
        mediated
          AGBypass.Witness.Ch.d0
          AGBypass.Witness.Tr.violated
          AGBypass.Witness.Tr.ok :=
      Or.inr (And.intro rfl rfl)
    have hAdmissible :
        Admissible s (fun _ => True) := by
      intro a ha
      trivial
    have hTrace :
        s.interfaceTraces
          (fun _ => True)
          AGBypass.Witness.Tr.ok :=
      hBridge
        AGBypass.Witness.Ch.d0
        AGBypass.Witness.Tr.violated
        AGBypass.Witness.Tr.ok
        hRepresents
        hMediated
        (fun _ => True)
        hAdmissible
        trivial
    simp [s] at hTrace


/--
E14-J domain alignment:
the transitions represented and mediated at the E13 access layer are
extensionally identical to the transitions designated causeable by the
AG model.
-/
def E13AGDomainAligned
    {Trace Channel : Type}
    (causeable : CauseableTransition Trace)
    (represents : Represents Channel Trace)
    (mediated : AccessMediated Channel Trace) : Prop :=
  ∀ s0 s1,
    causeable s0 s1 ↔
      ∃ a,
        represents a s0 s1 ∧
        mediated a s0 s1

/--
E14-J1:
Under exact domain alignment, the E13-to-AG trace bridge implies
AG causeable coverage.
-/
theorem e13_to_ag_trace_bridge_implies_ag_causeable_coverage_of_domain_alignment :
    ∀
      {Trace Channel : Type}
      (A : AGAssumption)
      (s : System Trace Channel)
      (causeable : CauseableTransition Trace)
      (represents : Represents Channel Trace)
      (mediated : AccessMediated Channel Trace),
      E13AGDomainAligned causeable represents mediated →
      E13ToAGTraceBridge A s represents mediated →
      AGCauseableCoverage A s causeable := by
  intro Trace Channel A s causeable represents mediated
  intro hAlignment hBridge
  intro s0 s1 hCause e hAdm hA
  obtain ⟨a, hRepresents, hMediated⟩ :=
    (hAlignment s0 s1).mp hCause
  exact hBridge a s0 s1 hRepresents hMediated e hAdm hA



/--
E14-J2:
Under exact domain alignment, AG causeable coverage implies the
E13-to-AG trace bridge.

The reverse implication requires the same domain alignment used by E14-J1.
-/
theorem ag_causeable_coverage_implies_e13_to_ag_trace_bridge_of_domain_alignment :
    ∀
      {Trace Channel : Type}
      (A : AGAssumption)
      (s : System Trace Channel)
      (causeable : CauseableTransition Trace)
      (represents : Represents Channel Trace)
      (mediated : AccessMediated Channel Trace),
      E13AGDomainAligned causeable represents mediated →
      AGCauseableCoverage A s causeable →
      E13ToAGTraceBridge A s represents mediated := by
  intro Trace Channel A s causeable represents mediated
  intro hAlignment hCoverage
  intro a s0 s1 hRepresents hMediated e hAdm hA
  have hCauseable : causeable s0 s1 := by
    exact (hAlignment s0 s1).mpr ⟨a, hRepresents, hMediated⟩
  exact hCoverage s0 s1 hCauseable e hAdm hA

/--
E14-J:
Under exact domain alignment, the E13-to-AG trace bridge and AG
causeable coverage are equivalent.
-/
theorem e13_to_ag_trace_bridge_iff_ag_causeable_coverage_of_domain_alignment :
    ∀
      {Trace Channel : Type}
      (A : AGAssumption)
      (s : System Trace Channel)
      (causeable : CauseableTransition Trace)
      (represents : Represents Channel Trace)
      (mediated : AccessMediated Channel Trace),
      E13AGDomainAligned causeable represents mediated →
      (E13ToAGTraceBridge A s represents mediated ↔
        AGCauseableCoverage A s causeable) := by
  intro Trace Channel A s causeable represents mediated hAlignment
  constructor
  · exact e13_to_ag_trace_bridge_implies_ag_causeable_coverage_of_domain_alignment
      A s causeable represents mediated hAlignment
  · exact ag_causeable_coverage_implies_e13_to_ag_trace_bridge_of_domain_alignment
      A s causeable represents mediated hAlignment


end E14AGContractComparison
end GRBS
