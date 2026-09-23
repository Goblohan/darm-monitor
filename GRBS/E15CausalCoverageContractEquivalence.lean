import GRBS
import R8RichContractSeparation
import E13CausalSemanticCorrespondence
import E14AGContractComparison

namespace GRBS
namespace E15CausalCoverageContractEquivalence

open R8RichContractSeparation
open E13CausalSemanticCorrespondence
open AGBypass
open E14AGContractComparison

/--
E15-A:
Instantiate the R8 contract-level coverage predicate over the actual
state-transition domain.

The dependency predicate is the causeable transition relation.
The contract-level covered predicate is the mediated transition relation.
-/
def TransitionContractCoverage
    {State : Type}
    (causeable : CauseableTransition State)
    (mediated : State → State → Prop) : Prop :=
  R8RichContractSeparation.R8e.ContractCoverage
    (fun p : State × State => mediated p.1 p.2)
    (fun p : State × State => causeable p.1 p.2)

/--
For a transition-indexed dependency domain, R8 contract coverage is
definitionally the same shape as E13 mediated causal coverage.
-/
theorem transition_contract_coverage_iff_mediated_causal_coverage
    {State : Type}
    (causeable : CauseableTransition State)
    (mediated : State → State → Prop) :
    TransitionContractCoverage causeable mediated ↔
      MediatedCausalCoverage causeable mediated := by
  constructor
  · intro h s0 s1 hCause
    exact h (s0, s1) hCause
  · intro h p hp
    exact h p.1 p.2 hp


/--
E15-B:
Ordinary contract coverage can hold while causal coverage fails when
the contract dependency domain does not represent every actual
causeable transition.

The countermodel separates:
1. coverage of the declared dependency domain, and
2. completeness of that domain with respect to actual effects.
-/
def DeclaredDependency : Type := Bool

def declaredDependency
    (d : DeclaredDependency) : Prop :=
  d = true

def declaredCovered
    (d : DeclaredDependency) : Prop :=
  d = true

def declaredRepresents
    (d : DeclaredDependency)
    (s0 s1 : Bool) : Prop :=
  d = true ∧ s0 = true ∧ s1 = true

def actualCauseable
    (s0 s1 : Bool) : Prop :=
  s0 = false ∧ s1 = true

def actualMediated
    (_s0 _s1 : Bool) : Prop :=
  False

theorem e15_b_contract_coverage_holds :
    R8RichContractSeparation.R8e.ContractCoverage
      declaredCovered
      declaredDependency := by
  intro d hd
  exact hd

theorem e15_b_unrepresented_causeable_transition :
    ∃ s0 s1,
      actualCauseable s0 s1 ∧
      ¬ ∃ d : DeclaredDependency,
        declaredDependency d ∧
        declaredRepresents d s0 s1 := by
  refine ⟨false, true, ?_, ?_⟩
  · constructor <;> rfl
  · intro h
    rcases h with ⟨d, hd, hr⟩
    rcases hr with ⟨_, hs0, _⟩
    exact Bool.noConfusion hs0

theorem e15_b_causal_coverage_fails :
    ¬ MediatedCausalCoverage actualCauseable actualMediated := by
  intro h
  have hCause : actualCauseable false true := by
    constructor <;> rfl
  have hMed := h false true hCause
  exact hMed

/--
E15-C:
Ordinary contract coverage recovers causal coverage when two additional
domain-linkage obligations are supplied:

1. every actual causeable transition is represented by a declared
   dependency; and
2. every covered declared dependency mediates every transition that it
   represents.

Thus the missing assurance step is not the coverage predicate itself,
but the correspondence between the declared dependency domain and the
actual causeable-effect domain.
-/
def ContractDomainComplete
    {State D : Type}
    (causeable : CauseableTransition State)
    (dep : D → Prop)
    (represents : D → State → State → Prop) : Prop :=
  ∀ s0 s1,
    causeable s0 s1 →
    ∃ d, dep d ∧ represents d s0 s1

def ContractRepresentationSound
    {State D : Type}
    (covered : D → Prop)
    (represents : D → State → State → Prop)
    (mediated : State → State → Prop) : Prop :=
  ∀ d,
    covered d →
    ∀ s0 s1,
      represents d s0 s1 →
      mediated s0 s1

theorem contract_coverage_plus_domain_linkage_implies_causal_coverage
    {State D : Type}
    (causeable : CauseableTransition State)
    (mediated : State → State → Prop)
    (dep : D → Prop)
    (covered : D → Prop)
    (represents : D → State → State → Prop)
    (hCoverage :
      R8RichContractSeparation.R8e.ContractCoverage covered dep)
    (hComplete :
      ContractDomainComplete causeable dep represents)
    (hSound :
      ContractRepresentationSound covered represents mediated) :
    MediatedCausalCoverage causeable mediated := by
  intro s0 s1 hCause
  rcases hComplete s0 s1 hCause with ⟨d, hDep, hRepresents⟩
  exact hSound d (hCoverage d hDep) s0 s1 hRepresents


/--
E15-D:
Domain completeness is independently necessary.

Contract coverage and representation soundness can both hold while
causal coverage fails if an actual causeable transition has no
corresponding declared dependency.
-/
def dDeclaredDependency : Type := Bool

def dDep
    (d : dDeclaredDependency) : Prop :=
  d = true

def dCovered
    (d : dDeclaredDependency) : Prop :=
  d = true

def dRepresents
    (d : dDeclaredDependency)
    (s0 s1 : Bool) : Prop :=
  d = true ∧ s0 = true ∧ s1 = true

def dCauseable
    (s0 s1 : Bool) : Prop :=
  s0 = false ∧ s1 = true

def dMediated
    (s0 s1 : Bool) : Prop :=
  s0 = true ∧ s1 = true

theorem e15_d_contract_coverage :
    R8RichContractSeparation.R8e.ContractCoverage dCovered dDep := by
  intro d hd
  exact hd

theorem e15_d_representation_soundness :
    ContractRepresentationSound dCovered dRepresents dMediated := by
  intro d hd s0 s1 hRep
  rcases hRep with ⟨_, hs0, hs1⟩
  exact ⟨hs0, hs1⟩

theorem e15_d_domain_completeness_fails :
    ¬ ContractDomainComplete dCauseable dDep dRepresents := by
  intro h
  have hComplete := h false true (by constructor <;> rfl)
  rcases hComplete with ⟨d, hd, hRep⟩
  rcases hRep with ⟨_, hs0, _⟩
  exact Bool.noConfusion hs0

theorem e15_d_causal_coverage_fails :
    ¬ MediatedCausalCoverage dCauseable dMediated := by
  intro h
  have hCause : dCauseable false true := by
    constructor <;> rfl
  have hMed := h false true hCause
  rcases hMed with ⟨hs0, _⟩
  exact Bool.noConfusion hs0


/--
E15-E:
Representation soundness is independently necessary.

Contract coverage and domain completeness can both hold while causal
coverage fails if a covered dependency represents a transition that
is not actually mediated.
-/
def eDeclaredDependency : Type := Bool

def eDep
    (_d : eDeclaredDependency) : Prop :=
  True

def eCovered
    (_d : eDeclaredDependency) : Prop :=
  True

def eRepresents
    (_d : eDeclaredDependency)
    (s0 s1 : Bool) : Prop :=
  s0 = false ∧ s1 = true

def eCauseable
    (s0 s1 : Bool) : Prop :=
  s0 = false ∧ s1 = true

def eMediated
    (s0 s1 : Bool) : Prop :=
  s0 = true ∧ s1 = true

theorem e15_e_contract_coverage :
    R8RichContractSeparation.R8e.ContractCoverage eCovered eDep := by
  intro d hd
  trivial

theorem e15_e_domain_completeness :
    ContractDomainComplete eCauseable eDep eRepresents := by
  intro s0 s1 hCause
  refine ⟨false, ?_, hCause⟩
  trivial

theorem e15_e_representation_soundness_fails :
    ¬ ContractRepresentationSound eCovered eRepresents eMediated := by
  intro h
  have hSound := h false trivial false true
  have hRep : eRepresents false false true := by
    constructor <;> rfl
  have hMed := hSound hRep
  rcases hMed with ⟨hs0, _⟩
  exact Bool.noConfusion hs0

theorem e15_e_causal_coverage_fails :
    ¬ MediatedCausalCoverage eCauseable eMediated := by
  intro h
  have hCause : eCauseable false true := by
    constructor <;> rfl
  have hMed := h false true hCause
  rcases hMed with ⟨hs0, _⟩
  exact Bool.noConfusion hs0


/--
E15-F1:
The E13 representation construction can instantiate the E15 domain-linkage
factorization when every access dependency is declared and covered.

E13 complete mediation supplies E15 representation soundness, while
E13 effect-representation completeness supplies E15 domain completeness.
-/
theorem e15_f1_e13_instantiates_domain_linkage
    {Access State : Type}
    (causeable : CauseableTransition State)
    (represents : Represents Access State)
    (mediated : AccessMediated Access State)
    (hComplete :
      RepresentationCompleteMediation represents mediated)
    (hRepresentation :
      EffectRepresentationComplete causeable represents) :
    ContractDomainComplete
      causeable
      (fun _ : Access => True)
      represents ∧
    ContractRepresentationSound
      (fun _ : Access => True)
      represents
      (AccessMediatedTransition represents mediated) := by
  constructor
  · intro s s' hCause
    obtain ⟨a, hRepresents⟩ :=
      hRepresentation s s' hCause
    exact ⟨a, trivial, hRepresents⟩
  · intro a hCovered s s' hRepresents
    exact ⟨a, hRepresents, hComplete a s s' hRepresents⟩


/--
E15-F2:
E15 domain linkage does not recover E13 representation-level complete
mediation.

A causeable transition has two representations. One is mediated and one is
not. E15 representation soundness is nevertheless satisfied because it only
requires some mediated representation for each covered dependency, whereas
E13 complete mediation requires every representation to be mediated.
-/
theorem e15_f2_domain_linkage_does_not_imply_e13_complete_mediation :
    ∃
      (Access State : Type)
      (causeable : CauseableTransition State)
      (represents : Represents Access State)
      (mediated : AccessMediated Access State),
      ContractDomainComplete
        causeable
        (fun _ : Access => True)
        represents ∧
      ContractRepresentationSound
        (fun _ : Access => True)
        represents
        (AccessMediatedTransition represents mediated) ∧
      ¬ RepresentationCompleteMediation represents mediated := by
  let Access := Bool
  let State := Bool

  let represents : Represents Access State :=
    fun _ s s' =>
      s = false ∧ s' = true

  let mediated : AccessMediated Access State :=
    fun a _ _ => a = true

  let causeable : CauseableTransition State :=
    fun s s' =>
      s = false ∧ s' = true

  refine ⟨Access, State, causeable, represents, mediated, ?_, ?_, ?_⟩

  · intro s s' hCause
    obtain ⟨hs, hs'⟩ := hCause
    exact ⟨true, trivial, hs, hs'⟩

  · intro a hCovered s s' hRepresents
    exact ⟨true, hRepresents, rfl⟩

  · intro hComplete
    have hRepresents : represents false false true := by
      constructor <;> rfl
    have hMediated : mediated false false true :=
      hComplete false false true hRepresents
    exact Bool.noConfusion hMediated


/--
E15-F3:
Mediated causal coverage does not by itself imply E15 contract-domain
completeness when the declared dependency predicate is explicit.

A causeable transition has a mediated representation, but the dependency
representing that transition is not declared by the contract. Thus causal
coverage holds while the linkage from the actual causeable domain into the
declared contract dependency domain fails.
-/
theorem e15_f3_causal_coverage_does_not_imply_domain_completeness :
    ∃
      (Access State : Type)
      (causeable : CauseableTransition State)
      (dep : Access → Prop)
      (represents : Represents Access State)
      (mediated : AccessMediated Access State),
      MediatedCausalCoverage
        causeable
        (AccessMediatedTransition represents mediated) ∧
      ¬ ContractDomainComplete
        causeable
        dep
        represents := by
  let Access := Bool
  let State := Bool

  let dep : Access → Prop :=
    fun a => a = false

  let represents : Represents Access State :=
    fun a s s' =>
      a = true ∧ s = false ∧ s' = true

  let mediated : AccessMediated Access State :=
    fun a _ _ => a = true

  let causeable : CauseableTransition State :=
    fun s s' =>
      s = false ∧ s' = true

  refine ⟨Access, State, causeable, dep, represents, mediated, ?_, ?_⟩

  · intro s s' hCause
    obtain ⟨hs, hs'⟩ := hCause
    subst s
    subst s'
    have hRepresents : represents true false true := by
      constructor
      · rfl
      · constructor
        · rfl
        · rfl
    have hMediated : mediated true false true := by
      rfl
    exact ⟨true, hRepresents, hMediated⟩

  · intro hComplete
    have hCause : causeable false true := by
      constructor <;> rfl
    obtain ⟨d, hDep, hRepresents⟩ :=
      hComplete false true hCause
    have hDepFalse : d = false := hDep
    have hRepTrue : d = true := hRepresents.1
    exact Bool.noConfusion (hDepFalse.symm.trans hRepTrue)


/--
E15-F4:
Contract representation soundness does not by itself imply causal coverage.

The represented contract dependency is internally sound with respect to its
mediated transition, but the causeable transition lies outside the represented
domain. Thus representation soundness holds while domain completeness and
causal coverage both fail.
-/
theorem e15_f4_representation_soundness_does_not_imply_causal_coverage :
    ∃
      (Access State : Type)
      (causeable : CauseableTransition State)
      (dep : Access → Prop)
      (represents : Represents Access State)
      (mediated : AccessMediated Access State),
      ContractRepresentationSound
        (fun _ : Access => True)
        represents
        (AccessMediatedTransition represents mediated) ∧
      ¬ ContractDomainComplete
        causeable
        dep
        represents ∧
      ¬ MediatedCausalCoverage
        causeable
        (AccessMediatedTransition represents mediated) := by
  let Access := Unit
  let State := Bool

  let dep : Access → Prop :=
    fun _ => True

  let represents : Represents Access State :=
    fun _ s s' =>
      s = false ∧ s' = false

  let mediated : AccessMediated Access State :=
    fun _ _ _ => True

  let causeable : CauseableTransition State :=
    fun s s' =>
      s = false ∧ s' = true

  refine ⟨Access, State, causeable, dep, represents, mediated, ?_⟩
  constructor
  · intro d hCovered s s' hRepresents
    exact ⟨d, hRepresents, trivial⟩
  · constructor
    · intro hComplete
      have hCause : causeable false true := by
        constructor <;> rfl
      obtain ⟨d, hDep, hRepresents⟩ :=
        hComplete false true hCause
      have hTarget : (true : Bool) = false := hRepresents.2
      exact Bool.noConfusion hTarget
    · intro hCoverage
      have hCause : causeable false true := by
        constructor <;> rfl
      obtain ⟨d, hRepresents, hMediated⟩ :=
        hCoverage false true hCause
      have hTarget : (true : Bool) = false := hRepresents.2
      exact Bool.noConfusion hTarget


/--
E15-F5:
Contract-domain completeness does not by itself imply causal coverage.

Every causeable transition has a declared dependency representation, so the
contract domain is complete with respect to the causeable domain. However,
the represented transition is not mediated. Thus domain completeness holds
while representation soundness and mediated causal coverage fail.
-/
theorem e15_f5_domain_completeness_does_not_imply_causal_coverage :
    ∃
      (Access State : Type)
      (causeable : CauseableTransition State)
      (dep : Access → Prop)
      (represents : Represents Access State)
      (mediated : AccessMediated Access State),
      ContractDomainComplete
        causeable
        dep
        represents ∧
      ¬ ContractRepresentationSound
        dep
        represents
        (AccessMediatedTransition represents mediated) ∧
      ¬ MediatedCausalCoverage
        causeable
        (AccessMediatedTransition represents mediated) := by
  let Access := Unit
  let State := Bool

  let dep : Access → Prop :=
    fun _ => True

  let represents : Represents Access State :=
    fun _ s s' =>
      s = false ∧ s' = true

  let mediated : AccessMediated Access State :=
    fun _ _ _ => False

  let causeable : CauseableTransition State :=
    fun s s' =>
      s = false ∧ s' = true

  refine ⟨Access, State, causeable, dep, represents, mediated, ?_⟩
  constructor
  · intro s s' hCause
    obtain ⟨hs, hs'⟩ := hCause
    subst s
    subst s'
    have hRepresents : represents () false true := by
      change false = false ∧ true = true
      constructor
      · rfl
      · rfl
    exact ⟨(), trivial, hRepresents⟩
  · constructor
    · intro hSound
      have hDep : dep () := trivial
      have hRepresents : represents () false true := by
        change false = false ∧ true = true
        constructor
        · rfl
        · rfl
      have hMediated :=
        hSound () hDep false true hRepresents
      obtain ⟨d, hRepresents', hMediated'⟩ := hMediated
      exact hMediated'
    · intro hCoverage
      have hCause : causeable false true := by
        constructor <;> rfl
      obtain ⟨d, hRepresents, hMediated⟩ :=
        hCoverage false true hCause
      exact hMediated


end E15CausalCoverageContractEquivalence
end GRBS

namespace GRBS
namespace E15CausalCoverageContractEquivalence

/-
E15-G1:
Test whether enriched AG causeable coverage entails the E15
contract-domain linkage obligation.

The intended separation is that AGCauseableCoverage quantifies directly
over causeable transitions, while ContractDomainComplete additionally
requires each causeable transition to be represented by a declared
dependency.
-/

def g1Trace : Type := Bool
def g1Channel : Type := Unit

def g1Assumption : GRBS.AGBypass.AGAssumption :=
  fun _ => True

def g1Guarantee : GRBS.AGBypass.Guarantee g1Trace :=
  fun t => t = true

def g1System : GRBS.AGBypass.System g1Trace g1Channel :=
  { interface := fun _ => True
    interfaceTraces := fun _ t => t = true
    physicalStep := fun _ _ => False
    cov := fun _ => True }

def g1Causeable : GRBS.E13CausalSemanticCorrespondence.CauseableTransition g1Trace :=
  fun s0 s1 => s0 = false ∧ s1 = true

theorem e15_g1_ag_causeable_coverage :
    GRBS.E14AGContractComparison.AGCauseableCoverage
      g1Assumption
      g1System
      g1Causeable := by
  intro s0 s1 hCause e hAdmissible hA
  have hTarget : s1 = true := hCause.2
  simpa [g1System] using hTarget


theorem e15_g1_ag_coverage_does_not_imply_domain_completeness :
    ∃
      (D : Type)
      (causeable : GRBS.E13CausalSemanticCorrespondence.CauseableTransition g1Trace)
      (dep : D → Prop)
      (represents : D → g1Trace → g1Trace → Prop),
      GRBS.E14AGContractComparison.AGCauseableCoverage
        g1Assumption
        g1System
        causeable ∧
      ¬ ContractDomainComplete
        causeable
        dep
        represents := by
  let D := Unit

  let dep : D → Prop :=
    fun _ => True

  let represents : D → g1Trace → g1Trace → Prop :=
    fun _ s0 s1 =>
      s0 = true ∧ s1 = true

  refine ⟨D, g1Causeable, dep, represents, e15_g1_ag_causeable_coverage, ?_⟩

  intro hComplete
  have hCause : g1Causeable false true := by
    constructor <;> rfl

  obtain ⟨d, hDep, hRepresents⟩ :=
    hComplete false true hCause

  have hTarget : (true : Bool) = false := hRepresents.1.symm
  exact Bool.noConfusion hTarget


/-
E15-G2:
Test the converse separation.

All three E15 contract obligations hold:
  1. contract coverage,
  2. domain completeness,
  3. representation soundness,

while enriched AG causeable coverage fails.

This tests whether E15's causal contract obligations are sufficient
to establish the particular AG observation relation used by E14.
-/

def g2Trace : Type := Bool
def g2Channel : Type := Unit
def g2Dependency : Type := Unit

def g2Assumption : GRBS.AGBypass.AGAssumption :=
  fun _ => True

def g2System : GRBS.AGBypass.System g2Trace g2Channel :=
  { interface := fun _ => True
    interfaceTraces := fun _ t => t = false
    physicalStep := fun _ _ => False
    cov := fun _ => True }

def g2Causeable :
    GRBS.E13CausalSemanticCorrespondence.CauseableTransition g2Trace :=
  fun s0 s1 => s0 = false ∧ s1 = true

def g2Dep : g2Dependency → Prop :=
  fun _ => True

def g2Covered : g2Dependency → Prop :=
  fun _ => True

def g2Represents :
    g2Dependency → g2Trace → g2Trace → Prop :=
  fun _ s0 s1 => s0 = false ∧ s1 = true

def g2Mediated : g2Trace → g2Trace → Prop :=
  fun s0 s1 => s0 = false ∧ s1 = true

theorem e15_g2_contract_coverage :
    R8RichContractSeparation.R8e.ContractCoverage
      g2Covered
      g2Dep := by
  intro d hDep
  trivial

theorem e15_g2_domain_completeness :
    ContractDomainComplete
      g2Causeable
      g2Dep
      g2Represents := by
  intro s0 s1 hCause
  exact ⟨(), trivial, hCause⟩

theorem e15_g2_representation_soundness :
    ContractRepresentationSound
      g2Covered
      g2Represents
      g2Mediated := by
  intro d hCovered s0 s1 hRepresents
  exact hRepresents

theorem e15_g2_ag_causeable_coverage_fails :
    ¬ GRBS.E14AGContractComparison.AGCauseableCoverage
      g2Assumption
      g2System
      g2Causeable := by
  intro hCoverage
  have hCause : g2Causeable false true := by
    constructor <;> rfl
  have hInterface :
      g2System.interfaceTraces
        (fun _ : GRBS.AGBypass.Action => False)
        true := by
    exact hCoverage
      false
      true
      hCause
      (fun _ => False)
      (by
        intro a h
        exact False.elim h)
      trivial
  have hTrace : (true : Bool) = false := hInterface
  exact Bool.noConfusion hTrace

theorem e15_g2_e15_obligations_hold_ag_coverage_fails :
    R8RichContractSeparation.R8e.ContractCoverage
        g2Covered
        g2Dep ∧
      ContractDomainComplete
        g2Causeable
        g2Dep
        g2Represents ∧
      ContractRepresentationSound
        g2Covered
        g2Represents
        g2Mediated ∧
      ¬ GRBS.E14AGContractComparison.AGCauseableCoverage
        g2Assumption
        g2System
        g2Causeable := by
  exact ⟨
    e15_g2_contract_coverage,
    e15_g2_domain_completeness,
    e15_g2_representation_soundness,
    e15_g2_ag_causeable_coverage_fails⟩


/-
E15-G3A:
Test whether the three E15 contract obligations imply the forward
direction of the E14 domain-alignment condition.

The forward direction is:

  causeable s0 s1 ->
    exists d, represents d s0 s1 /\ mediated s0 s1

This is weaker than E14 exact domain alignment because it does not
establish the converse direction.
-/

def E15ForwardDomainCoverage
    {State D : Type}
    (causeable : GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
    (represents : D → State → State → Prop)
    (mediated : State → State → Prop) : Prop :=
  ∀ s0 s1,
    causeable s0 s1 →
    ∃ d,
      represents d s0 s1 ∧
      mediated s0 s1

theorem e15_g3a_obligations_imply_forward_domain_coverage
    {State D : Type}
    (causeable : GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
    (dep : D → Prop)
    (represents : D → State → State → Prop)
    (covered : D → Prop)
    (mediated : State → State → Prop)
    (hCoverage :
      R8RichContractSeparation.R8e.ContractCoverage covered dep)
    (hComplete :
      ContractDomainComplete causeable dep represents)
    (hSound :
      ContractRepresentationSound covered represents mediated) :
    E15ForwardDomainCoverage
      causeable represents mediated := by
  intro s0 s1 hCause
  obtain ⟨d, hDep, hRepresents⟩ :=
    hComplete s0 s1 hCause
  have hCovered : covered d :=
    hCoverage d hDep
  have hMediated : mediated s0 s1 :=
    hSound d hCovered s0 s1 hRepresents
  exact ⟨d, hRepresents, hMediated⟩


/-
E15-G3B:
Test whether the E15 obligations imply the reverse direction of
E14 exact domain alignment.

The reverse direction would require:

  exists d, represents d s0 s1 /\ mediated s0 s1 ->
    causeable s0 s1

E15 does not explicitly require this restriction. The countermodel
therefore tests whether the reverse direction is an independent
correspondence obligation.
-/

def E15ReverseDomainCoverage
    {State D : Type}
    (causeable : GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
    (represents : D → State → State → Prop)
    (mediated : State → State → Prop) : Prop :=
  ∀ s0 s1,
    (∃ d,
      represents d s0 s1 ∧
      mediated s0 s1) →
    causeable s0 s1

theorem e15_g3b_obligations_do_not_imply_reverse_domain_coverage :
    ∃
      (D State : Type)
      (causeable : GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep ∧
      ContractDomainComplete causeable dep represents ∧
      ContractRepresentationSound covered represents mediated ∧
      E15ForwardDomainCoverage
        causeable represents mediated ∧
      ¬ E15ReverseDomainCoverage
        causeable represents mediated := by
  let D := Bool
  let State := Bool

  let causeable :
      GRBS.E13CausalSemanticCorrespondence.CauseableTransition State :=
    fun s0 s1 => s0 = false ∧ s1 = true

  let dep : D → Prop :=
    fun d => d = false

  let covered : D → Prop :=
    fun d => d = false

  let represents : D → State → State → Prop :=
    fun d s0 s1 =>
      (d = false ∧ s0 = false ∧ s1 = true) ∨
      (d = true ∧ s0 = true ∧ s1 = true)

  let mediated : State → State → Prop :=
    fun s0 s1 =>
      (s0 = false ∧ s1 = true) ∨
      (s0 = true ∧ s1 = true)

  refine ⟨D, State, causeable, dep, covered, represents, mediated, ?_⟩

  constructor
  · intro d hDep
    exact hDep

  constructor
  · intro s0 s1 hCause
    rcases hCause with ⟨hs0, hs1⟩
    subst s0
    subst s1
    refine ⟨false, rfl, ?_⟩
    left
    constructor
    · rfl
    · constructor <;> rfl

  constructor
  · intro d hCovered s0 s1 hRepresents
    have hd : d = false := hCovered
    subst d
    rcases hRepresents with h | h
    · left
      constructor
      · exact h.2.1
      · exact h.2.2
    · exact False.elim (Bool.noConfusion h.1)

  constructor
  · exact e15_g3a_obligations_imply_forward_domain_coverage
      causeable
      dep
      represents
      covered
      mediated
      (by
        intro d hDep
        exact hDep)
      (by
        intro s0 s1 hCause
        rcases hCause with ⟨hs0, hs1⟩
        subst s0
        subst s1
        refine ⟨false, rfl, ?_⟩
        left
        constructor
        · rfl
        · constructor <;> rfl)
      (by
        intro d hCovered s0 s1 hRepresents
        have hd : d = false := hCovered
        subst d
        rcases hRepresents with h | h
        · left
          constructor
          · exact h.2.1
          · exact h.2.2
        · exact False.elim (Bool.noConfusion h.1))

  · intro hReverse
    have hWitness :
        ∃ d,
          represents d true true ∧
          mediated true true := by
      refine ⟨true, ?_, ?_⟩
      · right
        constructor
        · rfl
        · constructor <;> rfl
      · right
        constructor <;> rfl

    have hCause : causeable true true :=
      hReverse true true hWitness

    exact Bool.noConfusion hCause.1

/-
E15-G3C:
Test whether the E15 obligations recover enriched AG causeable coverage
when an explicit cross-layer trace bridge is supplied.

The bridge states that whenever a declared dependency is covered and its
representation is mediated, the corresponding endpoint is observable
through the AG system's interface-trace relation.
-/

def E15ToAGTraceBridge
    {Trace Channel D : Type}
    (A : GRBS.AGBypass.AGAssumption)
    (s : GRBS.AGBypass.System Trace Channel)
    (dep : D → Prop)
    (covered : D → Prop)
    (represents : D → Trace → Trace → Prop)
    (mediated : Trace → Trace → Prop) : Prop :=
  ∀ d,
    dep d →
    covered d →
    ∀ s0 s1,
      represents d s0 s1 →
      mediated s0 s1 →
      ∀ e : GRBS.AGBypass.Environment,
        GRBS.AGBypass.Admissible s e →
        A e →
        s.interfaceTraces e s1

theorem e15_g3c_obligations_plus_ag_trace_bridge_imply_ag_causeable_coverage :
    ∀
      {Trace Channel D : Type}
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System Trace Channel)
      (causeable : GRBS.E13CausalSemanticCorrespondence.CauseableTransition Trace)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → Trace → Trace → Prop)
      (mediated : Trace → Trace → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep →
      ContractDomainComplete causeable dep represents →
      ContractRepresentationSound covered represents mediated →
      E15ToAGTraceBridge A s dep covered represents mediated →
      GRBS.E14AGContractComparison.AGCauseableCoverage A s causeable := by
  intro Trace Channel D A s causeable dep covered represents mediated
  intro hCoverage hComplete hSound hBridge
  intro s0 s1 hCause e hAdmissible hA
  obtain ⟨d, hDep, hRepresents⟩ :=
    hComplete s0 s1 hCause
  have hCovered : covered d :=
    hCoverage d hDep
  have hMediated : mediated s0 s1 :=
    hSound d hCovered s0 s1 hRepresents
  exact hBridge d hDep hCovered s0 s1 hRepresents hMediated
    e hAdmissible hA


/-
E15-G3D:
Test whether the E15-to-AG trace bridge is necessary for recovering
AG causeable coverage.

The countermodel keeps all three E15 contract obligations true while
AGCauseableCoverage fails because the mediated transition is not
represented in the AG interface-trace observation relation.
-/

def g3dTrace : Type := Bool
def g3dChannel : Type := Unit
def g3dDependency : Type := Unit

def g3dAssumption : GRBS.AGBypass.AGAssumption :=
  fun _ => True

def g3dSystem : GRBS.AGBypass.System g3dTrace g3dChannel :=
  { interface := fun _ => True
    interfaceTraces := fun _ t => t = false
    physicalStep := fun _ _ => False
    cov := fun _ => True }

def g3dCauseable :
    GRBS.E13CausalSemanticCorrespondence.CauseableTransition g3dTrace :=
  fun s0 s1 => s0 = false ∧ s1 = true

def g3dDep : g3dDependency → Prop :=
  fun _ => True

def g3dCovered : g3dDependency → Prop :=
  fun _ => True

def g3dRepresents :
    g3dDependency → g3dTrace → g3dTrace → Prop :=
  fun _ s0 s1 => s0 = false ∧ s1 = true

def g3dMediated : g3dTrace → g3dTrace → Prop :=
  fun s0 s1 => s0 = false ∧ s1 = true


theorem e15_g3d_e15_obligations_hold :
    R8RichContractSeparation.R8e.ContractCoverage
        g3dCovered
        g3dDep ∧
      ContractDomainComplete
        g3dCauseable
        g3dDep
        g3dRepresents ∧
      ContractRepresentationSound
        g3dCovered
        g3dRepresents
        g3dMediated := by
  exact ⟨
    by
      intro d hDep
      trivial,
    by
      intro s0 s1 hCause
      exact ⟨(), trivial, hCause⟩,
    by
      intro d hCovered s0 s1 hRepresents
      exact hRepresents⟩

theorem e15_g3d_ag_causeable_coverage_fails :
    ¬ GRBS.E14AGContractComparison.AGCauseableCoverage
      g3dAssumption
      g3dSystem
      g3dCauseable := by
  intro hCoverage
  have hCause : g3dCauseable false true := by
    constructor <;> rfl
  have hInterface :
      g3dSystem.interfaceTraces
        (fun _ : GRBS.AGBypass.Action => False)
        true := by
    exact hCoverage
      false
      true
      hCause
      (fun _ => False)
      (by
        intro a h
        exact False.elim h)
      trivial
  have hTrace : (true : Bool) = false := hInterface
  exact Bool.noConfusion hTrace

theorem e15_g3d_bridge_fails :
    ¬ E15ToAGTraceBridge
      g3dAssumption
      g3dSystem
      g3dDep
      g3dCovered
      g3dRepresents
      g3dMediated := by
  intro hBridge
  have hRepresents :
      g3dRepresents () false true := by
    constructor <;> rfl
  have hMediated :
      g3dMediated false true := hRepresents
  have hTrace :=
    hBridge
      ()
      trivial
      trivial
      false
      true
      hRepresents
      hMediated
      (fun _ : GRBS.AGBypass.Action => False)
      (by
        intro a h
        exact False.elim h)
      trivial
  have hFalse : (true : Bool) = false := hTrace
  exact Bool.noConfusion hFalse

theorem e15_g3d_e15_obligations_do_not_imply_ag_causeable_coverage :
    ∃
      (D State : Type)
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System State g3dChannel)
      (causeable : GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep ∧
      ContractDomainComplete causeable dep represents ∧
      ContractRepresentationSound covered represents mediated ∧
      ¬ E15ToAGTraceBridge
        A
        s
        dep
        covered
        represents
        mediated ∧
      ¬ GRBS.E14AGContractComparison.AGCauseableCoverage
        A
        s
        causeable := by
  exact ⟨
    g3dDependency,
    g3dTrace,
    g3dAssumption,
    g3dSystem,
    g3dCauseable,
    g3dDep,
    g3dCovered,
    g3dRepresents,
    g3dMediated,
    e15_g3d_e15_obligations_hold.1,
    e15_g3d_e15_obligations_hold.2.1,
    e15_g3d_e15_obligations_hold.2.2,
    e15_g3d_bridge_fails,
    e15_g3d_ag_causeable_coverage_fails⟩

end E15CausalCoverageContractEquivalence
end GRBS

namespace GRBS
namespace E15CausalCoverageContractEquivalence

/-
E15-G4A:
Factor the E15-to-AG trace bridge into an independent observation
correspondence.

The correspondence says that every mediated transition is observable
as the corresponding endpoint in the AG trace model, under the AG
assumption and admissibility conditions.

This separates:
  E15 contract/domain reasoning
from:
  semantic transition-to-observation correspondence.
-/

def MediatedAGObservationCorrespondence
    {Trace Channel : Type}
    (A : GRBS.AGBypass.AGAssumption)
    (s : GRBS.AGBypass.System Trace Channel)
    (mediated : Trace → Trace → Prop) : Prop :=
  ∀ s0 s1,
    mediated s0 s1 →
    ∀ e : GRBS.AGBypass.Environment,
      GRBS.AGBypass.Admissible s e →
      A e →
      s.interfaceTraces e s1

theorem e15_g4a_observation_correspondence_implies_ag_causeable_coverage :
    ∀
      {Trace Channel D : Type}
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System Trace Channel)
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition Trace)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → Trace → Trace → Prop)
      (mediated : Trace → Trace → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep →
      ContractDomainComplete causeable dep represents →
      ContractRepresentationSound covered represents mediated →
      MediatedAGObservationCorrespondence A s mediated →
      GRBS.E14AGContractComparison.AGCauseableCoverage A s causeable := by
  intro Trace Channel D A s causeable dep covered represents mediated
  intro hCoverage hComplete hSound hObservation
  intro s0 s1 hCause e hAdmissible hA
  obtain ⟨d, hDep, hRepresents⟩ :=
    hComplete s0 s1 hCause
  have hCovered : covered d :=
    hCoverage d hDep
  have hMediated : mediated s0 s1 :=
    hSound d hCovered s0 s1 hRepresents
  exact hObservation s0 s1 hMediated e hAdmissible hA

end E15CausalCoverageContractEquivalence
end GRBS

namespace GRBS
namespace E15CausalCoverageContractEquivalence

/-
E15-G4B:
Test whether the mediated-to-AG observation correspondence is an
independent obligation.

The countermodel preserves all three E15 obligations while the AG
system observes false at the relevant endpoint, although the E15
mediated transition reaches true.
-/

def g4bTrace : Type := Bool
def g4bChannel : Type := Unit
def g4bDependency : Type := Unit

def g4bAssumption : GRBS.AGBypass.AGAssumption :=
  fun _ => True

def g4bSystem : GRBS.AGBypass.System g4bTrace g4bChannel :=
  { interface := fun _ => True
    interfaceTraces := fun _ t => t = false
    physicalStep := fun _ _ => False
    cov := fun _ => True }

def g4bCauseable :
    GRBS.E13CausalSemanticCorrespondence.CauseableTransition g4bTrace :=
  fun s0 s1 => s0 = false ∧ s1 = true

def g4bDep : g4bDependency → Prop :=
  fun _ => True

def g4bCovered : g4bDependency → Prop :=
  fun _ => True

def g4bRepresents :
    g4bDependency → g4bTrace → g4bTrace → Prop :=
  fun _ s0 s1 => s0 = false ∧ s1 = true

def g4bMediated : g4bTrace → g4bTrace → Prop :=
  fun s0 s1 => s0 = false ∧ s1 = true

theorem e15_g4b_e15_obligations_hold :
    R8RichContractSeparation.R8e.ContractCoverage
        g4bCovered
        g4bDep ∧
      ContractDomainComplete
        g4bCauseable
        g4bDep
        g4bRepresents ∧
      ContractRepresentationSound
        g4bCovered
        g4bRepresents
        g4bMediated := by
  exact ⟨
    by
      intro d hDep
      trivial,
    by
      intro s0 s1 hCause
      exact ⟨(), trivial, hCause⟩,
    by
      intro d hCovered s0 s1 hRepresents
      exact hRepresents⟩

theorem e15_g4b_observation_correspondence_fails :
    ¬ MediatedAGObservationCorrespondence
      g4bAssumption
      g4bSystem
      g4bMediated := by
  intro hObservation
  have hMediated : g4bMediated false true := by
    constructor <;> rfl
  have hTrace :=
    hObservation
      false
      true
      hMediated
      (fun _ : GRBS.AGBypass.Action => False)
      (by
        intro a h
        exact False.elim h)
      trivial
  have hFalse : (true : Bool) = false := hTrace
  exact Bool.noConfusion hFalse

theorem e15_g4b_ag_causeable_coverage_fails :
    ¬ GRBS.E14AGContractComparison.AGCauseableCoverage
      g4bAssumption
      g4bSystem
      g4bCauseable := by
  intro hCoverage
  have hCause : g4bCauseable false true := by
    constructor <;> rfl
  have hInterface :
      g4bSystem.interfaceTraces
        (fun _ : GRBS.AGBypass.Action => False)
        true := by
    exact hCoverage
      false
      true
      hCause
      (fun _ => False)
      (by
        intro a h
        exact False.elim h)
      trivial
  have hTrace : (true : Bool) = false := hInterface
  exact Bool.noConfusion hTrace

theorem e15_g4b_e15_obligations_do_not_imply_observation_correspondence :
    ∃
      (D State : Type)
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System State g4bChannel)
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep ∧
      ContractDomainComplete causeable dep represents ∧
      ContractRepresentationSound covered represents mediated ∧
      ¬ MediatedAGObservationCorrespondence A s mediated := by
  exact ⟨
    g4bDependency,
    g4bTrace,
    g4bAssumption,
    g4bSystem,
    g4bCauseable,
    g4bDep,
    g4bCovered,
    g4bRepresents,
    g4bMediated,
    e15_g4b_e15_obligations_hold.1,
    e15_g4b_e15_obligations_hold.2.1,
    e15_g4b_e15_obligations_hold.2.2,
    e15_g4b_observation_correspondence_fails⟩

/--
E15-G4C:
Consolidated assurance-transfer theorem.

The three E15 contract obligations, together with the independent
mediated-to-AG observation correspondence, jointly imply
AG causeable coverage.

This packages the preceding G3C/G4A decomposition into a single
assurance-transfer condition.
-/
theorem e15_g4c_consolidated_assurance_transfer :
    ∀
      {Trace Channel D : Type}
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System Trace Channel)
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition Trace)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → Trace → Trace → Prop)
      (mediated : Trace → Trace → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep →
      ContractDomainComplete causeable dep represents →
      ContractRepresentationSound covered represents mediated →
      MediatedAGObservationCorrespondence A s mediated →
      GRBS.E14AGContractComparison.AGCauseableCoverage A s causeable := by
  intro Trace Channel D A s causeable dep covered represents mediated
  intro hCoverage hComplete hSound hObservation
  intro s0 s1 hCause e hAdmissible hA
  obtain ⟨d, hDep, hRepresents⟩ :=
    hComplete s0 s1 hCause
  have hCovered : covered d :=
    hCoverage d hDep
  have hMediated : mediated s0 s1 :=
    hSound d hCovered s0 s1 hRepresents
  exact hObservation s0 s1 hMediated e hAdmissible hA

/--
E15-ATC:
Explicit assurance-transfer certificate.

The certificate packages the four obligations identified by E15:
contract coverage, domain completeness, representation soundness, and
mediated-to-AG observation correspondence.

It is evidence for an assurance transfer, not itself a safety primitive.
-/
structure AssuranceTransferObligations
    {Trace Channel D : Type}
    (A : GRBS.AGBypass.AGAssumption)
    (s : GRBS.AGBypass.System Trace Channel)
    (causeable :
      GRBS.E13CausalSemanticCorrespondence.CauseableTransition Trace)
    (dep : D → Prop)
    (covered : D → Prop)
    (represents : D → Trace → Trace → Prop)
    (mediated : Trace → Trace → Prop) : Prop where
  contract_coverage :
    R8RichContractSeparation.R8e.ContractCoverage covered dep

  domain_completeness :
    ContractDomainComplete causeable dep represents

  representation_soundness :
    ContractRepresentationSound covered represents mediated

  observation_correspondence :
    MediatedAGObservationCorrespondence A s mediated

/--
Consume an explicit assurance-transfer certificate to obtain AG
causeable coverage.
-/
theorem assurance_transfer_of_obligations
    {Trace Channel D : Type}
    (A : GRBS.AGBypass.AGAssumption)
    (s : GRBS.AGBypass.System Trace Channel)
    (causeable :
      GRBS.E13CausalSemanticCorrespondence.CauseableTransition Trace)
    (dep : D → Prop)
    (covered : D → Prop)
    (represents : D → Trace → Trace → Prop)
    (mediated : Trace → Trace → Prop)
    (h :
      AssuranceTransferObligations
        A s causeable dep covered represents mediated) :
    GRBS.E14AGContractComparison.AGCauseableCoverage A s causeable := by
  exact e15_g4c_consolidated_assurance_transfer
    A s causeable dep covered represents mediated
    h.contract_coverage
    h.domain_completeness
    h.representation_soundness
    h.observation_correspondence
/--
E15-G5A:
Independence of contract coverage.

This countermodel preserves domain completeness, representation
soundness, and mediated-to-AG observation correspondence, while
contract coverage fails and AG causeable coverage fails.

The result establishes necessity of contract coverage within the
current E15 assurance-transfer formulation.
-/

def g5aTrace : Type := Bool
def g5aChannel : Type := Unit
def g5aDependency : Type := Unit

def g5aAssumption : GRBS.AGBypass.AGAssumption :=
  fun _ => True

def g5aSystem : GRBS.AGBypass.System g5aTrace g5aChannel :=
  { interface := fun _ => True
    interfaceTraces := fun _ _ => False
    physicalStep := fun _ _ => False
    cov := fun _ => True }

def g5aCauseable :
    GRBS.E13CausalSemanticCorrespondence.CauseableTransition g5aTrace :=
  fun s0 s1 => s0 = false ∧ s1 = true

def g5aDep : g5aDependency → Prop :=
  fun _ => True

def g5aCovered : g5aDependency → Prop :=
  fun _ => False

def g5aRepresents :
    g5aDependency → g5aTrace → g5aTrace → Prop :=
  fun _ s0 s1 => s0 = false ∧ s1 = true

def g5aMediated : g5aTrace → g5aTrace → Prop :=
  fun _ _ => False

theorem e15_g5a_domain_completeness :
    ContractDomainComplete
      g5aCauseable
      g5aDep
      g5aRepresents := by
  intro s0 s1 hCause
  exact ⟨(), trivial, hCause⟩

theorem e15_g5a_representation_soundness :
    ContractRepresentationSound
      g5aCovered
      g5aRepresents
      g5aMediated := by
  intro d hCovered
  exact False.elim hCovered

theorem e15_g5a_observation_correspondence :
    MediatedAGObservationCorrespondence
      g5aAssumption
      g5aSystem
      g5aMediated := by
  intro s0 s1 hMediated
  exact False.elim hMediated

theorem e15_g5a_contract_coverage_fails :
    ¬ R8RichContractSeparation.R8e.ContractCoverage
      g5aCovered
      g5aDep := by
  intro hCoverage
  have hCovered : g5aCovered () :=
    hCoverage () trivial
  exact hCovered

theorem e15_g5a_ag_causeable_coverage_fails :
    ¬ GRBS.E14AGContractComparison.AGCauseableCoverage
      g5aAssumption
      g5aSystem
      g5aCauseable := by
  intro hCoverage
  have hCause : g5aCauseable false true := by
    constructor <;> rfl
  have hTrace :=
    hCoverage
      false
      true
      hCause
      (fun _ : GRBS.AGBypass.Action => False)
      (by
        intro a h
        exact False.elim h)
      trivial
  simpa [g5aSystem] using hTrace

theorem e15_g5a_obligations_without_contract_coverage_do_not_imply_ag :
    ∃
      (D State : Type)
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System State g5aChannel)
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      ContractDomainComplete causeable dep represents ∧
      ContractRepresentationSound covered represents mediated ∧
      MediatedAGObservationCorrespondence A s mediated ∧
      ¬ R8RichContractSeparation.R8e.ContractCoverage covered dep ∧
      ¬ GRBS.E14AGContractComparison.AGCauseableCoverage A s causeable := by
  exact ⟨
    g5aDependency,
    g5aTrace,
    g5aAssumption,
    g5aSystem,
    g5aCauseable,
    g5aDep,
    g5aCovered,
    g5aRepresents,
    g5aMediated,
    e15_g5a_domain_completeness,
    e15_g5a_representation_soundness,
    e15_g5a_observation_correspondence,
    e15_g5a_contract_coverage_fails,
    e15_g5a_ag_causeable_coverage_fails⟩


def g5bTrace : Type := Bool
def g5bChannel : Type := Unit
def g5bDependency : Type := Unit

def g5bAssumption : GRBS.AGBypass.AGAssumption :=
  fun _ => True

def g5bSystem : GRBS.AGBypass.System g5bTrace g5bChannel :=
  { interface := fun _ => True
    interfaceTraces := fun _ t => t = true
    physicalStep := fun _ _ => False
    cov := fun _ => True }

def g5bCauseable :
    GRBS.E13CausalSemanticCorrespondence.CauseableTransition g5bTrace :=
  fun s0 s1 => s0 = false ∧ s1 = false

def g5bDep : g5bDependency → Prop :=
  fun _ => True

def g5bCovered : g5bDependency → Prop :=
  fun _ => True

def g5bRepresents :
    g5bDependency → g5bTrace → g5bTrace → Prop :=
  fun _ s0 s1 => s0 = true ∧ s1 = true

def g5bMediated : g5bTrace → g5bTrace → Prop :=
  fun s0 s1 => s0 = true ∧ s1 = true

theorem e15_g5b_contract_coverage :
    R8RichContractSeparation.R8e.ContractCoverage
      g5bCovered
      g5bDep := by
  intro d hDep
  trivial

theorem e15_g5b_representation_soundness :
    ContractRepresentationSound
      g5bCovered
      g5bRepresents
      g5bMediated := by
  intro d hCovered s0 s1 hRepresents
  exact hRepresents

theorem e15_g5b_observation_correspondence :
    MediatedAGObservationCorrespondence
      g5bAssumption
      g5bSystem
      g5bMediated := by
  intro s0 s1 hMediated e hAdmissible hA
  exact hMediated.2

theorem e15_g5b_domain_completeness_fails :
    ¬ ContractDomainComplete
      g5bCauseable
      g5bDep
      g5bRepresents := by
  intro hComplete
  obtain ⟨d, hDep, hRepresents⟩ :=
    hComplete false false (by
      constructor <;> rfl)
  exact Bool.noConfusion hRepresents.1

theorem e15_g5b_ag_causeable_coverage_fails :
    ¬ GRBS.E14AGContractComparison.AGCauseableCoverage
      g5bAssumption
      g5bSystem
      g5bCauseable := by
  intro hCoverage
  have hCause : g5bCauseable false false := by
    constructor <;> rfl
  have hTrace :=
    hCoverage
      false
      false
      hCause
      (fun _ : GRBS.AGBypass.Action => False)
      (by
        intro a h
        exact False.elim h)
      trivial
  simpa [g5bSystem] using hTrace

theorem e15_g5b_e15_obligations_do_not_imply_ag_causeable_coverage :
    ∃
      (D State : Type)
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System State g5bChannel)
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep ∧
      ContractRepresentationSound covered represents mediated ∧
      MediatedAGObservationCorrespondence A s mediated ∧
      ¬ ContractDomainComplete causeable dep represents ∧
      ¬ GRBS.E14AGContractComparison.AGCauseableCoverage A s causeable := by
  exact ⟨
    g5bDependency,
    g5bTrace,
    g5bAssumption,
    g5bSystem,
    g5bCauseable,
    g5bDep,
    g5bCovered,
    g5bRepresents,
    g5bMediated,
    e15_g5b_contract_coverage,
    e15_g5b_representation_soundness,
    e15_g5b_observation_correspondence,
    e15_g5b_domain_completeness_fails,
    e15_g5b_ag_causeable_coverage_fails⟩


def g5cTrace : Type := Bool
def g5cChannel : Type := Unit
def g5cDependency : Type := Unit

def g5cAssumption : GRBS.AGBypass.AGAssumption :=
  fun _ => True

def g5cSystem : GRBS.AGBypass.System g5cTrace g5cChannel :=
  { interface := fun _ => True
    interfaceTraces := fun _ _ => False
    physicalStep := fun _ _ => False
    cov := fun _ => True }

def g5cCauseable :
    GRBS.E13CausalSemanticCorrespondence.CauseableTransition g5cTrace :=
  fun s0 s1 => s0 = false ∧ s1 = true

def g5cDep : g5cDependency → Prop :=
  fun _ => True

def g5cCovered : g5cDependency → Prop :=
  fun _ => True

def g5cRepresents :
    g5cDependency → g5cTrace → g5cTrace → Prop :=
  fun _ s0 s1 => s0 = false ∧ s1 = true

def g5cMediated : g5cTrace → g5cTrace → Prop :=
  fun _ _ => False

theorem e15_g5c_contract_coverage :
    R8RichContractSeparation.R8e.ContractCoverage
      g5cCovered
      g5cDep := by
  intro d hDep
  trivial

theorem e15_g5c_domain_completeness :
    ContractDomainComplete
      g5cCauseable
      g5cDep
      g5cRepresents := by
  intro s0 s1 hCause
  exact ⟨(), trivial, hCause⟩

theorem e15_g5c_observation_correspondence :
    MediatedAGObservationCorrespondence
      g5cAssumption
      g5cSystem
      g5cMediated := by
  intro s0 s1 hMediated
  exact False.elim hMediated

theorem e15_g5c_representation_soundness_fails :
    ¬ ContractRepresentationSound
      g5cCovered
      g5cRepresents
      g5cMediated := by
  intro hSound
  have hMediated :
      g5cMediated false true :=
    hSound () trivial false true (by
      constructor <;> rfl)
  exact hMediated

theorem e15_g5c_ag_causeable_coverage_fails :
    ¬ GRBS.E14AGContractComparison.AGCauseableCoverage
      g5cAssumption
      g5cSystem
      g5cCauseable := by
  intro hCoverage
  have hCause : g5cCauseable false true := by
    constructor <;> rfl
  have hTrace :=
    hCoverage
      false
      true
      hCause
      (fun _ : GRBS.AGBypass.Action => False)
      (by
        intro a h
        exact False.elim h)
      trivial
  simpa [g5cSystem] using hTrace

theorem e15_g5c_obligations_without_representation_soundness_do_not_imply_ag :
    ∃
      (D State : Type)
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System State g5cChannel)
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep ∧
      ContractDomainComplete causeable dep represents ∧
      MediatedAGObservationCorrespondence A s mediated ∧
      ¬ ContractRepresentationSound covered represents mediated ∧
      ¬ GRBS.E14AGContractComparison.AGCauseableCoverage A s causeable := by
  exact ⟨
    g5cDependency,
    g5cTrace,
    g5cAssumption,
    g5cSystem,
    g5cCauseable,
    g5cDep,
    g5cCovered,
    g5cRepresents,
    g5cMediated,
    e15_g5c_contract_coverage,
    e15_g5c_domain_completeness,
    e15_g5c_observation_correspondence,
    e15_g5c_representation_soundness_fails,
    e15_g5c_ag_causeable_coverage_fails⟩


def g5dTrace : Type := Bool
def g5dChannel : Type := Unit
def g5dDependency : Type := Unit

def g5dAssumption : GRBS.AGBypass.AGAssumption :=
  fun _ => True

def g5dSystem : GRBS.AGBypass.System g5dTrace g5dChannel :=
  { interface := fun _ => True
    interfaceTraces := fun _ _ => False
    physicalStep := fun _ _ => False
    cov := fun _ => True }

def g5dCauseable :
    GRBS.E13CausalSemanticCorrespondence.CauseableTransition g5dTrace :=
  fun s0 s1 => s0 = false ∧ s1 = true

def g5dDep : g5dDependency → Prop :=
  fun _ => True

def g5dCovered : g5dDependency → Prop :=
  fun _ => True

def g5dRepresents :
    g5dDependency → g5dTrace → g5dTrace → Prop :=
  fun _ s0 s1 => s0 = false ∧ s1 = true

def g5dMediated : g5dTrace → g5dTrace → Prop :=
  fun s0 s1 => s0 = false ∧ s1 = true

theorem e15_g5d_contract_coverage :
    R8RichContractSeparation.R8e.ContractCoverage
      g5dCovered
      g5dDep := by
  intro d hDep
  trivial

theorem e15_g5d_domain_completeness :
    ContractDomainComplete
      g5dCauseable
      g5dDep
      g5dRepresents := by
  intro s0 s1 hCause
  exact ⟨(), trivial, hCause⟩

theorem e15_g5d_representation_soundness :
    ContractRepresentationSound
      g5dCovered
      g5dRepresents
      g5dMediated := by
  intro d hCovered s0 s1 hRepresents
  exact hRepresents

theorem e15_g5d_observation_correspondence_fails :
    ¬ MediatedAGObservationCorrespondence
      g5dAssumption
      g5dSystem
      g5dMediated := by
  intro hObservation
  have hMediated : g5dMediated false true := by
    constructor <;> rfl
  have hTrace :=
    hObservation
      false
      true
      hMediated
      (fun _ : GRBS.AGBypass.Action => False)
      (by
        intro a h
        exact False.elim h)
      trivial
  simpa [g5dSystem] using hTrace

theorem e15_g5d_ag_causeable_coverage_fails :
    ¬ GRBS.E14AGContractComparison.AGCauseableCoverage
      g5dAssumption
      g5dSystem
      g5dCauseable := by
  intro hCoverage
  have hCause : g5dCauseable false true := by
    constructor <;> rfl
  have hTrace :=
    hCoverage
      false
      true
      hCause
      (fun _ : GRBS.AGBypass.Action => False)
      (by
        intro a h
        exact False.elim h)
      trivial
  simpa [g5dSystem] using hTrace

theorem e15_g5d_obligations_without_observation_correspondence_do_not_imply_ag :
    ∃
      (D State : Type)
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System State g5dChannel)
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep ∧
      ContractDomainComplete causeable dep represents ∧
      ContractRepresentationSound covered represents mediated ∧
      ¬ MediatedAGObservationCorrespondence A s mediated ∧
      ¬ GRBS.E14AGContractComparison.AGCauseableCoverage A s causeable := by
  exact ⟨
    g5dDependency,
    g5dTrace,
    g5dAssumption,
    g5dSystem,
    g5dCauseable,
    g5dDep,
    g5dCovered,
    g5dRepresents,
    g5dMediated,
    e15_g5d_contract_coverage,
    e15_g5d_domain_completeness,
    e15_g5d_representation_soundness,
    e15_g5d_observation_correspondence_fails,
    e15_g5d_ag_causeable_coverage_fails⟩


structure E15DeletionMinimalityWitnesses : Prop where
  without_contract_coverage :
    ∃
      (D State : Type)
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System State g5aChannel)
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      ContractDomainComplete causeable dep represents ∧
      ContractRepresentationSound covered represents mediated ∧
      MediatedAGObservationCorrespondence A s mediated ∧
      ¬ R8RichContractSeparation.R8e.ContractCoverage covered dep ∧
      ¬ GRBS.E14AGContractComparison.AGCauseableCoverage A s causeable
  without_domain_completeness :
    ∃
      (D State : Type)
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System State g5bChannel)
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep ∧
      ContractRepresentationSound covered represents mediated ∧
      MediatedAGObservationCorrespondence A s mediated ∧
      ¬ ContractDomainComplete causeable dep represents ∧
      ¬ GRBS.E14AGContractComparison.AGCauseableCoverage A s causeable
  without_representation_soundness :
    ∃
      (D State : Type)
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System State g5cChannel)
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep ∧
      ContractDomainComplete causeable dep represents ∧
      MediatedAGObservationCorrespondence A s mediated ∧
      ¬ ContractRepresentationSound covered represents mediated ∧
      ¬ GRBS.E14AGContractComparison.AGCauseableCoverage A s causeable
  without_observation_correspondence :
    ∃
      (D State : Type)
      (A : GRBS.AGBypass.AGAssumption)
      (s : GRBS.AGBypass.System State g5dChannel)
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep ∧
      ContractDomainComplete causeable dep represents ∧
      ContractRepresentationSound covered represents mediated ∧
      ¬ MediatedAGObservationCorrespondence A s mediated ∧
      ¬ GRBS.E14AGContractComparison.AGCauseableCoverage A s causeable

theorem e15_g5_deletion_minimality :
    E15DeletionMinimalityWitnesses := by
  exact
    { without_contract_coverage :=
        e15_g5a_obligations_without_contract_coverage_do_not_imply_ag
      without_domain_completeness :=
        e15_g5b_e15_obligations_do_not_imply_ag_causeable_coverage
      without_representation_soundness :=
        e15_g5c_obligations_without_representation_soundness_do_not_imply_ag
      without_observation_correspondence :=
        e15_g5d_obligations_without_observation_correspondence_do_not_imply_ag }

namespace E15CausalCoverageContractEquivalence

/-
E15-G6:
Test whether the four-obligation assurance-transfer structure contains
a deeper causal-domain correspondence.

Observation correspondence is deliberately excluded from the composite
condition. It remains an AG-facing semantic obligation.
-/

def CausalAssuranceCorrespondence
    {State D : Type}
    (causeable :
      GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
    (dep : D → Prop)
    (covered : D → Prop)
    (represents : D → State → State → Prop)
    (mediated : State → State → Prop) : Prop :=
  ∀ s0 s1,
    causeable s0 s1 →
    ∃ d,
      dep d ∧
      covered d ∧
      represents d s0 s1 ∧
      mediated s0 s1

theorem e15_g6a_contract_obligations_imply_causal_assurance_correspondence :
    ∀
      {State D : Type}
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep →
      ContractDomainComplete causeable dep represents →
      ContractRepresentationSound covered represents mediated →
      CausalAssuranceCorrespondence
        causeable dep covered represents mediated := by
  intro State D causeable dep covered represents mediated
  intro hCoverage hComplete hSound
  intro s0 s1 hCause
  obtain ⟨d, hDep, hRepresents⟩ :=
    hComplete s0 s1 hCause
  have hCovered : covered d :=
    hCoverage d hDep
  have hMediated : mediated s0 s1 :=
    hSound d hCovered s0 s1 hRepresents
  exact ⟨d, hDep, hCovered, hRepresents, hMediated⟩

/-
E15-G6B1:
Causal-assurance correspondence implies domain completeness.
-/

theorem e15_g6b1_causal_assurance_correspondence_implies_domain_completeness :
    ∀
      {State D : Type}
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      CausalAssuranceCorrespondence
        causeable dep covered represents mediated →
      ContractDomainComplete causeable dep represents := by
  intro State D causeable dep covered represents mediated
  intro hCorrespondence s0 s1 hCause
  obtain ⟨d, hDep, hCovered, hRepresents, hMediated⟩ :=
    hCorrespondence s0 s1 hCause
  exact ⟨d, hDep, hRepresents⟩

/-
E15-G6B2:
Causal-assurance correspondence does not imply global contract coverage.
-/

def g6b2State : Type := Bool
def g6b2Dependency : Type := Bool

def g6b2Causeable :
    GRBS.E13CausalSemanticCorrespondence.CauseableTransition g6b2State :=
  fun s0 s1 => s0 = false ∧ s1 = true

def g6b2Dep : g6b2Dependency → Prop :=
  fun _ => True

def g6b2Covered : g6b2Dependency → Prop :=
  fun d => d = false

def g6b2Represents :
    g6b2Dependency → g6b2State → g6b2State → Prop :=
  fun d s0 s1 =>
    d = false ∧ s0 = false ∧ s1 = true

def g6b2Mediated : g6b2State → g6b2State → Prop :=
  fun s0 s1 => s0 = false ∧ s1 = true

theorem e15_g6b2_causal_assurance_correspondence_holds :
    CausalAssuranceCorrespondence
      g6b2Causeable
      g6b2Dep
      g6b2Covered
      g6b2Represents
      g6b2Mediated := by
  intro s0 s1 hCause
  rcases hCause with ⟨hs0, hs1⟩
  refine ⟨false, ?_, ?_, ?_, ?_⟩
  · trivial
  · rfl
  · exact ⟨rfl, hs0, hs1⟩
  · exact ⟨hs0, hs1⟩

theorem e15_g6b2_contract_coverage_fails :
    ¬ R8RichContractSeparation.R8e.ContractCoverage
        g6b2Covered g6b2Dep := by
  intro hCoverage
  have hCovered : g6b2Covered true :=
    hCoverage true trivial
  exact Bool.noConfusion hCovered

theorem e15_g6b2_causal_assurance_does_not_imply_contract_coverage :
    CausalAssuranceCorrespondence
        g6b2Causeable
        g6b2Dep
        g6b2Covered
        g6b2Represents
        g6b2Mediated ∧
    ¬ R8RichContractSeparation.R8e.ContractCoverage
        g6b2Covered g6b2Dep := by
  exact
    ⟨e15_g6b2_causal_assurance_correspondence_holds,
     e15_g6b2_contract_coverage_fails⟩

/-
E15-G6C:
Test whether causal-assurance correspondence plus contract coverage
and representation-domain closure is sufficient for representation soundness.
-/

def RepresentationDomainClosure
    {State D : Type}
    (causeable :
      GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
    (covered : D → Prop)
    (represents : D → State → State → Prop) : Prop :=
  ∀ d,
    covered d →
    ∀ s0 s1,
      represents d s0 s1 →
      causeable s0 s1

/-
E15-G6B3:
Causal-assurance correspondence does not imply global representation
soundness.
-/

def g6b3State : Type := Bool
def g6b3Dependency : Type := Bool

def g6b3Causeable :
    GRBS.E13CausalSemanticCorrespondence.CauseableTransition g6b3State :=
  fun s0 s1 => s0 = false ∧ s1 = true

def g6b3Dep : g6b3Dependency → Prop :=
  fun _ => True

def g6b3Covered : g6b3Dependency → Prop :=
  fun _ => True

def g6b3Represents :
    g6b3Dependency → g6b3State → g6b3State → Prop :=
  fun d s0 s1 =>
    (d = false ∧ s0 = false ∧ s1 = true) ∨
    (d = true ∧ s0 = false ∧ s1 = false)

def g6b3Mediated : g6b3State → g6b3State → Prop :=
  fun s0 s1 => s0 = false ∧ s1 = true

theorem e15_g6b3_causal_assurance_correspondence_holds :
    CausalAssuranceCorrespondence
      g6b3Causeable
      g6b3Dep
      g6b3Covered
      g6b3Represents
      g6b3Mediated := by
  intro s0 s1 hCause
  rcases hCause with ⟨hs0, hs1⟩
  refine ⟨false, ?_, ?_, ?_, ?_⟩
  · trivial
  · trivial
  · exact Or.inl ⟨rfl, hs0, hs1⟩
  · exact ⟨hs0, hs1⟩

theorem e15_g6b3_representation_soundness_fails :
    ¬ ContractRepresentationSound
        g6b3Covered
        g6b3Represents
        g6b3Mediated := by
  intro hSound
  have hMediated : g6b3Mediated false false :=
    hSound true trivial false false (Or.inr ⟨rfl, rfl, rfl⟩)
  exact Bool.noConfusion hMediated.2

theorem e15_g6b3_causal_assurance_does_not_imply_representation_soundness :
    CausalAssuranceCorrespondence
        g6b3Causeable
        g6b3Dep
        g6b3Covered
        g6b3Represents
        g6b3Mediated ∧
    ¬ ContractRepresentationSound
        g6b3Covered
        g6b3Represents
        g6b3Mediated := by
  exact
    ⟨e15_g6b3_causal_assurance_correspondence_holds,
     e15_g6b3_representation_soundness_fails⟩

/-
E15-G6D:
Causal-assurance correspondence is equivalent to mediated causal coverage
once the declared dependency domain is complete for actual causeable
transitions.

The forward direction extracts mediated causal coverage from the witness
carried by causal-assurance correspondence.

The reverse direction uses domain completeness to obtain a dependency
representation witness for each causeable transition, then uses mediated
causal coverage to discharge the final mediated conjunct.

Thus CAC is a representation-witness refinement of causal coverage rather
than an independent causal-safety property.
-/

theorem e15_g6d_causal_assurance_implies_mediated_causal_coverage :
    ∀
      {State D : Type}
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      CausalAssuranceCorrespondence
        causeable dep covered represents mediated →
      GRBS.E13CausalSemanticCorrespondence.MediatedCausalCoverage
        causeable mediated := by
  intro State D causeable dep covered represents mediated
  intro hCorrespondence s0 s1 hCause
  obtain ⟨d, hDep, hCovered, hRepresents, hMediated⟩ :=
    hCorrespondence s0 s1 hCause
  exact hMediated

theorem e15_g6d_domain_complete_plus_mediated_causal_coverage_implies_causal_assurance :
    ∀
      {State D : Type}
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep →
      ContractDomainComplete causeable dep represents →
      GRBS.E13CausalSemanticCorrespondence.MediatedCausalCoverage
        causeable mediated →
      CausalAssuranceCorrespondence
        causeable dep covered represents mediated := by
  intro State D causeable dep covered represents mediated
  intro hCoverage hComplete hCausalCoverage
  intro s0 s1 hCause
  obtain ⟨d, hDep, hRepresents⟩ :=
    hComplete s0 s1 hCause
  have hCovered : covered d :=
    hCoverage d hDep
  have hMediated : mediated s0 s1 :=
    hCausalCoverage s0 s1 hCause
  exact ⟨d, hDep, hCovered, hRepresents, hMediated⟩

theorem e15_g6d_under_domain_completeness_cac_iff_mediated_causal_coverage :
    ∀
      {State D : Type}
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (dep : D → Prop)
      (covered : D → Prop)
      (represents : D → State → State → Prop)
      (mediated : State → State → Prop),
      R8RichContractSeparation.R8e.ContractCoverage covered dep →
      ContractDomainComplete causeable dep represents →
      (CausalAssuranceCorrespondence
          causeable dep covered represents mediated ↔
        GRBS.E13CausalSemanticCorrespondence.MediatedCausalCoverage
          causeable mediated) := by
  intro State D causeable dep covered represents mediated
  intro hCoverage hComplete
  constructor
  · exact
      e15_g6d_causal_assurance_implies_mediated_causal_coverage
        causeable dep covered represents mediated
  · intro hCausalCoverage
    exact
      e15_g6d_domain_complete_plus_mediated_causal_coverage_implies_causal_assurance
        causeable dep covered represents mediated
        hCoverage
        hComplete
        hCausalCoverage

/-
E15-G6E:
E13 representation completeness and complete mediation construct the
E15 causal-assurance witness, provided the represented access domain is
covered by the contract.

The witness is the access channel supplied by E13
EffectRepresentationComplete. E13 RepresentationCompleteMediation then
establishes the corresponding mediated transition.
-/

theorem e15_g6e_e13_representation_obligations_plus_contract_coverage_imply_causal_assurance :
    ∀
      {Access State : Type}
      (causeable :
        GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (represents :
        GRBS.E13CausalSemanticCorrespondence.Represents Access State)
      (mediated :
        GRBS.E13CausalSemanticCorrespondence.AccessMediated Access State)
      (covered : Access → Prop),
      R8RichContractSeparation.R8e.ContractCoverage
        covered
        (fun _ : Access => True) →
      GRBS.E13CausalSemanticCorrespondence.EffectRepresentationComplete
        causeable represents →
      GRBS.E13CausalSemanticCorrespondence.RepresentationCompleteMediation
        represents mediated →
      CausalAssuranceCorrespondence
        causeable
        (fun _ : Access => True)
        covered
        represents
        (GRBS.E13CausalSemanticCorrespondence.AccessMediatedTransition
          represents mediated) := by
  intro Access State causeable represents mediated covered
  intro hCoverage hRepresentation hComplete
  intro s0 s1 hCause
  obtain ⟨a, hRepresents⟩ :=
    hRepresentation s0 s1 hCause
  have hCovered : covered a :=
    hCoverage a trivial
  have hAccessMediated : mediated a s0 s1 :=
    hComplete a s0 s1 hRepresents
  have hMediated :
      GRBS.E13CausalSemanticCorrespondence.AccessMediatedTransition
        represents mediated s0 s1 := by
    exact ⟨a, hRepresents, hAccessMediated⟩
  exact ⟨a, trivial, hCovered, hRepresents, hMediated⟩

/-
E15-G6F:
Specialize the G6 causal-assurance correspondence to the E13
step/authorization representation.

This makes explicit that the E13 causal witness can be enriched with
the E15 contract witness without changing the underlying mediated
causal transition.
-/

theorem e15_g6f_e13_specialization_constructs_causal_assurance :
    ∀
      {State Action : Type}
      (causeable : GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (step : State → Action → State → Prop)
      (authorized : State → Action → State → Prop)
      (covered : Action → Prop),
      R8RichContractSeparation.R8e.ContractCoverage
        covered
        (fun _ : Action => True) →
      GRBS.E13CausalSemanticCorrespondence.EffectRepresentationComplete
        causeable
        (fun a s0 s1 => step s0 a s1) →
      GRBS.E13CausalSemanticCorrespondence.RepresentationCompleteMediation
        (fun a s0 s1 => step s0 a s1)
        (fun a s0 s1 => authorized s0 a s1) →
      CausalAssuranceCorrespondence
        causeable
        (fun _ : Action => True)
        covered
        (fun a s0 s1 => step s0 a s1)
        (fun s0 s1 =>
          ∃ a,
            step s0 a s1 ∧
              authorized s0 a s1) := by
  intro State Action causeable step authorized covered
  intro hCoverage hRepresentation hComplete
  intro s0 s1 hCause
  obtain ⟨a, hStep⟩ :=
    hRepresentation s0 s1 hCause
  have hCovered : covered a :=
    hCoverage a trivial
  have hAuthorized : authorized s0 a s1 :=
    hComplete a s0 s1 hStep
  have hMediated :
      (∃ a,
        step s0 a s1 ∧
          authorized s0 a s1) := by
    exact ⟨a, hStep, hAuthorized⟩
  exact ⟨a, trivial, hCovered, hStep, hMediated⟩

/-
E15-G6G:
The E13-specialized causal-assurance correspondence recovers the exact
E13 mediated causal coverage relation.

This is a specialization of G6-D, not a converse to E13's
representation-level complete-mediation condition.
-/

theorem e15_g6g_e13_specialized_causal_assurance_implies_e13_causal_coverage :
    ∀
      {State Action : Type}
      (causeable : GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (step : State → Action → State → Prop)
      (authorized : State → Action → State → Prop)
      (covered : Action → Prop),
      CausalAssuranceCorrespondence
        causeable
        (fun _ : Action => True)
        covered
        (fun a s0 s1 => step s0 a s1)
        (fun s0 s1 =>
          ∃ a,
            step s0 a s1 ∧
              authorized s0 a s1) →
      GRBS.E13CausalSemanticCorrespondence.MediatedCausalCoverage
        causeable
        (fun s0 s1 =>
          ∃ a,
            step s0 a s1 ∧
              authorized s0 a s1) := by
  intro State Action causeable step authorized covered
  intro hCAC
  exact
    e15_g6d_causal_assurance_implies_mediated_causal_coverage
      causeable
      (fun _ : Action => True)
      covered
      (fun a s0 s1 => step s0 a s1)
      (fun s0 s1 =>
        ∃ a,
          step s0 a s1 ∧
            authorized s0 a s1)
      hCAC

/-
E15-G6H:
Under the E13 representation obligations and E15 contract coverage,
the E15 causal-assurance correspondence is equivalent to the exact
E13 mediated causal-coverage relation.

The reverse direction uses E13 representation completeness and complete
mediation to construct CAC through G6-F. The theorem therefore does not
claim that causal coverage alone reconstructs the representation-level
E13 obligations.
-/

theorem e15_g6h_e13_e15_causal_coverage_round_trip :
    ∀
      {State Action : Type}
      (causeable : GRBS.E13CausalSemanticCorrespondence.CauseableTransition State)
      (step : State → Action → State → Prop)
      (authorized : State → Action → State → Prop)
      (covered : Action → Prop),
      R8RichContractSeparation.R8e.ContractCoverage
        covered
        (fun _ : Action => True) →
      GRBS.E13CausalSemanticCorrespondence.EffectRepresentationComplete
        causeable
        (fun a s0 s1 => step s0 a s1) →
      GRBS.E13CausalSemanticCorrespondence.RepresentationCompleteMediation
        (fun a s0 s1 => step s0 a s1)
        (fun a s0 s1 => authorized s0 a s1) →
      (CausalAssuranceCorrespondence
          causeable
          (fun _ : Action => True)
          covered
          (fun a s0 s1 => step s0 a s1)
          (fun s0 s1 =>
            ∃ a,
              step s0 a s1 ∧
                authorized s0 a s1) ↔
        GRBS.E13CausalSemanticCorrespondence.MediatedCausalCoverage
          causeable
          (fun s0 s1 =>
            ∃ a,
              step s0 a s1 ∧
                authorized s0 a s1)) := by
  intro State Action causeable step authorized covered
  intro hCoverage hRepresentation hComplete
  constructor
  · intro hCAC
    exact
      e15_g6g_e13_specialized_causal_assurance_implies_e13_causal_coverage
        causeable step authorized covered hCAC
  · intro hCausalCoverage
    exact
      e15_g6f_e13_specialization_constructs_causal_assurance
        causeable step authorized covered
        hCoverage
        hRepresentation
        hComplete

end E15CausalCoverageContractEquivalence
end E15CausalCoverageContractEquivalence
end GRBS
