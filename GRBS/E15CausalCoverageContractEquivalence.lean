import GRBS
import GRBS.R8RichContractSeparation
import GRBS.E13CausalSemanticCorrespondence
import GRBS.E14AGContractComparison

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
