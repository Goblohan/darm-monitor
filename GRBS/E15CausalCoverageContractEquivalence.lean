import GRBS
import GRBS.R8RichContractSeparation
import GRBS.E13CausalSemanticCorrespondence

namespace GRBS
namespace E15CausalCoverageContractEquivalence

open R8RichContractSeparation
open E13CausalSemanticCorrespondence

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

end E15CausalCoverageContractEquivalence
end GRBS
