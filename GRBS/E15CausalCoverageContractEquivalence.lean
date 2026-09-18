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

end E15CausalCoverageContractEquivalence
end GRBS
