import DARMCoreCalculus

namespace GRBS.DCEE2SACMTransfer

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge

/-- Minimal SACM-style claim representation for the comparison experiment. -/
structure SACMClaim where
  proposition : Prop

/-- Minimal SACM-style context representation. -/
structure SACMContext where
  proposition : Prop

/-- Minimal SACM-style evidence representation. -/
structure SACMEvidence where
  proposition : Prop

/-- Minimal assurance-case relation: context and evidence support a claim. -/
structure SACMAssuranceCase where
  claim : SACMClaim
  context : SACMContext
  evidence : SACMEvidence
  supported :
    context.proposition →
    evidence.proposition →
    claim.proposition

/-- A scope-change candidate for comparison with DARM. -/
structure ScopeChange (D : Type) where
  source : D → Prop
  target : D → Prop
  property : D → Prop

end GRBS.DCEE2SACMTransfer

namespace GRBS.DCEE2SACMTransfer.Level2ACounterexample

inductive D
  | d1
  | d2

inductive G
  | g

inductive S
  | s

inductive B
  | b

inductive L
  | l

/-- Concrete GRBS frame:
    d1 is covered; d2 is structurally relevant but uncovered. -/
def F : GRBS.Frame where
  Trace := Unit
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := Unit
  Safe := fun _ _ => True
  dep := fun _ _ d =>
    match d with
    | D.d1 => True
    | D.d2 => True
  cov := fun _ _ _ d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def scopeChange :
    GRBS.DCEE2SACMTransfer.ScopeChange (GRBS.Frame.Dependency F) where
  source := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  target := fun _ => True
  property := fun _ => True

def sacmClaim : SACMClaim where
  proposition :=
    ∀ d, scopeChange.source d → scopeChange.property d

def sacmContext : SACMContext where
  proposition := True

def sacmEvidence : SACMEvidence where
  proposition := True

def assuranceCase : SACMAssuranceCase where
  claim := sacmClaim
  context := sacmContext
  evidence := sacmEvidence
  supported := by
    intro hcontext hevidence
    intro d hd
    trivial

theorem assurance_case_valid :
    assuranceCase.claim.proposition := by
  exact assuranceCase.supported trivial trivial

theorem target_dependency_is_introduced :
    GRBS.R5AssuranceConservation.Delta
      (GRBS.Frame.Dependency F)
      scopeChange.source
      scopeChange.target
      D.d2 := by
  constructor
  · trivial
  · intro h
    cases h

theorem target_dependency_is_uncovered :
    ¬ GRBS.Frame.cov F B.b L.l S.s D.d2 := by
  simp [F]

end GRBS.DCEE2SACMTransfer.Level2ACounterexample

namespace GRBS.DCEE2SACMTransfer.Level2BDependencyAware

open GRBS

/-- A stronger SACM-style assurance case in which the claim explicitly
    identifies the dependencies on which it is conditioned. -/
structure DependencyAwareClaim (D : Type) where
  proposition : D → Prop
  dependency : D → Prop

structure DependencyAwareCase (D : Type) where
  claim : DependencyAwareClaim D
  context : Prop
  evidence : Prop
  supported :
    context →
    evidence →
    (∀ d, claim.dependency d → claim.proposition d)

/-- Explicit refinement of the dependency set. -/
def DependencySetRefines
    {D : Type}
    (source target : D → Prop) : Prop :=
  ∀ d, target d → source d

inductive D
  | d1
  | d2

def source : D → Prop
  | D.d1 => True
  | D.d2 => False

def target : D → Prop
  | D.d1 => True
  | D.d2 => True

def property : D → Prop := fun _ => True

def dependencyAwareClaim : DependencyAwareClaim D where
  proposition := property
  dependency := target

def dependencyAwareCase : DependencyAwareCase D where
  claim := dependencyAwareClaim
  context := True
  evidence := True
  supported := by
    intro hcontext hevidence d hd
    trivial

theorem dependency_aware_case_valid :
    ∀ d, dependencyAwareCase.claim.dependency d →
      dependencyAwareCase.claim.proposition d := by
  exact dependencyAwareCase.supported trivial trivial

theorem dependency_set_refinement_fails :
    ¬ DependencySetRefines source target := by
  intro h
  have hd2 : target D.d2 := by
    trivial
  have hs2 : source D.d2 := h D.d2 hd2
  cases hs2

theorem dependency_aware_refinement_rejects_expansion :
    ¬ DependencySetRefines source target := by
  exact dependency_set_refinement_fails

end GRBS.DCEE2SACMTransfer.Level2BDependencyAware


namespace GRBS.DCEE2SACMTransfer.Level2CCoverageAware

open GRBS

/-- A richer assurance-case representation that explicitly records
    dependencies, boundary coverage, and semantic discharge. -/
structure CoverageAwareCase (D : Type) where
  claim : D → Prop
  dependency : D → Prop
  covered : D → Prop
  discharged : D → Prop

/-- Transfer validity in the enriched assurance-case representation. -/
def TransferValid
    {D : Type}
    (target : D → Prop)
    (caseTarget : CoverageAwareCase D) : Prop :=
  (∀ d, target d → caseTarget.claim d) ∧
  (∀ d, target d → caseTarget.dependency d) ∧
  (∀ d, target d → caseTarget.covered d) ∧
  (∀ d, target d → caseTarget.discharged d)

inductive D
  | d1
  | d2

inductive G
  | g

inductive S
  | s

inductive B
  | b

inductive L
  | l

def F : GRBS.Frame where
  Trace := Unit
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := Unit
  Safe := fun _ _ => True
  dep := fun _ _ d =>
    match d with
    | D.d1 => True
    | D.d2 => True
  cov := fun _ _ _ d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def source : D → Prop
  | D.d1 => True
  | D.d2 => False

def target : D → Prop
  | D.d1 => True
  | D.d2 => True

def property : D → Prop := fun _ => True

/-- The enriched case deliberately records the actual boundary failure:
    d2 is a target dependency but is not covered. -/
def targetCase : CoverageAwareCase D where
  claim := property
  dependency := target
  covered := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  discharged := property

theorem target_case_dependency_is_explicit :
    ∀ d, targetCase.dependency d → target d := by
  intro d hd
  exact hd

theorem target_case_coverage_fails :
    ¬ (∀ d, target d → targetCase.covered d) := by
  intro h
  have hcovered : targetCase.covered D.d2 := h D.d2 trivial
  exact hcovered

theorem enriched_case_rejects_transfer :
    ¬ TransferValid target targetCase := by
  intro h
  exact target_case_coverage_fails h.2.2.1

theorem darm_rejects_same_witness :
    ¬ GRBS F G.g S.s B.b L.l := by
  intro h
  have hc : GRBS.Frame.cov F B.b L.l S.s D.d2 :=
    h D.d2 trivial
  exact hc

theorem both_reject_for_same_coverage_failure :
    (¬ TransferValid target targetCase) ∧
    (¬ GRBS F G.g S.s B.b L.l) := by
  constructor
  · exact enriched_case_rejects_transfer
  · exact darm_rejects_same_witness

end GRBS.DCEE2SACMTransfer.Level2CCoverageAware


namespace GRBS.DCEE2SACMTransfer.Level2DPositiveCorrespondence

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge
open GRBS.DARMCoreCalculus

inductive D
  | d1
  | d2

inductive G
  | g

inductive S
  | s

inductive B
  | b

inductive L
  | l

def F : GRBS.Frame where
  Trace := Unit
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := Unit
  Safe := fun _ _ => True
  dep := fun _ _ _ => True
  cov := fun _ _ _ _ => True
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def source : D → Prop
  | D.d1 => True
  | D.d2 => False

def target : D → Prop
  | D.d1 => True
  | D.d2 => True

def property : D → Prop := fun _ => True

def candidate : TransferCandidate F.Dependency where
  source := source
  target := target
  property := property

def targetCase :
    GRBS.DCEE2SACMTransfer.Level2CCoverageAware.CoverageAwareCase D where
  claim := property
  dependency := target
  covered := fun _ => True
  discharged := property

theorem enriched_case_transfer_holds :
    GRBS.DCEE2SACMTransfer.Level2CCoverageAware.TransferValid
      target targetCase := by
  constructor
  · intro d hd
    trivial
  · constructor
    · intro d hd
      exact hd
    · constructor
      · intro d hd
        trivial
      · intro d hd
        trivial

theorem darm_grbs_holds :
    GRBS F G.g S.s B.b L.l := by
  intro d hd
  trivial

theorem darm_delta_is_represented :
    DeltaSubsetDependency F G.g S.s source target := by
  intro d hd
  trivial

theorem darm_delta_is_discharged :
    CoveredDischargesProperty F G.g S.s B.b L.l property := by
  intro d hd hcov
  trivial

theorem darm_transfer_holds :
    DARMTransferAdmissible F G.g S.s B.b L.l candidate := by
  constructor
  · exact darm_delta_is_represented
  · constructor
    · exact darm_grbs_holds
    · exact darm_delta_is_discharged

theorem positive_correspondence_witness :
    GRBS.DCEE2SACMTransfer.Level2CCoverageAware.TransferValid
        target targetCase ∧
    DARMTransferAdmissible F G.g S.s B.b L.l candidate := by
  constructor
  · exact enriched_case_transfer_holds
  · exact darm_transfer_holds

end GRBS.DCEE2SACMTransfer.Level2DPositiveCorrespondence
