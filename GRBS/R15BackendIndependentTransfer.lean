import GRBS
import R5AssuranceConservation
import R6GRBSDeltaBridge

open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge

namespace GRBS.R15BackendIndependentTransfer

/--
A backend-neutral assurance interface.

DARM consumes the resulting source assurance rather than depending
on the internal mechanism used to establish it.
-/
def BackendAssurance
    {D : Type}
    (source property : D → Prop) : Prop :=
  SourceAssured D source property

/--
A proof-oriented assurance backend.
-/
def ProofBackend
    {D : Type}
    (source property : D → Prop) : Prop :=
  SourceAssured D source property

/--
A contract-oriented assurance backend.
-/
def ContractBackend
    {D : Type}
    (source property : D → Prop) : Prop :=
  SourceAssured D source property

/--
A proof backend result can be presented through the backend-neutral
assurance interface.
-/
theorem proof_backend_produces_assurance
    {D : Type}
    (source property : D → Prop)
    (hProof : ProofBackend source property) :
    BackendAssurance source property :=
  hProof

/--
A contract backend result can be presented through the backend-neutral
assurance interface.
-/
theorem contract_backend_produces_assurance
    {D : Type}
    (source property : D → Prop)
    (hContract : ContractBackend source property) :
    BackendAssurance source property :=
  hContract

/--
DARM transfer conditions are independent of the assurance-generation
mechanism.
-/
def TransferAdmissible
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop) : Prop :=
  GRBS F g s b l ∧
  DeltaSubsetDependency F g s source target ∧
  CoveredDischargesProperty F g s b l property

/--
Once an assurance backend has produced the backend-neutral source
assurance, DARM applies the same transfer rule.
-/
theorem backend_independent_transfer
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop)
    (hBackend :
      BackendAssurance source property)
    (hTransfer :
      TransferAdmissible F g s b l source target property) :
    TargetAssured F.Dependency target property := by
  rcases hTransfer with ⟨hGRBS, hDeltaDep, hCovered⟩
  have hDelta :
      DeltaObligation F.Dependency source target property :=
    grbs_implies_delta_obligation
      F g s b l source target property
      hGRBS hDeltaDep hCovered
  exact target_assured_of_source_and_delta
    F.Dependency source target property hBackend hDelta

/--
Proof-generated assurance and contract-generated assurance have the
same DARM transfer consequence after entering the common assurance
interface.
-/
theorem proof_backend_transfer
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop)
    (hProof : ProofBackend source property)
    (hTransfer :
      TransferAdmissible F g s b l source target property) :
    TargetAssured F.Dependency target property := by
  apply backend_independent_transfer
    F g s b l source target property
    (proof_backend_produces_assurance source property hProof)
  exact hTransfer

theorem contract_backend_transfer
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop)
    (hContract : ContractBackend source property)
    (hTransfer :
      TransferAdmissible F g s b l source target property) :
    TargetAssured F.Dependency target property := by
  apply backend_independent_transfer
    F g s b l source target property
    (contract_backend_produces_assurance source property hContract)
  exact hTransfer

end GRBS.R15BackendIndependentTransfer

namespace GRBS.R15BackendIndependentTransfer.R15Negative

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

def F : Frame where
  Trace := Unit
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := Unit
  Safe := fun _ _ => True
  dep := fun _ _ d => d = D.d1 ∨ d = D.d2
  cov := fun _ _ _ d => d = D.d1
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def g : F.Guarantee := G.g
def s : F.System := S.s
def b : F.Boundary := B.b
def l : F.Locus := L.l

def source : F.Dependency → Prop :=
  fun d => d = D.d1

def target : F.Dependency → Prop :=
  fun d => d = D.d1 ∨ d = D.d2

def property : F.Dependency → Prop :=
  fun _ => True

theorem proof_backend_holds :
    ProofBackend source property := by
  intro d hd
  trivial

theorem contract_backend_holds :
    ContractBackend source property := by
  intro d hd
  trivial

theorem target_dependency_is_uncovered :
    ∃ d, F.dep G.g S.s d ∧ ¬ F.cov B.b L.l S.s d := by
  refine ⟨D.d2, ?_, ?_⟩
  · exact Or.inr rfl
  · intro h
    cases h

theorem grbs_fails :
    ¬ GRBS F G.g S.s B.b L.l := by
  intro h
  have hd : F.dep G.g S.s D.d2 := by
    exact Or.inr rfl
  have hc := h D.d2 hd
  cases hc

theorem transfer_admissibility_fails :
    ¬ TransferAdmissible
      F G.g S.s B.b L.l source target property := by
  intro h
  exact grbs_fails h.1

theorem proof_assurance_survives_but_transfer_fails :
    ProofBackend source property ∧
    ¬ TransferAdmissible
      F G.g S.s B.b L.l source target property := by
  exact ⟨proof_backend_holds, transfer_admissibility_fails⟩

theorem contract_assurance_survives_but_transfer_fails :
    ContractBackend source property ∧
    ¬ TransferAdmissible
      F G.g S.s B.b L.l source target property := by
  exact ⟨contract_backend_holds, transfer_admissibility_fails⟩

end GRBS.R15BackendIndependentTransfer.R15Negative
