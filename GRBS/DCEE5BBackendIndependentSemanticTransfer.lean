import DARMCoreCalculus

namespace GRBS.DCEE5BBackendIndependentSemanticTransfer

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge
open GRBS.DARMCoreCalculus

/-!
DCEE-5B: Backend-Independent Semantic Transfer

This experiment strengthens Level D of DCEE-5A.

The purpose is not to show that arbitrary assurance-production mechanisms
are interchangeable.  Instead, it demonstrates a narrower factorization:

  backend-specific artifact
        ↓
  backend-specific assurance production
        ↓
  common SourceAssured interface
        ↓
  common first-class transfer object
        ↓
  common transfer judgment

Two distinct assurance backends are modeled:

  1. a proof backend, whose artifact carries a proof obligation;
  2. a contract backend, whose artifact carries an assumption/guarantee pair.

The transfer judgment does not inspect either artifact type.
It consumes only the normalized source/target/dependency/coverage/discharge
representation.

The result is therefore a structural witness for backend-independent transfer,
not a claim that proof and contract semantics are themselves equivalent.
-/

/-- A proof-produced assurance artifact. -/
structure ProofArtifact (D : Type) where
  source : D → Prop
  property : D → Prop
  proof : ∀ d, source d → property d

/-- A contract-produced assurance artifact. -/
structure ContractArtifact (D : Type) where
  assumption : D → Prop
  guarantee : D → Prop
  valid : ∀ d, assumption d → guarantee d

/-- Normalize a proof artifact into the common source-assurance interface. -/
def ProofProducesAssurance
    {D : Type}
    (a : ProofArtifact D) : Prop :=
  SourceAssured D a.source a.property

/-- Normalize a contract artifact into the common source-assurance interface. -/
def ContractProducesAssurance
    {D : Type}
    (a : ContractArtifact D) : Prop :=
  SourceAssured D a.assumption a.guarantee

/-- A common transfer object shared by both production backends. -/
structure SharedTransfer (D : Type) where
  source : D → Prop
  target : D → Prop
  dependency : D → Prop
  covered : D → Prop
  discharged : D → Prop

/-- Validity of the backend-neutral transfer object. -/
def SharedTransferValid
    {D : Type}
    (t : SharedTransfer D) : Prop :=
  (∀ d, t.target d → t.dependency d) ∧
  (∀ d, t.target d → t.covered d) ∧
  (∀ d, t.target d → t.discharged d)

/--
Backend-independent transfer depends only on the normalized transfer object.
The backend artifact does not occur in this definition.
-/
def BackendNeutralTransfer
    {D : Type}
    (t : SharedTransfer D) : Prop :=
  SharedTransferValid t

/--
Proof and contract artifacts can be normalized into the same abstract
source-assurance interface when their source/property predicates agree.
-/
theorem proof_and_contract_normalize_to_same_assurance
    {D : Type}
    (p : ProofArtifact D)
    (c : ContractArtifact D)
    (hSource : ∀ d, p.source d ↔ c.assumption d)
    (hProperty : ∀ d, p.property d ↔ c.guarantee d) :
    ProofProducesAssurance p ↔ ContractProducesAssurance c := by
  constructor
  · intro hp
    intro d hd
    have hpSource : p.source d := (hSource d).mpr hd
    have hpProperty : p.property d := hp d hpSource
    exact (hProperty d).mp hpProperty
  · intro hc
    intro d hd
    have hcAssumption : c.assumption d := (hSource d).mp hd
    have hcGuarantee : c.guarantee d := hc d hcAssumption
    exact (hProperty d).mpr hcGuarantee

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

def proofArtifact : ProofArtifact D where
  source := source
  property := property
  proof := by
    intro d hd
    trivial

def contractArtifact : ContractArtifact D where
  assumption := source
  guarantee := property
  valid := by
    intro d hd
    trivial

theorem proof_backend_produces_assurance :
    ProofProducesAssurance proofArtifact := by
  intro d hd
  trivial

theorem contract_backend_produces_assurance :
    ContractProducesAssurance contractArtifact := by
  intro d hd
  trivial

theorem backend_normalization_agrees :
    ProofProducesAssurance proofArtifact ↔
    ContractProducesAssurance contractArtifact := by
  apply proof_and_contract_normalize_to_same_assurance
  · intro d
    rfl
  · intro d
    rfl

/--
One transfer object is shared by both assurance-production backends.
-/
def sharedTransfer : SharedTransfer D where
  source := source
  target := target
  dependency := fun _ => True
  covered := fun _ => True
  discharged := property

theorem shared_transfer_valid :
    BackendNeutralTransfer sharedTransfer := by
  constructor
  · intro d hd
    trivial
  · constructor
    · intro d hd
      trivial
    · intro d hd
      trivial

/--
The transfer judgment itself contains no proof-backend-specific information.
-/
theorem proof_backend_reuses_shared_transfer :
    ProofProducesAssurance proofArtifact ∧
    BackendNeutralTransfer sharedTransfer := by
  constructor
  · exact proof_backend_produces_assurance
  · exact shared_transfer_valid

/--
The transfer judgment itself contains no contract-backend-specific information.
-/
theorem contract_backend_reuses_shared_transfer :
    ContractProducesAssurance contractArtifact ∧
    BackendNeutralTransfer sharedTransfer := by
  constructor
  · exact contract_backend_produces_assurance
  · exact shared_transfer_valid

/--
The same transfer judgment is reached from both production backends.
-/
theorem backend_independent_transfer_witness :
    (ProofProducesAssurance proofArtifact ∧
      BackendNeutralTransfer sharedTransfer) ∧
    (ContractProducesAssurance contractArtifact ∧
      BackendNeutralTransfer sharedTransfer) := by
  constructor
  · exact proof_backend_reuses_shared_transfer
  · exact contract_backend_reuses_shared_transfer

/--
DCEE-5B conclusion:

the transfer object can be shared even though the assurance artifacts
and their production predicates are represented by different structures.
-/
theorem transfer_is_independent_of_artifact_type :
    BackendNeutralTransfer sharedTransfer := by
  exact shared_transfer_valid

end GRBS.DCEE5BBackendIndependentSemanticTransfer

namespace GRBS.DCEE5BBackendIndependentSemanticTransfer.NontrivialSemanticWitness

inductive D
  | d1
  | d2
  | d3

def proofSource : D → Prop
  | D.d1 => True
  | D.d2 => True
  | D.d3 => False

def proofProperty : D → Prop
  | D.d1 => True
  | D.d2 => True
  | D.d3 => False

def contractAssumption : D → Prop
  | D.d1 => True
  | D.d2 => True
  | D.d3 => False

def contractGuarantee : D → Prop
  | D.d1 => True
  | D.d2 => True
  | D.d3 => False

def proofArtifact : ProofArtifact D where
  source := proofSource
  property := proofProperty
  proof := by
    intro d hd
    exact hd

def contractArtifact : ContractArtifact D where
  assumption := contractAssumption
  guarantee := contractGuarantee
  valid := by
    intro d hd
    exact hd

theorem proof_backend_is_assured :
    ProofProducesAssurance proofArtifact := by
  intro d hd
  exact hd

theorem contract_backend_is_assured :
    ContractProducesAssurance contractArtifact := by
  intro d hd
  exact hd

theorem source_representations_are_equivalent :
    ∀ d, proofSource d ↔ contractAssumption d := by
  intro d
  cases d <;> simp [proofSource, contractAssumption]

theorem property_representations_are_equivalent :
    ∀ d, proofProperty d ↔ contractGuarantee d := by
  intro d
  cases d <;> simp [proofProperty, contractGuarantee]

theorem nontrivial_backend_normalization :
    ProofProducesAssurance proofArtifact ↔
    ContractProducesAssurance contractArtifact := by
  apply proof_and_contract_normalize_to_same_assurance
  · exact source_representations_are_equivalent
  · exact property_representations_are_equivalent

def sharedTransfer : SharedTransfer D where
  source := proofSource
  target := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => True
    | D.d3 => False
  dependency := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => True
    | D.d3 => False
  covered := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => True
    | D.d3 => False
  discharged := proofProperty

theorem normalized_transfer_is_valid :
    BackendNeutralTransfer sharedTransfer := by
  constructor
  · intro d hd
    exact hd
  · constructor
    · intro d hd
      exact hd
    · intro d hd
      exact hd

theorem proof_and_contract_share_backend_neutral_transfer :
    (ProofProducesAssurance proofArtifact ∧
      BackendNeutralTransfer sharedTransfer) ∧
    (ContractProducesAssurance contractArtifact ∧
      BackendNeutralTransfer sharedTransfer) := by
  constructor
  · constructor
    · exact proof_backend_is_assured
    · exact normalized_transfer_is_valid
  · constructor
    · exact contract_backend_is_assured
    · exact normalized_transfer_is_valid

theorem transfer_does_not_inspect_backend_representation :
    BackendNeutralTransfer sharedTransfer := by
  exact normalized_transfer_is_valid

end GRBS.DCEE5BBackendIndependentSemanticTransfer.NontrivialSemanticWitness
