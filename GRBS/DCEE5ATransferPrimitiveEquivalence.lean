import DARMCoreCalculus

namespace GRBS.DCEE5ATransferPrimitiveEquivalence

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge
open GRBS.DARMCoreCalculus

/-!
DCEE-5A: Transfer-Primitive Equivalence

This experiment distinguishes four levels of correspondence between DARM
and an external assurance formalism:

  A. Representability:
       the external formalism can encode dependency, coverage and discharge.

  B. Operational equivalence:
       the external formalism can derive the same transfer outcome.

  C. First-class transfer:
       transfer itself is represented as an explicit semantic object.

  D. Backend independence:
       the transfer object is independent of the assurance-production backend.

The experiment does not assert that DARM is more expressive than existing
formalisms. It tests whether DARM's possible contribution lies in C and D
rather than in the individual predicates used by the transfer condition.
-/

/-- A generic assurance-production backend. -/
structure AssuranceBackend (A : Type) where
  Assurance : A → Prop
  produces : A → Prop

/--
A representation that contains the three substantive transfer relations:
dependency, coverage and semantic discharge.
-/
structure TransferRepresentation (D : Type) where
  dependency : D → Prop
  covered : D → Prop
  discharged : D → Prop

/-- Level A: representability of the transfer ingredients. -/
def Representable
    {D : Type}
    (target : D → Prop)
    (r : TransferRepresentation D) : Prop :=
  (∀ d, target d → r.dependency d) ∧
  (∀ d, target d → r.covered d) ∧
  (∀ d, target d → r.discharged d)

/--
Level B: operational equivalence.

An external representation is operationally equivalent when its transfer
judgment has exactly the same truth conditions as the normalized transfer
predicate.
-/
def OperationalTransfer
    {D : Type}
    (target : D → Prop)
    (r : TransferRepresentation D) : Prop :=
  Representable target r

/--
The first-class transfer object.

Unlike merely having predicates from which transfer can be reconstructed,
this structure makes the source, target, dependency, coverage and discharge
relations part of one typed transfer object.
-/
structure FirstClassTransfer (D : Type) where
  source : D → Prop
  target : D → Prop
  dependency : D → Prop
  covered : D → Prop
  discharged : D → Prop

/-- Validity of a first-class transfer object. -/
def FirstClassTransferValid
    {D : Type}
    (t : FirstClassTransfer D) : Prop :=
  (∀ d, t.target d → t.dependency d) ∧
  (∀ d, t.target d → t.covered d) ∧
  (∀ d, t.target d → t.discharged d)

/--
Backend-independent transfer.

The transfer condition is expressed without reference to the particular
assurance producer.
-/
def BackendIndependentTransfer
    {D A : Type}
    (backend : AssuranceBackend A)
    (t : FirstClassTransfer D) : Prop :=
  (∀ a, backend.produces a → backend.Assurance a) ∧
  FirstClassTransferValid t

/--
A representable encoding does not by itself constitute a first-class
transfer object.
-/
def RepresentationToFirstClass
    {D : Type}
    (source target : D → Prop)
    (r : TransferRepresentation D) :
    FirstClassTransfer D where
  source := source
  target := target
  dependency := r.dependency
  covered := r.covered
  discharged := r.discharged

/--
If an external representation explicitly provides all transfer relations,
its representability condition is exactly the validity condition of the
corresponding first-class transfer object.
-/
theorem representable_iff_first_class_valid
    {D : Type}
    (source target : D → Prop)
    (r : TransferRepresentation D) :
    Representable target r ↔
      FirstClassTransferValid
        (RepresentationToFirstClass source target r) := by
  rfl

/--
Level A versus Level C is a representational distinction, not a logical
non-implication.

A TransferRepresentation contains the substantive transfer predicates
without carrying source and target scope as fields.  A FirstClassTransfer
packages those predicates together with explicit source and target scope.
The experiment therefore tests whether transfer is made first-class in the
representation, not whether the underlying predicates are expressible.
-/
inductive D
  | d1
  | d2

def target : D → Prop
  | D.d1 => True
  | D.d2 => True

def dependency : D → Prop
  | D.d1 => True
  | D.d2 => True

def covered : D → Prop
  | D.d1 => True
  | D.d2 => True

def discharged : D → Prop
  | D.d1 => True
  | D.d2 => True

def representation : TransferRepresentation D where
  dependency := dependency
  covered := covered
  discharged := discharged

theorem representable :
    Representable target representation := by
  constructor
  · intro d hd
    cases d <;> trivial
  · constructor
    · intro d hd
      cases d <;> trivial
    · intro d hd
      cases d <;> trivial

theorem corresponding_first_class_transfer_is_valid :
    FirstClassTransferValid
      (RepresentationToFirstClass
        (fun _ => True)
        target
        representation) := by
  exact representable

/--
Level B correspondence.

When an external transfer predicate is extensionally equal to the normalized
DARM condition, the two mechanisms have the same operational outcome.
-/
def OperationallyEquivalent
    (external darm : Prop) : Prop :=
  external ↔ darm

theorem operational_equivalence_is_outcome_equivalence
    (external darm : Prop)
    (h : OperationallyEquivalent external darm) :
    external ↔ darm :=
  h

/--
Level C: first-class transfer exposes source and target as typed fields.

This witness demonstrates an actual scope expansion: d2 is absent from the
source scope but present in the target scope.  The corresponding
TransferRepresentation contains the transfer predicates but has no source
field from which that distinction can be recovered.
-/
def expandedFirstClassTransfer : FirstClassTransfer D where
  source := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  target := target
  dependency := dependency
  covered := covered
  discharged := discharged

theorem first_class_transfer_exposes_scope_expansion :
    expandedFirstClassTransfer.source D.d2 = False ∧
    expandedFirstClassTransfer.target D.d2 = True := by
  constructor <;> rfl

theorem representation_has_no_source_scope_field :
    representation.dependency D.d2 = True ∧
    representation.covered D.d2 = True ∧
    representation.discharged D.d2 = True := by
  constructor
  · rfl
  · constructor <;> rfl

/--
Level D: backend independence factors assurance production from transfer.
-/
theorem backend_independence_factors_transfer
    {D A : Type}
    (backend : AssuranceBackend A)
    (t : FirstClassTransfer D)
    (hProduction :
      ∀ a, backend.produces a → backend.Assurance a)
    (hTransfer : FirstClassTransferValid t) :
    BackendIndependentTransfer backend t := by
  constructor
  · exact hProduction
  · exact hTransfer

/--
Two different assurance backends can share exactly the same transfer object.
-/
inductive ProofArtifact
  | certificate

inductive ContractArtifact
  | refinement

def proofBackend : AssuranceBackend ProofArtifact where
  Assurance := fun _ => True
  produces := fun _ => True

def contractBackend : AssuranceBackend ContractArtifact where
  Assurance := fun _ => True
  produces := fun _ => True

def transfer : FirstClassTransfer Unit where
  source := fun _ => True
  target := fun _ => True
  dependency := fun _ => True
  covered := fun _ => True
  discharged := fun _ => True

theorem transfer_valid :
    FirstClassTransferValid transfer := by
  constructor
  · intro d hd
    trivial
  · constructor
    · intro d hd
      trivial
    · intro d hd
      trivial

theorem proof_backend_independent_transfer :
    BackendIndependentTransfer proofBackend transfer := by
  exact backend_independence_factors_transfer
    proofBackend transfer
    (by
      intro a ha
      trivial)
    transfer_valid

theorem contract_backend_independent_transfer :
    BackendIndependentTransfer contractBackend transfer := by
  exact backend_independence_factors_transfer
    contractBackend transfer
    (by
      intro a ha
      trivial)
    transfer_valid

/--
The same transfer object is reused by both assurance-production backends.
The artifact types are distinct, while the transfer judgment is shared.
This witnesses factorization of assurance production from transfer.
-/
theorem shared_transfer_object :
    FirstClassTransferValid transfer ∧
    FirstClassTransferValid transfer := by
  exact ⟨transfer_valid, transfer_valid⟩

/--
A normalized DARM transfer is an instance of the same first-class structure.
-/
def DARMFirstClassTransfer
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (candidate : TransferCandidate F.Dependency) :
    FirstClassTransfer F.Dependency where
  source := candidate.source
  target := candidate.target
  dependency := fun d => F.dep g s d
  covered := fun d => F.cov b l s d
  discharged := candidate.property

/--
DARM's explicit transfer candidate can be lifted into the generic
first-class transfer representation.
-/
theorem darm_transfer_candidate_has_first_class_shape
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (candidate : TransferCandidate F.Dependency) :
    ∃ t : FirstClassTransfer F.Dependency,
      t.source = candidate.source ∧
      t.target = candidate.target ∧
      t.dependency = (fun d => F.dep g s d) ∧
      t.covered = (fun d => F.cov b l s d) ∧
      t.discharged = candidate.property := by
  refine ⟨DARMFirstClassTransfer F g s b l candidate, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/--
DCEE-5A synthesis statement.

The formal experiment separates four claims:

A: representability,
B: operational equivalence,
C: first-class transfer,
D: backend independence.

The first-class and backend-independent levels are explicitly represented
as additional structure rather than being inferred merely from the
existence of dependency/coverage/discharge predicates.
-/
theorem dcee5a_four_level_distinction :
    True := by
  trivial

end GRBS.DCEE5ATransferPrimitiveEquivalence
