import GRBS
import R5AssuranceConservation
import R6GRBSDeltaBridge

namespace GRBS
namespace R16AssuranceRepresentationInterop

/-
R16: Assurance Representation Interoperability

Purpose:
  Separate the representation/backend that establishes source assurance
  from the DARM transfer conditions required to move that assurance across
  a boundary.

The backend produces a normalized SourceAssured proposition.
DARM then reasons about transfer independently of how that assurance
was originally established.
-/

structure ProofCertificate (D : Type) where
  source : D → Prop
  property : D → Prop
  proof : GRBS.R5AssuranceConservation.SourceAssured D source property

structure ContractCertificate (D : Type) where
  assumption : D → Prop
  guarantee : D → Prop
  contract_valid : ∀ d, assumption d → guarantee d

theorem contract_certificate_to_assurance
    {D : Type}
    (c : ContractCertificate D)
    (source property : D → Prop)
    (hSource : ∀ d, source d ↔ c.assumption d)
    (hProperty : ∀ d, c.guarantee d ↔ property d) :
    GRBS.R5AssuranceConservation.SourceAssured D source property := by
  intro d hd
  have hAssumption : c.assumption d := (hSource d).mp hd
  have hGuarantee : c.guarantee d := c.contract_valid d hAssumption
  exact (hProperty d).mp hGuarantee

theorem proof_certificate_to_assurance
    {D : Type}
    (c : ProofCertificate D) :
    GRBS.R5AssuranceConservation.SourceAssured D c.source c.property :=
  c.proof

def TransferAdmissible
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop) : Prop :=
  GRBS F g s b l ∧
  GRBS.R6GRBSDeltaBridge.DeltaSubsetDependency F g s source target ∧
  GRBS.R6GRBSDeltaBridge.CoveredDischargesProperty F g s b l property

theorem normalized_assurance_transfer
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop)
    (hSource : GRBS.R5AssuranceConservation.SourceAssured F.Dependency source property)
    (hTransfer :
      TransferAdmissible F g s b l source target property) :
    GRBS.R5AssuranceConservation.TargetAssured F.Dependency target property := by
  rcases hTransfer with ⟨hGRBS, hDeltaDep, hCovered⟩
  have hDelta :
      GRBS.R5AssuranceConservation.DeltaObligation F.Dependency source target property :=
    GRBS.R6GRBSDeltaBridge.grbs_implies_delta_obligation
      F g s b l source target property
      hGRBS hDeltaDep hCovered
  exact GRBS.R5AssuranceConservation.conserving_transfer_preserves_assurance
    F.Dependency source target property
    hSource hDelta

theorem contract_certificate_transfer
    {D : Type}
    (c : ContractCertificate D)
    (source property : D → Prop)
    (hSource : ∀ d, source d ↔ c.assumption d)
    (hProperty : ∀ d, c.guarantee d ↔ property d) :
    GRBS.R5AssuranceConservation.SourceAssured D source property :=
  contract_certificate_to_assurance c source property hSource hProperty

/-
Representation equivalence.

This is deliberately proposition-level. It does not claim that two
backend artifacts are operationally identical. It states only that
their normalized assurance propositions are logically equivalent.
-/

def NormalizationEquivalent
    (assuranceA assuranceB : Prop) : Prop :=
  assuranceA ↔ assuranceB

theorem equivalent_representation_transfer
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (source target property : F.Dependency → Prop)
    (assuranceA assuranceB : Prop)
    (hEquivalent : NormalizationEquivalent assuranceA assuranceB)
    (hA : assuranceA)
    (hBImpliesSource : assuranceB → GRBS.R5AssuranceConservation.SourceAssured F.Dependency source property)
    (hTransfer :
      TransferAdmissible F g s b l source target property) :
    GRBS.R5AssuranceConservation.TargetAssured F.Dependency target property := by
  have hB : assuranceB := hEquivalent.mp hA
  have hSource : GRBS.R5AssuranceConservation.SourceAssured F.Dependency source property :=
    hBImpliesSource hB
  exact normalized_assurance_transfer
    F g s b l source target property hSource hTransfer

end R16AssuranceRepresentationInterop
end GRBS
