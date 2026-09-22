import GRBS.R20DARMToSemanticCorrespondence
import GRBS.R19bSemanticDependencyBridge

namespace GRBS.R20R19bAdapter

open GRBS
open GRBS.R20DARMToSemanticCorrespondence
open GRBS.R19bSemanticDependencyBridge

/--
Explicit representation map from an R20 semantic dependency to an R19b
semantic dependency.
-/
def R20ToR19b
    {D : Type}
    {S : SemanticSystem} :
    R20DARMToSemanticCorrespondence.SemanticDependency D S.State →
      R19bSemanticDependencyBridge.SemanticDependency D S.State :=
  fun sd =>
    R19bSemanticDependencyBridge.SemanticDependency.mk
      sd.dependency
      sd.source
      sd.target

/--
R20 target guarantees are sufficient for the R19b preservation predicate
only when that predicate is invariant under the explicit representation
correspondence.
-/
def R20R19bStateCorrespondence
    {D : Type}
    {S : SemanticSystem}
    (realize : SemanticRealization D S) : Prop :=
  ∀ d
    (sd : R19bSemanticDependencyBridge.SemanticDependency D S.State),
    sd.dependency = d →
    (realize d).source = sd.source ∧
    (realize d).target = sd.target

def PropertyCorrespondence
    {D : Type}
    {S : SemanticSystem}
    (G : SemanticGuarantee S)
    (preservesR19b :
      R19bSemanticDependencyBridge.SemanticDependency D S.State → Prop)
    (realize : SemanticRealization D S) : Prop :=
  ∀ d
    (sd : R20DARMToSemanticCorrespondence.SemanticDependency D S.State),
    sd.dependency = d →
    G.property (realize d).target →
    preservesR19b (R20ToR19b sd)

def PreservationRepresentationInvariant
    {D : Type}
    {S : SemanticSystem}
    (preservesR19b :
      R19bSemanticDependencyBridge.SemanticDependency D S.State → Prop) : Prop :=
  ∀
    (r20 : R20DARMToSemanticCorrespondence.SemanticDependency D S.State)
    (r19b : R19bSemanticDependencyBridge.SemanticDependency D S.State),
    r19b.dependency = r20.dependency →
    r19b.source = r20.source →
    r19b.target = r20.target →
    (preservesR19b r19b ↔ preservesR19b (R20ToR19b r20))

/--
An R20 target guarantee transports to R19b semantic preservation when
the two semantic-dependency representations are explicitly related.
-/
theorem r20_target_guarantee_transports_to_r19b
    {D : Type}
    {S : SemanticSystem}
    (G : SemanticGuarantee S)
    (realize : SemanticRealization D S)
    (relevantR19b :
      R19bSemanticDependencyBridge.SemanticDependency D S.State → Prop)
    (preservesR19b :
      R19bSemanticDependencyBridge.SemanticDependency D S.State → Prop)
    (delta : D → Prop)
    (hFaithful : R20DARMToSemanticCorrespondence.RealizationFaithful realize)
    (hStateCorrespondence : R20R19bStateCorrespondence realize)
    (hR20Target :
      ∀ d, delta d → G.property (realize d).target)
    (hPropertyCorrespondence :
      PropertyCorrespondence
        G preservesR19b realize)
    (hRepresentationInvariant :
      PreservationRepresentationInvariant preservesR19b)
    (hR19bCoverage :
      ∀ sd,
        relevantR19b sd →
        delta sd.dependency) :
    SemanticPreservation relevantR19b preservesR19b := by
  intro sd hRelevant
  have hDelta : delta sd.dependency :=
    hR19bCoverage sd hRelevant
  have hTarget :
      G.property (realize sd.dependency).target :=
    hR20Target sd.dependency hDelta
  have hMappedPreserves :
      preservesR19b (R20ToR19b (realize sd.dependency)) :=
    hPropertyCorrespondence
      sd.dependency
      (realize sd.dependency)
      (hFaithful sd.dependency)
      hTarget
  have hRepresentation :
      preservesR19b (R20ToR19b (realize sd.dependency)) :=
    hMappedPreserves
  have hSource :
      sd.source = (realize sd.dependency).source :=
    (hStateCorrespondence
      sd.dependency
      sd
      rfl).1.symm
  have hTargetState :
      sd.target = (realize sd.dependency).target :=
    (hStateCorrespondence
      sd.dependency
      sd
      rfl).2.symm
  have hDependency :
      sd.dependency = (realize sd.dependency).dependency :=
    (hFaithful sd.dependency).symm
  exact
    (hRepresentationInvariant
      (realize sd.dependency)
      sd
      hDependency
      hSource
      hTargetState).mpr hRepresentation

end GRBS.R20R19bAdapter

#print axioms GRBS.R20R19bAdapter.r20_target_guarantee_transports_to_r19b
