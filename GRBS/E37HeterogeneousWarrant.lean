/-
  E37: HETEROGENEOUS WARRANTED CLAIM TRANSFER

  PURPOSE

  E35 studies whether a concrete representation retains the distinctions
  required by a property.

  E36 studies finite chains of representation transitions over a common
  observation type and localizes the first lossy transition.

  E37 asks a different question:

      when source and target live in DIFFERENT representation domains,
      when is a downstream claim actually warranted?

  The central distinction is between:

    1. loss:
         a source claim is explicitly warranted for transfer, but does not
         hold at the target;

    2. unsupported introduction:
         a target claim is asserted even though it has neither inherited
         warrant from the source nor an explicit local warrant generated
         at the boundary.

  This module deliberately does NOT claim that heterogeneous assurance
  domains are semantically identical.
-/

import E36CompositionalAdequacy
import DARMCoreCalculus

namespace DARM.E37

structure Boundary (S T : Type) where
  source : S → Prop
  target : T → Prop
  sourceClaim : S → Prop
  targetClaim : T → Prop
  relates : S → T → Prop
  transferWarrant : S → T → Prop
  localWarrant : T → Prop

def InheritedWarrant
    {S T : Type}
    (b : Boundary S T)
    (t : T) : Prop :=
  ∃ s,
    b.source s ∧
    b.sourceClaim s ∧
    b.relates s t ∧
    b.transferWarrant s t

def Entitled
    {S T : Type}
    (b : Boundary S T)
    (t : T) : Prop :=
  InheritedWarrant b t ∨ b.localWarrant t

def TransferSound
    {S T : Type}
    (b : Boundary S T) : Prop :=
  ∀ s t,
    b.source s →
    b.sourceClaim s →
    b.relates s t →
    b.transferWarrant s t →
    b.target t →
    b.targetClaim t

def LocalWarrantSound
    {S T : Type}
    (b : Boundary S T) : Prop :=
  ∀ t,
    b.target t →
    b.localWarrant t →
    b.targetClaim t

def NoUnsupportedIntroduction
    {S T : Type}
    (b : Boundary S T) : Prop :=
  ∀ t,
    b.target t →
    b.targetClaim t →
    Entitled b t

def Valid
    {S T : Type}
    (b : Boundary S T) : Prop :=
  TransferSound b ∧
  LocalWarrantSound b ∧
  NoUnsupportedIntroduction b

theorem target_claim_iff_entitled
    {S T : Type}
    {b : Boundary S T}
    (hValid : Valid b)
    {t : T}
    (hTarget : b.target t) :
    b.targetClaim t ↔ Entitled b t := by
  constructor
  · intro hClaim
    exact hValid.2.2 t hTarget hClaim
  · intro hEntitled
    rcases hEntitled with hInherited | hLocal
    · rcases hInherited with
        ⟨s, hSource, hSourceClaim, hRelates, hWarrant⟩
      exact hValid.1
        s t
        hSource hSourceClaim hRelates hWarrant hTarget
    · exact hValid.2.1 t hTarget hLocal

structure LossWitness
    {S T : Type}
    (b : Boundary S T) where
  sourceValue : S
  targetValue : T
  sourceInScope : b.source sourceValue
  sourceClaimHolds : b.sourceClaim sourceValue
  related : b.relates sourceValue targetValue
  warrant : b.transferWarrant sourceValue targetValue
  targetInScope : b.target targetValue
  targetClaimFails : ¬ b.targetClaim targetValue

theorem lossWitness_breaks_transferSound
    {S T : Type}
    {b : Boundary S T}
    (w : LossWitness b) :
    ¬ TransferSound b := by
  intro h
  exact w.targetClaimFails
    (h
      w.sourceValue
      w.targetValue
      w.sourceInScope
      w.sourceClaimHolds
      w.related
      w.warrant
      w.targetInScope)

structure UnsupportedIntroductionWitness
    {S T : Type}
    (b : Boundary S T) where
  targetValue : T
  targetInScope : b.target targetValue
  targetClaimAsserted : b.targetClaim targetValue
  notEntitled : ¬ Entitled b targetValue

theorem unsupportedIntroduction_breaks_condition
    {S T : Type}
    {b : Boundary S T}
    (w : UnsupportedIntroductionWitness b) :
    ¬ NoUnsupportedIntroduction b := by
  intro h
  exact w.notEntitled
    (h w.targetValue w.targetInScope w.targetClaimAsserted)

def MiddleCompatible
    {S T U : Type}
    (b₁ : Boundary S T)
    (b₂ : Boundary T U) : Prop :=
  (∀ t, b₁.target t → b₂.source t) ∧
  (∀ t, b₁.targetClaim t → b₂.sourceClaim t)

theorem two_boundary_transfer_sound
    {S T U : Type}
    (b₁ : Boundary S T)
    (b₂ : Boundary T U)
    (h₁ : TransferSound b₁)
    (h₂ : TransferSound b₂)
    (hCompatible : MiddleCompatible b₁ b₂)
    {s : S} {t : T} {u : U}
    (hSource : b₁.source s)
    (hSourceClaim : b₁.sourceClaim s)
    (hRel₁ : b₁.relates s t)
    (hWarrant₁ : b₁.transferWarrant s t)
    (hTarget₁ : b₁.target t)
    (hRel₂ : b₂.relates t u)
    (hWarrant₂ : b₂.transferWarrant t u)
    (hTarget₂ : b₂.target u) :
    b₂.targetClaim u := by
  have hMiddleClaim :
      b₁.targetClaim t :=
    h₁ s t
      hSource hSourceClaim
      hRel₁ hWarrant₁ hTarget₁

  have hMiddleSource :
      b₂.source t :=
    hCompatible.1 t hTarget₁

  have hMiddleSourceClaim :
      b₂.sourceClaim t :=
    hCompatible.2 t hMiddleClaim

  exact h₂ t u
    hMiddleSource hMiddleSourceClaim
    hRel₂ hWarrant₂ hTarget₂

def BoundaryLossAt
    {S T : Type}
    (b : Boundary S T)
    (s : S)
    (t : T) : Prop :=
  b.source s ∧
  b.sourceClaim s ∧
  b.relates s t ∧
  b.transferWarrant s t ∧
  b.target t ∧
  ¬ b.targetClaim t

theorem terminal_failure_localizes
    {S T U : Type}
    (b₁ : Boundary S T)
    (b₂ : Boundary T U)
    (hCompatible : MiddleCompatible b₁ b₂)
    {s : S} {t : T} {u : U}
    (hSource : b₁.source s)
    (hSourceClaim : b₁.sourceClaim s)
    (hRel₁ : b₁.relates s t)
    (hWarrant₁ : b₁.transferWarrant s t)
    (hTarget₁ : b₁.target t)
    (hRel₂ : b₂.relates t u)
    (hWarrant₂ : b₂.transferWarrant t u)
    (hTarget₂ : b₂.target u)
    (hTerminalFailure : ¬ b₂.targetClaim u) :
    BoundaryLossAt b₁ s t ∨
    BoundaryLossAt b₂ t u := by
  by_cases hMiddleClaim : b₁.targetClaim t
  · right
    exact ⟨
      hCompatible.1 t hTarget₁,
      hCompatible.2 t hMiddleClaim,
      hRel₂,
      hWarrant₂,
      hTarget₂,
      hTerminalFailure
    ⟩
  · left
    exact ⟨
      hSource,
      hSourceClaim,
      hRel₁,
      hWarrant₁,
      hTarget₁,
      hMiddleClaim
    ⟩

open GRBS.R5AssuranceConservation

def fromR5
    {X : Type}
    (source target property : X → Prop) :
    Boundary X X where
  source := source
  target := target
  sourceClaim := property
  targetClaim := property
  relates := fun s t => s = t
  transferWarrant := fun _ _ => True
  localWarrant := fun t =>
    Delta X source target t ∧ property t

theorem r5_assurance_yields_valid_boundary
    {X : Type}
    (source target property : X → Prop)
    (hSource : SourceAssured X source property)
    (hDelta : DeltaObligation X source target property) :
    Valid (fromR5 source target property) := by
  constructor
  · intro s t hs hProperty hEq _hWarrant ht
    subst t
    exact hProperty
  · constructor
    · intro t ht hLocal
      exact hLocal.2
    · intro t ht hProperty
      by_cases hs : source t
      · left
        refine ⟨t, hs, ?_, rfl, trivial⟩
        exact hSource t hs
      · right
        exact ⟨
          ⟨ht, hs⟩,
          hDelta t ⟨ht, hs⟩
        ⟩


/-!
## Evidence-backed local warrant

`localWarrant` by itself is only an assertion made at the boundary.

E37 must not silently treat that assertion as its own justification.
A stronger transfer therefore exposes an independent evidence carrier
and requires every local warrant to have a corresponding admissible
evidence item.

This does NOT prove that the evidence model corresponds to physical
reality. That remains a separate adequacy/refinement obligation.
-/

/--
An evidence basis is intentionally external to `Boundary`.

`admissible` says which evidence artifacts are accepted by this evidence
model.

`supports` states which target objects an admissible evidence artifact
is relevant to.
-/
structure EvidenceBasis (T E : Type) where
  admissible : E → Prop
  supports : E → T → Prop

/--
Every locally asserted warrant must have an explicit evidence witness.
-/
def LocalWarrantGrounded
    {S T E : Type}
    (b : Boundary S T)
    (evidence : EvidenceBasis T E) : Prop :=
  ∀ t,
    b.localWarrant t →
    ∃ e,
      evidence.admissible e ∧
      evidence.supports e t

/--
The evidence interpretation must actually establish the target claim
for in-scope targets.

This separates:

    evidence exists

from:

    the evidence is sufficient for this claim.
-/
def EvidenceSupportsClaim
    {S T E : Type}
    (b : Boundary S T)
    (evidence : EvidenceBasis T E) : Prop :=
  ∀ e t,
    evidence.admissible e →
    evidence.supports e t →
    b.target t →
    b.targetClaim t

/--
Evidence-backed validity strengthens `Valid`.

The local-warrant branch now requires:

  local warrant
      ->
  explicit admissible evidence
      ->
  evidence supports target
      ->
  target claim
-/
def EvidenceBackedValid
    {S T E : Type}
    (b : Boundary S T)
    (evidence : EvidenceBasis T E) : Prop :=
  TransferSound b ∧
  LocalWarrantGrounded b evidence ∧
  EvidenceSupportsClaim b evidence ∧
  NoUnsupportedIntroduction b

/--
Evidence-backed validity is sufficient for the earlier E37 validity
judgment.

Crucially, `LocalWarrantSound` is now DERIVED from evidence grounding
and evidence soundness rather than merely asserted independently.
-/
theorem evidence_backed_valid_implies_valid
    {S T E : Type}
    {b : Boundary S T}
    {evidence : EvidenceBasis T E}
    (h : EvidenceBackedValid b evidence) :
    Valid b := by
  rcases h with
    ⟨hTransfer, hGrounded, hEvidenceSound, hNoUnsupported⟩

  refine ⟨hTransfer, ?_, hNoUnsupported⟩

  intro t hTarget hLocal
  rcases hGrounded t hLocal with
    ⟨e, hAdmissible, hSupports⟩

  exact hEvidenceSound
    e t
    hAdmissible
    hSupports
    hTarget


/-!
## Empirical adequacy boundary

Evidence-backed validity is still internal to the formal evidence model.

An `EvidenceBasis` may truthfully say:

    evidence e is admissible
    evidence e supports target t

while the interpretation connecting that evidence to the external world
is wrong.

E37 therefore exposes a further boundary between:

    evidence semantics

and:

    world semantics.

This boundary is not eliminated by the calculus. It must be explicitly
discharged by empirical calibration, validated test procedures, trusted
measurement, certification, or another appropriate external anchor.
-/

/--
An external-world interpretation.

`targetPresent` identifies the target object in a world state.

`evidenceObserved` records that an evidence artifact was actually produced
or observed in that world.

`worldClaim` is the property that really holds of the target in that world.

E37 does not define physical reality. It makes the relation to it explicit.
-/
structure EmpiricalSemantics (T E W : Type) where
  targetPresent : W → T → Prop
  evidenceObserved : W → E → Prop
  worldClaim : W → T → Prop

/--
The evidence interpretation is empirically adequate when every admissible
piece of evidence that claims to support a present target actually implies
the corresponding world property.
-/
def EvidenceSemanticsAdequate
    {T E W : Type}
    (evidence : EvidenceBasis T E)
    (world : EmpiricalSemantics T E W) : Prop :=
  ∀ w e t,
    world.evidenceObserved w e →
    evidence.admissible e →
    evidence.supports e t →
    world.targetPresent w t →
    world.worldClaim w t

/--
Grounding in an abstract evidence basis is not enough.

For a particular world state, every local warrant must be realized by an
evidence artifact that is actually observed in that world.
-/
def LocalWarrantEmpiricallyRealized
    {S T E W : Type}
    (b : Boundary S T)
    (evidence : EvidenceBasis T E)
    (world : EmpiricalSemantics T E W)
    (w : W) : Prop :=
  ∀ t,
    b.localWarrant t →
    ∃ e,
      evidence.admissible e ∧
      evidence.supports e t ∧
      world.evidenceObserved w e

/--
An empirically anchored E37 judgment requires three distinct layers:

  1. internal evidence-backed validity;
  2. actual realization of the evidence in the world;
  3. adequacy of the evidence semantics for that world model.
-/
def EmpiricallyAnchoredValid
    {S T E W : Type}
    (b : Boundary S T)
    (evidence : EvidenceBasis T E)
    (world : EmpiricalSemantics T E W)
    (w : W) : Prop :=
  EvidenceBackedValid b evidence ∧
  LocalWarrantEmpiricallyRealized b evidence world w ∧
  EvidenceSemanticsAdequate evidence world

/--
Once all three layers are explicit, a local warrant can establish the
external world claim.

The result does not manufacture empirical adequacy. It consumes it.
-/
theorem empirically_anchored_local_claim
    {S T E W : Type}
    {b : Boundary S T}
    {evidence : EvidenceBasis T E}
    {world : EmpiricalSemantics T E W}
    {w : W}
    (h : EmpiricallyAnchoredValid b evidence world w)
    {t : T}
    (hLocal : b.localWarrant t)
    (hPresent : world.targetPresent w t) :
    world.worldClaim w t := by
  rcases h with
    ⟨_hEvidenceBacked, hRealized, hAdequate⟩

  rcases hRealized t hLocal with
    ⟨e, hAdmissible, hSupports, hObserved⟩

  exact hAdequate
    w e t
    hObserved
    hAdmissible
    hSupports
    hPresent

namespace IntegrityUpgrade

inductive SourceRep where
  | untrusted

inductive TargetRep where
  | assertedTrusted

def attemptedUpgrade : Boundary SourceRep TargetRep where
  source := fun _ => True
  target := fun _ => True
  sourceClaim := fun _ => True
  targetClaim := fun _ => True
  relates := fun _ _ => True
  transferWarrant := fun _ _ => False
  localWarrant := fun _ => False

def upgrade_is_unsupported :
    UnsupportedIntroductionWitness attemptedUpgrade := by
  refine {
    targetValue := TargetRep.assertedTrusted
    targetInScope := ?_
    targetClaimAsserted := ?_
    notEntitled := ?_
  }
  · trivial
  · trivial
  · intro h
    rcases h with hInherited | hLocal
    · rcases hInherited with
        ⟨s, _hSource, _hClaim, _hRel, hWarrant⟩
      exact hWarrant.elim
    · exact hLocal.elim

end IntegrityUpgrade

namespace AuthorityExpansion

inductive Token where
  | readOnly

inductive Action where
  | write

def attemptedExpansion : Boundary Token Action where
  source := fun _ => True
  target := fun _ => True
  sourceClaim := fun _ => True
  targetClaim := fun _ => True
  relates := fun _ _ => True
  transferWarrant := fun _ _ => False
  localWarrant := fun _ => False

def write_authority_is_unsupported :
    UnsupportedIntroductionWitness attemptedExpansion := by
  refine {
    targetValue := Action.write
    targetInScope := ?_
    targetClaimAsserted := ?_
    notEntitled := ?_
  }
  · trivial
  · trivial
  · intro h
    rcases h with hInherited | hLocal
    · rcases hInherited with
        ⟨s, _hSource, _hClaim, _hRel, hWarrant⟩
      exact hWarrant.elim
    · exact hLocal.elim

end AuthorityExpansion

namespace ContractRefinement

inductive AbstractSpec where
  | safeSpec

inductive ConcreteImpl where
  | refinedImpl

def refinementBoundary :
    Boundary AbstractSpec ConcreteImpl where
  source := fun _ => True
  target := fun _ => True
  sourceClaim := fun _ => True
  targetClaim := fun _ => True
  relates := fun _ _ => True
  transferWarrant := fun _ _ => True
  localWarrant := fun _ => False

theorem refinement_boundary_valid :
    Valid refinementBoundary := by
  constructor
  · intro s t hs hClaim hRel hWarrant ht
    trivial
  · constructor
    · intro t ht hLocal
      exact hLocal.elim
    · intro t ht hClaim
      left
      refine ⟨AbstractSpec.safeSpec, ?_, ?_, ?_, ?_⟩
      · trivial
      · trivial
      · trivial
      · trivial

theorem refined_claim_is_entitled :
    Entitled refinementBoundary ConcreteImpl.refinedImpl := by
  exact
    (refinement_boundary_valid.2.2
      ConcreteImpl.refinedImpl
      trivial
      trivial)

end ContractRefinement

namespace PhysicalFabrication

inductive Simulation where
  | passed5kN

inductive Artifact where
  | printedPart

def unverifiedFabrication :
    Boundary Simulation Artifact where
  source := fun _ => True
  target := fun _ => True
  sourceClaim := fun _ => True
  targetClaim := fun _ => True
  relates := fun _ _ => True
  transferWarrant := fun _ _ => False
  localWarrant := fun _ => False

def physical_claim_is_unsupported :
    UnsupportedIntroductionWitness unverifiedFabrication := by
  refine {
    targetValue := Artifact.printedPart
    targetInScope := ?_
    targetClaimAsserted := ?_
    notEntitled := ?_
  }
  · trivial
  · trivial
  · intro h
    rcases h with hInherited | hLocal
    · rcases hInherited with
        ⟨s, _hSource, _hClaim, _hRel, hWarrant⟩
      exact hWarrant.elim
    · exact hLocal.elim

def verifiedFabrication :
    Boundary Simulation Artifact where
  source := fun _ => True
  target := fun _ => True
  sourceClaim := fun _ => True
  targetClaim := fun _ => True
  relates := fun _ _ => True
  transferWarrant := fun _ _ => False
  localWarrant := fun _ => True

theorem verified_fabrication_valid :
    Valid verifiedFabrication := by
  constructor
  · intro s t hs hClaim hRel hWarrant ht
    exact hWarrant.elim
  · constructor
    · intro t ht hLocal
      trivial
    · intro t ht hClaim
      exact Or.inr trivial


/-!
### Evidence-origin attack

The existing `verifiedFabrication` boundary sets:

    localWarrant := True

That should NOT be sufficient by itself.

The first evidence model accepts no evidence at all. Therefore the local
warrant cannot be grounded.
-/

def noPhysicalEvidence :
    EvidenceBasis Artifact Unit where
  admissible := fun _ => False
  supports := fun _ _ => False

theorem bare_local_warrant_not_grounded :
    ¬ LocalWarrantGrounded
        verifiedFabrication
        noPhysicalEvidence := by
  intro h

  have hEvidence :=
    h Artifact.printedPart trivial

  rcases hEvidence with
    ⟨e, hAdmissible, _hSupports⟩

  exact hAdmissible.elim

/--
A minimal physical evidence carrier.

`loadTestPassed` stands only for an externally established artifact.
E37 does not claim here that a real load-test implementation has been
verified.
-/
inductive PhysicalEvidence where
  | loadTestPassed

def physicalEvidenceBasis :
    EvidenceBasis Artifact PhysicalEvidence where
  admissible := fun e =>
    match e with
    | PhysicalEvidence.loadTestPassed => True
  supports := fun e a =>
    match e, a with
    | PhysicalEvidence.loadTestPassed, Artifact.printedPart => True

/--
The physical local warrant is now explicitly grounded in an admissible
evidence artifact.
-/
theorem physical_local_warrant_grounded :
    LocalWarrantGrounded
      verifiedFabrication
      physicalEvidenceBasis := by
  intro t hLocal
  cases t
  exact ⟨
    PhysicalEvidence.loadTestPassed,
    trivial,
    trivial
  ⟩

/--
The evidence interpretation is sufficient for the toy physical claim.

Again, this theorem is internal to the toy evidence semantics. A real
physical system requires a separate bridge showing that its test procedure
implements this evidence predicate adequately.
-/
theorem physical_evidence_supports_claim :
    EvidenceSupportsClaim
      verifiedFabrication
      physicalEvidenceBasis := by
  intro e t hAdmissible hSupports hTarget
  cases e
  cases t
  trivial

/--
The repaired physical boundary is evidence-backed.

The key distinction is now explicit:

    localWarrant = True

is NOT enough.

The warrant becomes acceptable only when its independent evidence
grounding and evidence-to-claim interpretation are both discharged.
-/
theorem verified_fabrication_evidence_backed :
    EvidenceBackedValid
      verifiedFabrication
      physicalEvidenceBasis := by
  refine ⟨
    ?_,
    physical_local_warrant_grounded,
    physical_evidence_supports_claim,
    ?_
  ⟩
  · intro s t hSource hSourceClaim hRel hWarrant hTarget
    exact hWarrant.elim
  · intro t hTarget hClaim
    exact Or.inr trivial


/-!
### Empirical-anchor attack

We now construct two external interpretations using exactly the same:

  * fabricated artifact,
  * evidence token,
  * admissibility predicate,
  * support relation,
  * E37 boundary.

In the nominal interpretation the physical property holds.

In the defective interpretation the SAME evidence token is observed but
the physical property does not hold.

Therefore internal evidence-backed validity alone cannot determine physical
truth.
-/

def nominalPhysicalSemantics :
    EmpiricalSemantics Artifact PhysicalEvidence Unit where
  targetPresent := fun _ _ => True
  evidenceObserved := fun _ _ => True
  worldClaim := fun _ _ => True

def defectivePhysicalSemantics :
    EmpiricalSemantics Artifact PhysicalEvidence Unit where
  targetPresent := fun _ _ => True
  evidenceObserved := fun _ _ => True
  worldClaim := fun _ _ => False

theorem nominal_local_warrant_empirically_realized :
    LocalWarrantEmpiricallyRealized
      verifiedFabrication
      physicalEvidenceBasis
      nominalPhysicalSemantics
      () := by
  intro t hLocal
  cases t
  exact ⟨
    PhysicalEvidence.loadTestPassed,
    trivial,
    trivial,
    trivial
  ⟩

theorem defective_local_warrant_empirically_realized :
    LocalWarrantEmpiricallyRealized
      verifiedFabrication
      physicalEvidenceBasis
      defectivePhysicalSemantics
      () := by
  intro t hLocal
  cases t
  exact ⟨
    PhysicalEvidence.loadTestPassed,
    trivial,
    trivial,
    trivial
  ⟩

theorem nominal_evidence_semantics_adequate :
    EvidenceSemanticsAdequate
      physicalEvidenceBasis
      nominalPhysicalSemantics := by
  intro w e t hObserved hAdmissible hSupports hPresent
  cases e
  cases t
  trivial

theorem defective_evidence_semantics_not_adequate :
    ¬ EvidenceSemanticsAdequate
        physicalEvidenceBasis
        defectivePhysicalSemantics := by
  intro h

  exact h
    ()
    PhysicalEvidence.loadTestPassed
    Artifact.printedPart
    trivial
    trivial
    trivial
    trivial

/--
The nominal physical interpretation reaches the external world claim only
after the empirical adequacy bridge is explicitly supplied.
-/
theorem nominal_fabrication_empirically_anchored :
    EmpiricallyAnchoredValid
      verifiedFabrication
      physicalEvidenceBasis
      nominalPhysicalSemantics
      () := by
  exact ⟨
    verified_fabrication_evidence_backed,
    nominal_local_warrant_empirically_realized,
    nominal_evidence_semantics_adequate
  ⟩

theorem nominal_physical_world_claim :
    nominalPhysicalSemantics.worldClaim
      ()
      Artifact.printedPart := by
  exact empirically_anchored_local_claim
    nominal_fabrication_empirically_anchored
    trivial
    trivial

/--
E37's key negative empirical result.

Everything internal to the evidence machinery may succeed:

  * the boundary is evidence-backed;
  * an admissible evidence artifact exists;
  * that artifact is actually observed;
  * the evidence model says it supports the artifact.

Yet physical truth still does not follow if the evidence-to-world
interpretation is inadequate.

The remaining assumption has therefore been localized rather than hidden.
-/
theorem internal_evidence_stops_at_empirical_anchor :
    EvidenceBackedValid
      verifiedFabrication
      physicalEvidenceBasis
    ∧
    LocalWarrantEmpiricallyRealized
      verifiedFabrication
      physicalEvidenceBasis
      defectivePhysicalSemantics
      ()
    ∧
    ¬ EvidenceSemanticsAdequate
        physicalEvidenceBasis
        defectivePhysicalSemantics := by
  exact ⟨
    verified_fabrication_evidence_backed,
    defective_local_warrant_empirically_realized,
    defective_evidence_semantics_not_adequate
  ⟩


/--
Explicit countermodel:

internal evidence-backed validity does not, by itself, imply the external
world claim.

The E37 boundary and evidence basis are held fixed while the external
interpretation is one in which the physical claim is false.

This proves that the formal evidence state alone is insufficient to derive
physical truth without an empirical adequacy bridge.
-/
theorem evidence_backed_valid_not_sufficient_for_world_claim :
    ¬ (
      EvidenceBackedValid
        verifiedFabrication
        physicalEvidenceBasis →
      defectivePhysicalSemantics.worldClaim
        ()
        Artifact.printedPart
    ) := by
  intro h
  have hWorld :=
    h verified_fabrication_evidence_backed
  exact hWorld

/--
The same internal E37 boundary and evidence basis are compatible with
opposite external-world interpretations.

The distinction between the nominal and defective worlds is therefore not
contained in the internal evidence-backed judgment itself.
-/
theorem same_internal_evidence_opposite_world_truth :
    EvidenceBackedValid
      verifiedFabrication
      physicalEvidenceBasis
    ∧
    nominalPhysicalSemantics.worldClaim
      ()
      Artifact.printedPart
    ∧
    ¬ defectivePhysicalSemantics.worldClaim
        ()
        Artifact.printedPart := by
  refine ⟨
    verified_fabrication_evidence_backed,
    ?_,
    ?_
  ⟩
  · trivial
  · intro h
    exact h

theorem physical_claim_entitled_after_local_evidence :
    Entitled verifiedFabrication Artifact.printedPart := by
  exact Or.inr trivial

end PhysicalFabrication

#print axioms DARM.E37.empirically_anchored_local_claim
#print axioms DARM.E37.PhysicalFabrication.nominal_local_warrant_empirically_realized
#print axioms DARM.E37.PhysicalFabrication.defective_local_warrant_empirically_realized
#print axioms DARM.E37.PhysicalFabrication.nominal_evidence_semantics_adequate
#print axioms DARM.E37.PhysicalFabrication.defective_evidence_semantics_not_adequate
#print axioms DARM.E37.PhysicalFabrication.nominal_fabrication_empirically_anchored
#print axioms DARM.E37.PhysicalFabrication.nominal_physical_world_claim
#print axioms DARM.E37.PhysicalFabrication.internal_evidence_stops_at_empirical_anchor
#print axioms DARM.E37.evidence_backed_valid_implies_valid
#print axioms DARM.E37.PhysicalFabrication.bare_local_warrant_not_grounded
#print axioms DARM.E37.PhysicalFabrication.physical_local_warrant_grounded
#print axioms DARM.E37.PhysicalFabrication.physical_evidence_supports_claim
#print axioms DARM.E37.PhysicalFabrication.verified_fabrication_evidence_backed

#print axioms DARM.E37.PhysicalFabrication.evidence_backed_valid_not_sufficient_for_world_claim
#print axioms DARM.E37.PhysicalFabrication.same_internal_evidence_opposite_world_truth

end DARM.E37

#print axioms DARM.E37.target_claim_iff_entitled
#print axioms DARM.E37.lossWitness_breaks_transferSound
#print axioms DARM.E37.unsupportedIntroduction_breaks_condition
#print axioms DARM.E37.two_boundary_transfer_sound
#print axioms DARM.E37.terminal_failure_localizes
#print axioms DARM.E37.r5_assurance_yields_valid_boundary
#print axioms DARM.E37.IntegrityUpgrade.upgrade_is_unsupported
#print axioms DARM.E37.AuthorityExpansion.write_authority_is_unsupported
#print axioms DARM.E37.ContractRefinement.refinement_boundary_valid
#print axioms DARM.E37.PhysicalFabrication.physical_claim_is_unsupported
#print axioms DARM.E37.PhysicalFabrication.verified_fabrication_valid
