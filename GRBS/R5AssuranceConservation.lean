/-
  R5 — ASSURANCE CONSERVATION SYNTHESIS

  PURPOSE:

  R4a-R4e independently attacked assurance transfer under changes in:

    R4a  scope
    R4b  authority
    R4c  enforcement locus
    R4d  evidentiary basis
    R4e  boundary composition

  R5 asks whether these heterogeneous attacks share a common transfer
  structure:

      source assurance
          +
      assurance-relevant delta
          +
      discharged delta obligation
          =>
      justified target assurance

  The negative case is:

      valid source assurance
      +
      nonempty assurance-relevant delta
      +
      undischarged obligation
          =>
      unsupported target assurance

  IMPORTANT:

  This is a synthesis abstraction over the R4 attack family.

  It does not claim that scope, authority, locus, evidence, and composition
  are semantically identical.

  It does not claim that this abstraction is novel.

  It tests whether a common assurance-transfer structure can be stated and
  machine-checked independently of the individual R4 witnesses.
-/

namespace GRBS.R5AssuranceConservation

-- § 1  Abstract assurance state

/--
A source assurance establishes the relevant property over the original
assurance domain.
-/
def SourceAssured
    (X : Type)
    (source : X → Prop)
    (property : X → Prop) : Prop :=
  ∀ x, source x → property x

/--
A target assurance requires the property over the target domain.
-/
def TargetAssured
    (X : Type)
    (target : X → Prop)
    (property : X → Prop) : Prop :=
  ∀ x, target x → property x

/--
The assurance-relevant delta consists of items in the target domain that
were not in the source domain.
-/
def Delta
    (X : Type)
    (source target : X → Prop) : X → Prop :=
  fun x => target x ∧ ¬ source x

/--
A transfer obligation requires the target property for every item introduced
by the assurance-relevant delta.
-/
def DeltaObligation
    (X : Type)
    (source target : X → Prop)
    (property : X → Prop) : Prop :=
  ∀ x, Delta X source target x → property x

-- § 2  Positive conservation theorem

/--
If the source is assured and every newly introduced target item satisfies
the property, then the target is assured.

This is the positive conservation direction.

The obligation is a condition. It is not assumed to be automatically
discharged.
-/
theorem target_assured_of_source_and_delta
    (X : Type)
    (source target : X → Prop)
    (property : X → Prop)
    (hSource : SourceAssured X source property)
    (hDelta : DeltaObligation X source target property) :
    TargetAssured X target property := by
  intro x hx
  by_cases hs : source x
  · exact hSource x hs
  · exact hDelta x ⟨hx, hs⟩

-- § 3  Negative transfer theorem

/--
If the target introduces an item for which the required property is not
established, target assurance cannot hold.

This is the core conservation failure.

The source-assurance hypothesis is not needed for this negative direction.
That fact is intentional: the failure concerns the target obligation.
-/
theorem target_not_assured_of_undischarged_delta
    (X : Type)
    (source target : X → Prop)
    (property : X → Prop)
    (x₀ : X)
    (hIntroduced : target x₀ ∧ ¬ source x₀)
    (hUnestablished : ¬ property x₀) :
    ¬ TargetAssured X target property := by
  intro hTarget
  exact hUnestablished (hTarget x₀ hIntroduced.1)

-- § 4  Conservation condition

/--
A transfer is assurance-conserving when every assurance-relevant item
introduced by the target domain is discharged.
-/
def AssuranceConservingTransfer
    (X : Type)
    (source target : X → Prop)
    (property : X → Prop) : Prop :=
  DeltaObligation X source target property

/--
A conserving transfer preserves assurance.
-/
theorem conserving_transfer_preserves_assurance
    (X : Type)
    (source target : X → Prop)
    (property : X → Prop)
    (hSource : SourceAssured X source property)
    (hConserve : AssuranceConservingTransfer X source target property) :
    TargetAssured X target property := by
  exact target_assured_of_source_and_delta
    X source target property hSource hConserve

-- § 5  Concrete R5 witness

inductive Item where
  | original
  | introduced
deriving DecidableEq

def sourceDomain : Item → Prop
  | Item.original => True
  | Item.introduced => False

/--
The target domain adds one new assurance-relevant item.
-/
def targetDomain : Item → Prop
  | Item.original => True
  | Item.introduced => True

/--
The original item satisfies the guarantee.

The introduced item does not.
-/
def property : Item → Prop
  | Item.original => True
  | Item.introduced => False

-- § 6  Source assurance is valid

theorem source_is_assured :
    SourceAssured Item sourceDomain property := by
  intro x hx
  cases x with
  | original => trivial
  | introduced => contradiction

-- § 7  Target introduces a genuinely new assurance obligation

theorem introduced_item_is_delta :
    Delta Item sourceDomain targetDomain Item.introduced := by
  constructor
  · trivial
  · intro h
    cases h

/--
The newly introduced item does not satisfy the target property.
-/
theorem introduced_item_not_property :
    ¬ property Item.introduced := by
  intro h
  cases h

-- § 8  Conservation obligation fails

theorem conservation_obligation_not_discharged :
    ¬ AssuranceConservingTransfer
      Item sourceDomain targetDomain property := by
  intro h
  have hp : property Item.introduced :=
    h Item.introduced introduced_item_is_delta
  exact introduced_item_not_property hp

-- § 9  Unsupported transfer

/--
The source assurance remains valid, but target assurance fails because the
assurance-relevant delta is not discharged.
-/
theorem unsupported_transfer :
    SourceAssured Item sourceDomain property
    ∧ ¬ TargetAssured Item targetDomain property := by
  constructor
  · exact source_is_assured
  · intro h
    have hp : property Item.introduced :=
      h Item.introduced trivial
    exact introduced_item_not_property hp

/--
Complete R5 witness:

    source assurance       HOLDS
    assurance delta        EXISTS
    delta obligation       NOT DISCHARGED
    target assurance       FAILS
-/
theorem assurance_conservation_failure :
    SourceAssured Item sourceDomain property
    ∧ Delta Item sourceDomain targetDomain Item.introduced
    ∧ ¬ AssuranceConservingTransfer
        Item sourceDomain targetDomain property
    ∧ ¬ TargetAssured Item targetDomain property := by
  exact ⟨
    source_is_assured,
    introduced_item_is_delta,
    conservation_obligation_not_discharged,
    unsupported_transfer.2
  ⟩

/-!
  ## R5 interpretation

  R5 establishes a generic machine-checked transfer pattern:

      source assurance
          +
      introduced assurance-relevant state
          +
      discharged delta
          =>
      target assurance

  Conversely:

      source assurance
          +
      introduced assurance-relevant state
          +
      undischarged required property
          =>
      no target assurance

  R5 does NOT establish:

      * that scope, authority, locus, evidence, and composition are
        mathematically identical;

      * that every assurance framework must use this representation;

      * that this abstraction is absent from prior assurance-case,
        assume-guarantee, contract, capability, or compositional reasoning;

      * that GRBS is a fundamentally new semantic safety logic.

  The research question after R5 is therefore comparative:

      Does DARM provide a useful explicit representation of assurance
      transfer obligations across heterogeneous assurance changes, and
      does that representation expose unsupported assurance expansion
      that relevant existing methods leave implicit?

  That question requires comparison against prior art rather than another
  internally constructed theorem.
-/

end GRBS.R5AssuranceConservation
