/-
  R5 — DOMAIN POLYMORPHISM

  R5 is parameterized by an arbitrary assurance-object type X.

  The assurance object may represent:

    * a system component
    * an execution trace
    * an authority
    * an enforcement locus
    * an evidentiary coverage object
    * a dependency
    * a relational object
    * any other formally specified assurance domain

  R5 itself does not determine what X means.

  It specifies only the conservation condition required when assurance
  is transferred from a source domain to a target domain.
-/

namespace GRBS.R5DomainPolymorphism

/--
The assurance-relevant delta between a source and target domain.

An object is in the delta exactly when it is relevant to the target
assurance claim but was not in the source assurance domain.
-/
def Delta
    (X : Type)
    (source target : X → Prop) : X → Prop :=
  fun x => target x ∧ ¬ source x

/--
Assurance over the source domain.
-/
def SourceAssured
    (X : Type)
    (source : X → Prop)
    (property : X → Prop) : Prop :=
  ∀ x, source x → property x

/--
Assurance over the target domain.
-/
def TargetAssured
    (X : Type)
    (target : X → Prop)
    (property : X → Prop) : Prop :=
  ∀ x, target x → property x

/--
The assurance obligation introduced by the source-to-target transition.

Every newly relevant assurance object must satisfy the target property.
-/
def DeltaObligation
    (X : Type)
    (source target : X → Prop)
    (property : X → Prop) : Prop :=
  ∀ x, Delta X source target x → property x

/--
The generic assurance-conservation theorem.

If the source domain is assured and every assurance-relevant delta object
satisfies the required property, then the target domain is assured.
-/
theorem target_assured_of_source_and_delta
    (X : Type)
    (source target property : X → Prop)
    (hSource : SourceAssured X source property)
    (hDelta : DeltaObligation X source target property) :
    TargetAssured X target property := by
  intro x hxTarget
  by_cases hxSource : source x
  · exact hSource x hxSource
  · exact hDelta x ⟨hxTarget, hxSource⟩

/--
If a target-domain object lies in the assurance-relevant delta and fails
the required property, the target assurance claim cannot hold.
-/
theorem target_not_assured_of_bad_delta
    (X : Type)
    (source target property : X → Prop)
    (x : X)
    (hDelta : Delta X source target x)
    (hBad : ¬ property x) :
    ¬ TargetAssured X target property := by
  intro hTarget
  exact hBad (hTarget x hDelta.1)

/--
The conservation condition is therefore sufficient for transfer.
-/
def AssuranceConservingTransfer
    (X : Type)
    (source target property : X → Prop) : Prop :=
  DeltaObligation X source target property

theorem conserving_transfer_preserves_assurance
    (X : Type)
    (source target property : X → Prop)
    (hSource : SourceAssured X source property)
    (hConserve : AssuranceConservingTransfer X source target property) :
    TargetAssured X target property :=
  target_assured_of_source_and_delta
    X source target property hSource hConserve

/--
Domain polymorphism witness.

The theorem applies to a relational assurance domain without requiring
any special relational logic.

Here X is an arbitrary product type.
-/
theorem relational_domain_instance
    (A B : Type)
    (source target : A × B → Prop)
    (property : A × B → Prop)
    (hSource : SourceAssured (A × B) source property)
    (hDelta : DeltaObligation (A × B) source target property) :
    TargetAssured (A × B) target property :=
  target_assured_of_source_and_delta
    (A × B) source target property hSource hDelta

/--
The same generic theorem applies when the assurance object is itself
an execution trace, with no special treatment of traces.
-/
theorem trace_domain_instance
    (Trace : Type)
    (source target : Trace → Prop)
    (property : Trace → Prop)
    (hSource : SourceAssured Trace source property)
    (hDelta : DeltaObligation Trace source target property) :
    TargetAssured Trace target property :=
  target_assured_of_source_and_delta
    Trace source target property hSource hDelta

/--
Likewise for an arbitrary dependency domain.
-/
theorem dependency_domain_instance
    (Dependency : Type)
    (source target : Dependency → Prop)
    (property : Dependency → Prop)
    (hSource : SourceAssured Dependency source property)
    (hDelta : DeltaObligation Dependency source target property) :
    TargetAssured Dependency target property :=
  target_assured_of_source_and_delta
    Dependency source target property hSource hDelta

end GRBS.R5DomainPolymorphism
