import Mathlib.Data.Finset.Basic

namespace GRBS.IC1CredentialMutation

/--
A credential represented only by the set of tools it currently contains.
-/
structure Credential where
  tools : Finset Nat
deriving DecidableEq

/--
The current runtime-style credential update:
new tools are simply unioned into the existing credential.
-/
def expandCredential
    (credential : Credential)
    (newTools : Finset Nat) : Credential :=
  { tools := credential.tools ∪ newTools }

/--
The newly introduced authority.
-/
def AddedAuthority
    (before after : Credential) : Finset Nat :=
  after.tools \ before.tools

/--
Expansion really does introduce the requested new authority when it
was absent beforehand.
-/
theorem expansion_adds_new_authority :
    ∃ (before : Credential) (newTools : Finset Nat),
      let after := expandCredential before newTools
      AddedAuthority before after ≠ ∅ := by

  let before : Credential :=
    { tools := ∅ }

  let newTools : Finset Nat := {1}

  refine ⟨before, newTools, ?_⟩
  simp [expandCredential, AddedAuthority, before, newTools]

/--
A credential mutation by itself does not establish that the newly
added authority was independently authorized.

We model independent authorization explicitly rather than identifying
credential membership with authorization.
-/
def IndependentlyAuthorized
    (before : Credential)
    (newTools : Finset Nat) : Prop :=
  newTools ⊆ before.tools

/--
Concrete countermodel: a credential can be expanded with a tool that
was not already authorized by the previous credential.
-/
theorem credential_expansion_without_independent_authorization :
    ∃ (before : Credential) (newTools : Finset Nat),
      let after := expandCredential before newTools
      AddedAuthority before after ≠ ∅ ∧
      ¬ IndependentlyAuthorized before newTools := by

  let before : Credential :=
    { tools := ∅ }

  let newTools : Finset Nat := {1}

  refine ⟨before, newTools, ?_⟩
  constructor
  · simp [expandCredential, AddedAuthority, before, newTools]
  · simp [IndependentlyAuthorized, before, newTools]

/--
The key separation:

membership in the updated credential does not logically imply
independent authorization of the newly introduced authority.
-/
theorem credential_membership_does_not_imply_authorization :
    ¬ ∀ (before : Credential) (newTools : Finset Nat),
        let after := expandCredential before newTools
        newTools ⊆ after.tools →
        IndependentlyAuthorized before newTools := by

  intro h

  let before : Credential :=
    { tools := ∅ }

  let newTools : Finset Nat := {1}

  have hSubset :
      newTools ⊆ (expandCredential before newTools).tools := by
    simp [expandCredential, before, newTools]

  have hAuthorized :
      IndependentlyAuthorized before newTools :=
    h before newTools hSubset

  simp [IndependentlyAuthorized, before, newTools] at hAuthorized

end GRBS.IC1CredentialMutation

#print axioms GRBS.IC1CredentialMutation.expansion_adds_new_authority
#print axioms GRBS.IC1CredentialMutation.credential_expansion_without_independent_authorization
#print axioms GRBS.IC1CredentialMutation.credential_membership_does_not_imply_authorization
