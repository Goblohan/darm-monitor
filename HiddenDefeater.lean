namespace GRBS.HiddenDefeater

/-
  Tiny formal model:

  Visible card:
    System A passed the safety test.

  Hidden card:
    The safety test only checked formatting.

  Core claim:
    The visible claim can be true, yet reliance can collapse
    once the hidden boundary condition is revealed.
-/

inductive Atom where
  | passedSafetyTest
  | onlyFormatTest
deriving DecidableEq, Repr

abbrev Info := Atom -> Bool

def visible : Info
  | Atom.passedSafetyTest => true
  | Atom.onlyFormatTest => false

def full : Info
  | Atom.passedSafetyTest => true
  | Atom.onlyFormatTest => true

def contains (I : Info) (a : Atom) : Prop :=
  I a = true

/-
  Reliance rule:

  The receiver relies on the system if they know it passed a safety test
  and do not know that the test was only a formatting test.
-/
def relies (I : Info) : Prop :=
  contains I Atom.passedSafetyTest ∧
  ¬ contains I Atom.onlyFormatTest

def hidden (Ip Ir : Info) (a : Atom) : Prop :=
  Ip a = false ∧ Ir a = true

def materialSecret (Ip Ir : Info) (a : Atom) : Prop :=
  hidden Ip Ir a ∧ relies Ip ∧ ¬ relies Ir

/-
  The visible claim is true in the visible information state.
-/
theorem visible_contains_passed_test :
    contains visible Atom.passedSafetyTest := by
  rfl

/-
  The hidden defeater is absent from the visible state.
-/
theorem visible_hides_format_only :
    visible Atom.onlyFormatTest = false := by
  rfl

/-
  Before the hidden card is revealed, the receiver relies.
-/
theorem relies_on_visible :
    relies visible := by
  constructor
  · rfl
  · intro h
    cases h

/-
  After the hidden card is revealed, reliance fails.
-/
theorem does_not_rely_on_full :
    ¬ relies full := by
  intro h
  exact h.2 rfl

/-
  The hidden item is genuinely hidden.
-/
theorem only_format_test_is_hidden :
    hidden visible full Atom.onlyFormatTest := by
  constructor
  · rfl
  · rfl

/-
  Therefore the hidden item is a material secret.
-/
theorem only_format_test_is_material_secret :
    materialSecret visible full Atom.onlyFormatTest := by
  constructor
  · exact only_format_test_is_hidden
  · constructor
    · exact relies_on_visible
    · exact does_not_rely_on_full

/-
  The theorem-shaped version:

  In this model, there exists a hidden material secret whose disclosure
  defeats reliance.
-/
theorem material_secret_exists :
    ∃ a : Atom, materialSecret visible full a := by
  exists Atom.onlyFormatTest
  exact only_format_test_is_material_secret


/-
  General theorem:

  Any hidden atom whose disclosure coincides with reliance collapse
  is a material secret.
-/
theorem hidden_defeater_is_material
    (Ip Ir : Info)
    (a : Atom)
    (hHidden : hidden Ip Ir a)
    (hBefore : relies Ip)
    (hAfter : ¬ relies Ir) :
    materialSecret Ip Ir a := by
  constructor
  · exact hHidden
  · constructor
    · exact hBefore
    · exact hAfter

/-
  The concrete card experiment is an instance of the general theorem.
-/
theorem only_format_test_material_by_general_theorem :
    materialSecret visible full Atom.onlyFormatTest := by
  exact hidden_defeater_is_material
    visible
    full
    Atom.onlyFormatTest
    only_format_test_is_hidden
    relies_on_visible
    does_not_rely_on_full


end GRBS.HiddenDefeater
