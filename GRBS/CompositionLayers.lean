/-
  COMPOSING DEFENSES: WHEN ONE LAYER BACKS UP ANOTHER

  A layer checks a list of dimensions, each from its own view of the request,
  and admits if every dimension it checks looks fine. Two layers compose by
  both having to admit.

  Proved: the composition never admits more than either layer; and if the
  second layer checks a dimension from a correct view, a request that is bad in
  that dimension is refused whatever the first layer saw (independent backup).
  Witnesses, one per composition-experiment result: a fault in a dimension the
  second layer does not check passes the composition; a corruption in an input
  both layers share passes it; the same corruption, seen correctly by the
  second layer, is refused. So a layer backs up another only in a dimension it
  also checks, from an independent input.

  NOT claimed: anything about a particular upstream defense; that a layer's
  view is correct (that is the independence assumption the witnesses vary).
-/
namespace DARM.Composition

structure Layer (D : Type) where
  checks : List D

/-- A layer admits if every dimension it checks looks fine in its view. -/
def admits {D : Type} (L : Layer D) (view : D → Bool) : Bool := L.checks.all view

/-- Two layers compose by both having to admit. -/
def composed {D : Type} (A B : Layer D) (va vb : D → Bool) : Bool := admits A va && admits B vb

theorem composed_admits_only_if_both {D : Type} (A B : Layer D) (va vb : D → Bool)
    (h : composed A B va vb = true) : admits A va = true ∧ admits B vb = true := by
  unfold composed at h
  cases ha : admits A va <;> cases hb : admits B vb <;> simp_all

/-- Independent backup: if B checks d from a correct view and d is actually
    bad, the composition refuses, whatever A saw. -/
theorem independent_backup {D : Type} (A B : Layer D) (va vb ok : D → Bool) (d : D)
    (hB : d ∈ B.checks) (hcorrect : vb d = ok d) (hbad : ok d = false) :
    composed A B va vb = false := by
  unfold composed admits
  cases h : B.checks.all vb with
  | false => simp
  | true =>
    have hd := (List.all_eq_true.mp h) d hB
    rw [hcorrect, hbad] at hd
    exact absurd hd (by decide)

/-! ## Witnesses: the composition experiment's three results -/

inductive Dim where
  | authority | temporal | policy | provenance
  deriving DecidableEq, Repr

def allDims : List Dim := [.authority, .temporal, .policy, .provenance]
/-- The broker checks every dimension. -/
def broker : Layer Dim := ⟨allDims⟩
/-- An upstream layer that checks provenance only. -/
def provenanceOnly : Layer Dim := ⟨[.provenance]⟩

def authorityBad : Dim → Bool
  | .authority => false
  | _ => true
def provenanceBad : Dim → Bool
  | .provenance => false
  | _ => true
/-- A faulty or corrupted view: everything looks fine. -/
def allFine : Dim → Bool := fun _ => true

/-- A broker fault in authority passes a provenance-only layer. -/
theorem different_dimension_no_backup :
    composed broker provenanceOnly allFine authorityBad = true ∧
    allDims.all authorityBad = false := by
  decide

/-- Corrupted labels shared by both layers get through. -/
theorem shared_input_no_backup :
    composed broker provenanceOnly allFine allFine = true ∧
    allDims.all provenanceBad = false := by
  decide

/-- The same corruption, seen correctly by the upstream layer, is refused. -/
theorem independent_input_backs_up :
    composed broker provenanceOnly allFine provenanceBad = false :=
  independent_backup broker provenanceOnly allFine provenanceBad provenanceBad .provenance
    (by decide) rfl rfl

end DARM.Composition

#print axioms DARM.Composition.composed_admits_only_if_both
#print axioms DARM.Composition.independent_backup
#print axioms DARM.Composition.different_dimension_no_backup
#print axioms DARM.Composition.shared_input_no_backup
#print axioms DARM.Composition.independent_input_backs_up
