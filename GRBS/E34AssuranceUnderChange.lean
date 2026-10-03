/-
  E34 — AN ASSURANCE CLAIM THAT REMAINS VALID AS THE IMPLEMENTATION CHANGES

  An unconditional claim about what an implementation does cannot be decided
  from its code (Rice's theorem): a gate that judges changes from code alone is
  unsound or incomplete. The effect-surface gate is sound and incomplete by
  design, and what it supports is an inductive claim over the repository's
  history: every version the build accepts satisfies the property.

  Model. A program maps function names to code. An analysis supplies the
  effect functions of a program and, for each, its cone: the functions its
  verdict depends on. The property is local when its truth depends only on
  which functions are effect functions and on the code inside their cones. The
  gate accepts a version when it has the reviewed effect functions, the
  reviewed cones, and the reviewed code in every cone (in the implementation,
  token fingerprints stand for code equality).

  Proved: a local property that holds of the reviewed version holds of every
  version the gate accepts (preserved); in any history built from reviews and
  gate-passing commits, every version satisfies it (history_preserved). Both
  conditions are needed in the precise sense of two witnesses: a verdict that
  depends on code outside its cone passes the gate and fails
  (locality_necessary); and a change that keeps the property is still
  rejected (gate_incomplete), the price of soundness.

  Assumed, and stated: each review that accepts a version is correct; equal
  fingerprints mean equal code (collision resistance); equal code means equal
  behavior in the same environment. Not modeled: Python.
-/

namespace DARM.E34

abbrev Prog (N C : Type) := N → Option C

structure Analysis (N C : Type) where
  eff : Prog N C → List N
  cone : Prog N C → N → List N

/-- The property depends only on the effect functions and the code in their cones. -/
def Local {N C : Type} (A : Analysis N C) (P : Prog N C → Prop) : Prop :=
  ∀ V W : Prog N C, A.eff V = A.eff W →
    (∀ s ∈ A.eff V, A.cone V s = A.cone W s ∧ ∀ n ∈ A.cone V s, V n = W n) → (P V ↔ P W)

/-- The gate: the reviewed effect functions, the reviewed cones, the reviewed code in each. -/
def Gate {N C : Type} (A : Analysis N C) (R V : Prog N C) : Prop :=
  A.eff V = A.eff R ∧ ∀ s ∈ A.eff R, A.cone V s = A.cone R s ∧ ∀ n ∈ A.cone R s, V n = R n

theorem preserved {N C : Type} (A : Analysis N C) (P : Prog N C → Prop) (hL : Local A P)
    (R V : Prog N C) (hR : P R) (hG : Gate A R V) : P V := by
  have h := hL R V hG.1.symm (fun s hs => by
    obtain ⟨hc, hcode⟩ := hG.2 s hs
    exact ⟨hc.symm, fun n hn => (hcode n hn).symm⟩)
  exact h.mp hR

/-- A history: reviewed versions, and versions the gate accepts against the
    last reviewed one. `Accepted R V`: V is in the history, R its last review. -/
inductive Accepted {N C : Type} (A : Analysis N C) (P : Prog N C → Prop) :
    Prog N C → Prog N C → Prop where
  | review (R : Prog N C) : P R → Accepted A P R R
  | step (R V W : Prog N C) : Accepted A P R V → Gate A R W → Accepted A P R W
  | reaccept (R V W : Prog N C) : Accepted A P R V → P W → Accepted A P W W

/-- Every version in an accepted history satisfies the property. -/
theorem history_preserved {N C : Type} (A : Analysis N C) (P : Prog N C → Prop) (hL : Local A P)
    {R V : Prog N C} (h : Accepted A P R V) : P V ∧ P R := by
  induction h with
  | review R hR => exact ⟨hR, hR⟩
  | step R V W _ hG ih => exact ⟨preserved A P hL R W ih.2 hG, ih.2⟩
  | reaccept R V W _ hW _ => exact ⟨hW, hW⟩

/-! ## Why each condition is needed -/

/-- A reviewed program: the effect function `exec`, and a helper it relies on. -/
def reviewed : Prog String Nat := fun n => if n = "exec" then some 1 else if n = "helper" then some 0 else none
/-- The helper changes; exec does not. -/
def helperChanged : Prog String Nat := fun n => if n = "exec" then some 1 else if n = "helper" then some 1 else none
/-- exec is rewritten in a way that keeps what it does. -/
def execRewritten : Prog String Nat := fun n => if n = "exec" then some 2 else if n = "helper" then some 0 else none

/-- An analysis whose cone for exec omits the helper exec relies on. -/
def narrow : Analysis String Nat := ⟨fun _ => ["exec"], fun _ _ => ["exec"]⟩

/-- The verdict depends on the helper. -/
abbrev reliesOnHelper (V : Prog String Nat) : Prop := V "helper" = some 0

/-- Locality is necessary: the cone omits a dependency, the gate passes, and the
    property that held of the reviewed version fails. -/
theorem locality_necessary :
    Gate narrow reviewed helperChanged ∧ reliesOnHelper reviewed ∧ ¬ reliesOnHelper helperChanged := by
  refine ⟨⟨rfl, ?_⟩, by decide, by decide⟩
  intro s hs
  simp [narrow] at hs
  subst hs
  refine ⟨rfl, ?_⟩
  intro n hn
  simp [narrow] at hn
  subst hn
  decide

/-- The gate is incomplete: exec is rewritten without changing the property,
    and the gate rejects it all the same. -/
theorem gate_incomplete :
    ¬ Gate narrow reviewed execRewritten ∧ reliesOnHelper reviewed ∧ reliesOnHelper execRewritten := by
  refine ⟨?_, by decide, by decide⟩
  intro hG
  have := (hG.2 "exec" (by simp [narrow])).2 "exec" (by simp [narrow])
  exact absurd this (by decide)

end DARM.E34

#print axioms DARM.E34.preserved
#print axioms DARM.E34.history_preserved
#print axioms DARM.E34.locality_necessary
#print axioms DARM.E34.gate_incomplete
