/-
  E38: CONDITIONAL NON-LAUNDERING OF RELIANCE

  First model-only step. Distinguishes a target claim being asserted, a
  claim having warrant, and truth in an external world. The Boolean checks
  are abstract, not the current Python implementation. No inference of
  world truth is claimed without an additional adequacy assumption.
-/
import E37HeterogeneousWarrant

namespace DARM.E38

/-- Source and target can have different representation types. -/
structure RelianceVerifier (S T E W : Type) where
  boundary : DARM.E37.Boundary S T
  asserted : T → Prop
  worldTrue : W → T → Prop
  authentic : E → Prop
  boundToTarget : E → T → Prop
  current : E → Prop
  evidenceSupports : E → T → Prop
  checkSource : S → Bool
  checkSourceClaim : S → Bool
  checkRelation : S → T → Bool
  checkTransfer : S → T → Bool
  checkTarget : T → Bool
  checkAuthentic : E → Bool
  checkBinding : E → T → Bool
  checkFreshness : E → Bool
  checkSupport : E → T → Bool

/-- Semantic correctness requirements for each independent Boolean check. -/
structure SoundChecks {S T E W : Type}
    (v : RelianceVerifier S T E W) : Prop where
  source : ∀ s, v.checkSource s = true → v.boundary.source s
  sourceClaim : ∀ s, v.checkSourceClaim s = true → v.boundary.sourceClaim s
  relation : ∀ s t, v.checkRelation s t = true → v.boundary.relates s t
  transfer : ∀ s t, v.checkTransfer s t = true → v.boundary.transferWarrant s t
  target : ∀ t, v.checkTarget t = true → v.boundary.target t
  authenticity : ∀ e, v.checkAuthentic e = true → v.authentic e
  binding : ∀ e t, v.checkBinding e t = true → v.boundToTarget e t
  freshness : ∀ e, v.checkFreshness e = true → v.current e
  support : ∀ e t, v.checkSupport e t = true → v.evidenceSupports e t

/-- The model's executable Boolean interface. No assertion label is trusted. -/
def admitBool {S T E W : Type}
    (v : RelianceVerifier S T E W) (s : S) (t : T) (e : E) : Bool :=
  decide (
    v.checkSource s = true ∧
    v.checkSourceClaim s = true ∧
    v.checkRelation s t = true ∧
    v.checkTransfer s t = true ∧
    v.checkTarget t = true ∧
    v.checkAuthentic e = true ∧
    v.checkBinding e t = true ∧
    v.checkFreshness e = true ∧
    v.checkSupport e t = true)

/-- Entitlement is separate from assertion and external truth. -/
def Warranted {S T E W : Type}
    (v : RelianceVerifier S T E W) (t : T) (e : E) : Prop :=
  v.boundary.target t ∧
  DARM.E37.Entitled v.boundary t ∧
  v.authentic e ∧
  v.boundToTarget e t ∧
  v.current e ∧
  v.evidenceSupports e t

/-- No unsupported inherited reliance under explicit semantic check soundness.
    This theorem does NOT establish the checks' soundness for Python code. -/
theorem admitted_implies_warranted
    {S T E W : Type}
    (v : RelianceVerifier S T E W)
    (hSound : SoundChecks v)
    (s : S) (t : T) (e : E)
    (hAdmit : admitBool v s t e = true) :
    Warranted v t e := by
  have h :
      v.checkSource s = true ∧
      v.checkSourceClaim s = true ∧
      v.checkRelation s t = true ∧
      v.checkTransfer s t = true ∧
      v.checkTarget t = true ∧
      v.checkAuthentic e = true ∧
      v.checkBinding e t = true ∧
      v.checkFreshness e = true ∧
      v.checkSupport e t = true := by
    simpa [admitBool] using hAdmit
  rcases h with ⟨hs, hsc, hr, hw, ht, ha, hb, hf, hp⟩
  refine ⟨hSound.target t ht, ?_, hSound.authenticity e ha,
    hSound.binding e t hb, hSound.freshness e hf,
    hSound.support e t hp⟩
  exact Or.inl ⟨s, hSound.source s hs,
    hSound.sourceClaim s hsc,
    hSound.relation s t hr,
    hSound.transfer s t hw⟩

/-- An asserted claim is not made warranted merely by being asserted. -/
theorem asserted_does_not_suffice :
    ∃ (b : DARM.E37.Boundary Unit Unit),
      b.targetClaim () ∧ ¬ DARM.E37.Entitled b () := by
  let b : DARM.E37.Boundary Unit Unit := {
    source := fun _ => True
    target := fun _ => True
    sourceClaim := fun _ => True
    targetClaim := fun _ => True
    relates := fun _ _ => False
    transferWarrant := fun _ _ => False
    localWarrant := fun _ => False
  }
  refine ⟨b, trivial, ?_⟩
  intro h
  rcases h with hInherited | hLocal
  · rcases hInherited with ⟨_, _, _, hRel, _⟩
    exact hRel.elim
  · exact hLocal.elim

end DARM.E38
