import DARMCoreCalculus

namespace GRBS.DCEE3AEBTransfer

open GRBS
open GRBS.R5AssuranceConservation
open GRBS.R6GRBSDeltaBridge
open GRBS.DARMCoreCalculus

/--
A minimal AEB-style consequential action representation.

The representation distinguishes the consequential effect,
the authorization/evidence binding, and the paths by which
the executor can produce the effect.
-/
structure AEBAction (D : Type) where
  effect : D → Prop
  authorized : D → Prop
  evidenced : D → Prop
  mediated : D → Prop
  alternatePath : D → Prop

/-- A minimal executor-side validity condition. -/
def AEBValid
    {D : Type}
    (a : AEBAction D) : Prop :=
  (∀ d, a.effect d → a.authorized d) ∧
  (∀ d, a.effect d → a.evidenced d) ∧
  (∀ d, a.effect d → a.mediated d) ∧
  (∀ d, a.effect d → ¬ a.alternatePath d)

/-- A scope change introduces or removes consequential effects. -/
structure ScopeChange (D : Type) where
  source : D → Prop
  target : D → Prop
  property : D → Prop

namespace Level3AMinimalCounterexample

inductive D
  | d1
  | d2

inductive G
  | g

inductive S
  | s

inductive B
  | b

inductive L
  | l

def F : GRBS.Frame where
  Trace := Unit
  Guarantee := G
  System := S
  Boundary := B
  Locus := L
  Dependency := D
  Environment := Unit
  Safe := fun _ _ => True
  dep := fun _ _ d =>
    match d with
    | D.d1 => True
    | D.d2 => True
  cov := fun _ _ _ d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def source : D → Prop
  | D.d1 => True
  | D.d2 => False

def target : D → Prop
  | D.d1 => True
  | D.d2 => True

def property : D → Prop := fun _ => True

/--
The minimal AEB-style case sees only the original mediated effect.
The newly introduced d2 effect is not represented in the case.
-/
def aebCase : AEBAction D where
  effect := source
  authorized := fun _ => True
  evidenced := fun _ => True
  mediated := fun _ => True
  alternatePath := fun _ => False

theorem aeb_case_valid :
    AEBValid aebCase := by
  simp [AEBValid, aebCase]

theorem target_dependency_is_introduced :
    target D.d2 := by
  trivial

theorem target_dependency_is_uncovered :
    ¬ GRBS.Frame.cov F B.b L.l S.s D.d2 := by
  intro h
  exact h

theorem darm_rejects_scope_expansion :
    ¬ GRBS F G.g S.s B.b L.l := by
  intro h
  have hc : GRBS.Frame.cov F B.b L.l S.s D.d2 :=
    h D.d2 trivial
  exact hc

theorem aeb_validity_survives_but_darm_rejects :
    AEBValid aebCase ∧
    ¬ GRBS F G.g S.s B.b L.l := by
  constructor
  · exact aeb_case_valid
  · exact darm_rejects_scope_expansion

end Level3AMinimalCounterexample

end GRBS.DCEE3AEBTransfer

namespace GRBS.DCEE3AEBTransfer.Level3BExplicitCoverage

inductive D
  | d1
  | d2

/-- Explicit target effect/dependency representation. -/
structure ExplicitAEBAction (D : Type) where
  effect : D → Prop
  authorized : D → Prop
  evidenced : D → Prop
  mediated : D → Prop
  alternatePath : D → Prop

/-- Every target effect must be authorized, evidenced, mediated,
    and free of an alternate/bypass path. -/
def ExplicitAEBValid
    {D : Type}
    (target : D → Prop)
    (a : ExplicitAEBAction D) : Prop :=
  (∀ d, target d → a.effect d) ∧
  (∀ d, target d → a.authorized d) ∧
  (∀ d, target d → a.evidenced d) ∧
  (∀ d, target d → a.mediated d) ∧
  (∀ d, target d → ¬ a.alternatePath d)

def source : D → Prop
  | D.d1 => True
  | D.d2 => False

def target : D → Prop
  | D.d1 => True
  | D.d2 => True

/--
The enriched AEB representation explicitly claims the target effects,
but d2 is not mediated.
-/
def aebCase : ExplicitAEBAction D where
  effect := target
  authorized := fun _ => True
  evidenced := fun _ => True
  mediated := fun d =>
    match d with
    | D.d1 => True
    | D.d2 => False
  alternatePath := fun _ => False

theorem target_effect_is_explicit :
    ∀ d, target d → aebCase.effect d := by
  intro d hd
  exact hd

theorem explicit_aeb_rejects_unmediated_target :
    ¬ ExplicitAEBValid target aebCase := by
  intro h
  have hmed : aebCase.mediated D.d2 := h.2.2.2.1 D.d2 trivial
  exact hmed

theorem darm_rejects_same_target :
    ¬ GRBS
        (F := {
          Trace := Unit
          Guarantee := Unit
          System := Unit
          Boundary := Unit
          Locus := Unit
          Dependency := D
          Environment := Unit
          Safe := fun _ _ => True
          dep := fun _ _ _ => True
          cov := fun _ _ _ d =>
            match d with
            | D.d1 => True
            | D.d2 => False
          Envs := fun _ _ => True
          Traces := fun _ _ _ _ => True
          Perturbs := fun _ _ => True
        })
        ()
        ()
        ()
        () := by
  intro h
  have hc :
      (match D.d2 with
      | D.d1 => True
      | D.d2 => False) := h D.d2 trivial
  exact hc

theorem both_reject_same_target :
    (¬ ExplicitAEBValid target aebCase) ∧
    ¬ GRBS
        (F := {
          Trace := Unit
          Guarantee := Unit
          System := Unit
          Boundary := Unit
          Locus := Unit
          Dependency := D
          Environment := Unit
          Safe := fun _ _ => True
          dep := fun _ _ _ => True
          cov := fun _ _ _ d =>
            match d with
            | D.d1 => True
            | D.d2 => False
          Envs := fun _ _ => True
          Traces := fun _ _ _ _ => True
          Perturbs := fun _ _ => True
        })
        ()
        ()
        ()
        () := by
  constructor
  · exact explicit_aeb_rejects_unmediated_target
  · exact darm_rejects_same_target

end GRBS.DCEE3AEBTransfer.Level3BExplicitCoverage

namespace GRBS.DCEE3AEBTransfer.Level3CPositiveCorrespondence

inductive D
  | d1
  | d2

structure PositiveAEBAction (D : Type) where
  effect : D → Prop
  authorized : D → Prop
  evidenced : D → Prop
  mediated : D → Prop
  alternatePath : D → Prop

def PositiveAEBValid
    {D : Type}
    (target : D → Prop)
    (a : PositiveAEBAction D) : Prop :=
  (∀ d, target d → a.effect d) ∧
  (∀ d, target d → a.authorized d) ∧
  (∀ d, target d → a.evidenced d) ∧
  (∀ d, target d → a.mediated d) ∧
  (∀ d, target d → ¬ a.alternatePath d)

def source : D → Prop
  | D.d1 => True
  | D.d2 => False

def target : D → Prop
  | D.d1 => True
  | D.d2 => True

def property : D → Prop := fun _ => True

def aebCase : PositiveAEBAction D where
  effect := target
  authorized := fun _ => True
  evidenced := fun _ => True
  mediated := fun _ => True
  alternatePath := fun _ => False

def F : GRBS.Frame where
  Trace := Unit
  Guarantee := Unit
  System := Unit
  Boundary := Unit
  Locus := Unit
  Dependency := D
  Environment := Unit
  Safe := fun _ _ => True
  dep := fun _ _ _ => True
  cov := fun _ _ _ _ => True
  Envs := fun _ _ => True
  Traces := fun _ _ _ _ => True
  Perturbs := fun _ _ => True

def candidate : GRBS.DARMCoreCalculus.TransferCandidate F.Dependency where
  source := source
  target := target
  property := property

theorem aeb_positive_transfer_holds :
    PositiveAEBValid target aebCase := by
  simp [PositiveAEBValid, aebCase]

theorem darm_grbs_holds :
    GRBS F () () () () := by
  intro d hd
  trivial

theorem darm_delta_is_represented :
    GRBS.R6GRBSDeltaBridge.DeltaSubsetDependency
      F () () source target := by
  intro d hd
  trivial

theorem darm_delta_is_discharged :
    GRBS.R6GRBSDeltaBridge.CoveredDischargesProperty
      F () () () () property := by
  intro d hd hcov
  trivial

theorem darm_transfer_holds :
    GRBS.DARMCoreCalculus.DARMTransferAdmissible
      F () () () () candidate := by
  constructor
  · exact darm_delta_is_represented
  · constructor
    · exact darm_grbs_holds
    · exact darm_delta_is_discharged

theorem positive_correspondence_witness :
    PositiveAEBValid target aebCase ∧
    GRBS.DARMCoreCalculus.DARMTransferAdmissible
      F () () () () candidate := by
  constructor
  · exact aeb_positive_transfer_holds
  · exact darm_transfer_holds

end GRBS.DCEE3AEBTransfer.Level3CPositiveCorrespondence
