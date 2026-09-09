import GRBS

namespace GRBS

variable
  {F : Frame}
  {g : F.Guarantee}
  {s : F.System}
  {b : F.Boundary}
  {l : F.Locus}

/--
Violation completeness.

Every admissible unsafe trace must perturb at least one
structural dependency of the guarantee.
-/
def ViolationComplete : Prop :=
  ∀ e t,
    F.Envs b e →
    F.Traces s e b t →
    ¬ F.Safe g t →
    ∃ d,
      F.dep g s d ∧
      F.Perturbs t d

/--
Covered protection.

A perturbation of a covered structural dependency cannot
produce a trace violating the guarantee.
-/
def CoveredProtects : Prop :=
  ∀ t d,
    F.dep g s d →
    F.cov b l s d →
    F.Perturbs t d →
    F.Safe g t

/--
GRBS sufficiency.

If every unsafe admissible trace exposes a structural
dependency, and every covered dependency is protected,
then complete coverage implies transfer.
-/
theorem transfer_of_grbs
    (hGRBS : GRBS F g s b l)
    (hComplete :
      ViolationComplete (F := F) (g := g) (s := s) (b := b))
    (hProtect :
      CoveredProtects (F := F) (g := g) (s := s) (b := b) (l := l)) :
    Transfer F g s b := by
  intro e hEnv t hTrace
  exact Classical.byContradiction (fun hUnsafe =>
    let hWitness := hComplete e t hEnv hTrace hUnsafe
    match hWitness with
    | ⟨d, hDep, hPerturbs⟩ =>
        hUnsafe (hProtect t d (hDep) (hGRBS d hDep) hPerturbs))

/--
Two-sided characterization of assurance transfer.

Necessity comes from the existing R1 kernel.
Sufficiency comes from transfer_of_grbs.
-/
theorem transfer_iff_grbs
    (hExploit :
      Exploitability F g s b l)
    (hDependence :
      Dependence F g s b l)
    (hComplete :
      ViolationComplete (F := F) (g := g) (s := s) (b := b))
    (hProtect :
      CoveredProtects (F := F) (g := g) (s := s) (b := b) (l := l)) :
    Transfer F g s b ↔ GRBS F g s b l := by
  constructor
  · intro hTransfer
    exact covered_of_transfer F g s b l
      hExploit hDependence hTransfer

  · intro hGRBS
    exact transfer_of_grbs
      hGRBS hComplete hProtect

end GRBS

