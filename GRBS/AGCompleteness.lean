import GRBS

namespace GRBS
namespace AGCompleteness

/--
R3c: an unrestricted physical AG assumption.

Unlike AGBypass, this observation model is not restricted to the
software interface. It receives the same admissible environments and
composite traces used by DARM's semantic Transfer predicate.

It deliberately contains no `cov` or `GRBS` parameter.
-/
def PhysicalAG
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (A : F.Environment → Prop) : Prop :=
  ∀ e, F.Envs b e → A e →
    ∀ t, F.Traces s e b t → F.Safe g t

/--
If the AG assumption holds for every environment admitted by the
DARM boundary, physical AG establishes the same semantic Transfer
judgment used by DARM.
-/
theorem physicalAG_implies_transfer
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (A : F.Environment → Prop)
    (hA :
      ∀ e, F.Envs b e → A e)
    (hAG : PhysicalAG F g s b A) :
    Transfer F g s b := by
  intro e hEnv t hTrace
  exact hAG e hEnv (hA e hEnv) t hTrace

/--
R3c completeness route.

If physical AG establishes Transfer, and the existing DARM seams
Exploitability and Dependence hold, then the existing R1 theorem
recovers GRBS.

This theorem deliberately does not add `GRBS` or `cov` to the AG
premise. It tests whether sufficiently strong physical behavioral
reasoning can recover the same coverage conclusion indirectly.
-/
theorem physicalAG_implies_grbs
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (l : F.Locus)
    (A : F.Environment → Prop)
    (hA :
      ∀ e, F.Envs b e → A e)
    (hAG : PhysicalAG F g s b A)
    (hExploit : Exploitability F g s b l)
    (hDependence : Dependence F g s b l) :
    GRBS F g s b l := by
  exact covered_of_transfer F g s b l
    hExploit
    hDependence
    (physicalAG_implies_transfer F g s b A hA hAG)

#print axioms GRBS.AGCompleteness.physicalAG_implies_transfer
#print axioms GRBS.AGCompleteness.physicalAG_implies_grbs

namespace Behavioral

/--
The weakest direct behavioral AG assumption for the fixed system,
boundary, and guarantee: every trace produced against an environment
is safe.

It contains no dependency, coverage, authority, or mediation predicate.
-/
def SafeTraceAssumption
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary) :
    F.Environment → Prop :=
  fun e =>
    ∀ t, F.Traces s e b t → F.Safe g t

/--
The direct behavioral AG assumption is sufficient for Transfer when it
holds for every admissible environment.
-/
theorem safeTraceAssumption_implies_transfer
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (hA :
      ∀ e, F.Envs b e → SafeTraceAssumption F g s b e) :
    Transfer F g s b := by
  intro e hEnv t hTrace
  exact hA e hEnv t hTrace

/--
Transfer itself supplies the direct behavioral AG assumption for every
admissible environment.
-/
theorem transfer_implies_safeTraceAssumption
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary)
    (hTransfer : Transfer F g s b) :
    ∀ e, F.Envs b e → SafeTraceAssumption F g s b e := by
  intro e hEnv t hTrace
  exact hTransfer e hEnv t hTrace

/--
Characterization: the direct behavioral AG assumption is equivalent to
the semantic Transfer judgment.

No coverage predicate occurs in either direction.
-/
theorem safeTraceAssumption_iff_transfer
    (F : Frame)
    (g : F.Guarantee)
    (s : F.System)
    (b : F.Boundary) :
    (∀ e, F.Envs b e → SafeTraceAssumption F g s b e) ↔
      Transfer F g s b := by
  constructor
  · exact safeTraceAssumption_implies_transfer F g s b
  · exact transfer_implies_safeTraceAssumption F g s b

end Behavioral

end AGCompleteness
end GRBS
