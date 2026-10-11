/-
E38 conditional support-check refinement. No Python, crypto, issuer honesty, clock,
key custody, pin protection, or end-to-end refinement theorem is asserted.
The eight remaining semantic checks stay named premises, not new axioms.
-/
import E38RelianceNonLaundering
import E38OperationalCore

namespace DARM.E38.Correspondence

open DARM.E38

/-- Remaining E38 obligations after replacing its abstract support check. -/
structure ExternalChecks {S T E W : Type}
    (v : RelianceVerifier S T E W) : Prop where
  source : ∀ s, v.checkSource s = true → v.boundary.source s
  sourceClaim : ∀ s, v.checkSourceClaim s = true → v.boundary.sourceClaim s
  relation : ∀ s t, v.checkRelation s t = true → v.boundary.relates s t
  transfer : ∀ s t, v.checkTransfer s t = true → v.boundary.transferWarrant s t
  target : ∀ t, v.checkTarget t = true → v.boundary.target t
  authenticity : ∀ e, v.checkAuthentic e = true → v.authentic e
  binding : ∀ e t, v.checkBinding e t = true → v.boundToTarget e t
  freshness : ∀ e, v.checkFreshness e = true → v.current e

/-- The operational mapping must justify the ORIGINAL semantic support
    predicate. This obligation is not discharged by redefining that predicate.
    It includes policy interpretation adequacy, not merely key permission. -/
def SupportAdequacy {S T E W : Type}
    (v : RelianceVerifier S T E W)
    (facts : E → List String) (obligations : T → List (List String)) : Prop :=
  ∀ e t, Operational.Supported (facts e) (obligations t) → v.evidenceSupports e t

/-- Replace only the executable support check, preserving semantic predicates.
    Extraction from the runtime is tested, not proved by this definition. -/
def withOperationalSupport {S T E W : Type}
    (v : RelianceVerifier S T E W)
    (facts : E → List String) (obligations : T → List (List String)) :
    RelianceVerifier S T E W :=
  { v with checkSupport := fun e t => Operational.admitRel (facts e) (obligations t) [] }

theorem support_check_sound {S T E W : Type}
    (v : RelianceVerifier S T E W)
    (facts : E → List String) (obligations : T → List (List String))
    (h : ExternalChecks v) (hAdequate : SupportAdequacy v facts obligations) :
    SoundChecks (withOperationalSupport v facts obligations) := by
  refine ⟨h.source, h.sourceClaim, h.relation, h.transfer, h.target,
    h.authenticity, h.binding, h.freshness, ?_⟩
  intro e t hAdmit
  exact hAdequate e t
    (Operational.admitted_implies_supported (facts e) (obligations t) [] hAdmit)

theorem admitted_implies_e37_entitled {S T E W : Type}
    (v : RelianceVerifier S T E W)
    (facts : E → List String) (obligations : T → List (List String))
    (h : ExternalChecks v) (hAdequate : SupportAdequacy v facts obligations)
    (s : S) (t : T) (e : E)
    (ha : admitBool (withOperationalSupport v facts obligations) s t e = true) :
    DARM.E37.Entitled v.boundary t := by
  have hw := admitted_implies_warranted (withOperationalSupport v facts obligations)
    (support_check_sound v facts obligations h hAdequate) s t e ha
  exact hw.2.1

/-- World truth needs a separate explicit adequacy bridge. -/
theorem world_truth_only_with_adequacy {S T E W : Type}
    (v : RelianceVerifier S T E W)
    (facts : E → List String) (obligations : T → List (List String))
    (h : ExternalChecks v) (hAdequate : SupportAdequacy v facts obligations)
    (s : S) (t : T) (e : E) (w : W)
    (ha : admitBool (withOperationalSupport v facts obligations) s t e = true)
    (adequate : Warranted (withOperationalSupport v facts obligations) t e →
      v.worldTrue w t) : v.worldTrue w t := by
  exact adequate (admitted_implies_warranted
    (withOperationalSupport v facts obligations)
    (support_check_sound v facts obligations h hAdequate) s t e ha)

#print axioms support_check_sound
#print axioms admitted_implies_e37_entitled
#print axioms world_truth_only_with_adequacy

end DARM.E38.Correspondence
