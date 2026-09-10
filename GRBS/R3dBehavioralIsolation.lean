import AGBypass

namespace GRBS
namespace R3dBehavioralIsolation

open AGBypass
open AGBypass.Witness

/--
R3d-3: under the behavioral observation boundary, the two witness
systems are indistinguishable to every admissible AG assumption,
while their GRBS status differs.
-/
theorem behavioral_AG_cannot_recover_latent_coverage
    (A : AGAssumption) :
    (AGSatisfiesAdm A g S1 ↔ AGSatisfiesAdm A g S2) ∧
    (GRBS g S1 ∧ ¬ GRBS g S2) := by
  exact ⟨
    (grbs_isolates_latent_bypass A).1,
    (grbs_isolates_latent_bypass A).2.1
  ⟩

/--
The distinguishing information is outside the behavioral observation:
the bypass is physically exploitable in S2 but absent from the
interface-respecting AG observation.
-/
theorem latent_coverage_is_not_behaviorally_visible
    (A : AGAssumption) :
    (AGSatisfiesAdm A g S1 ↔ AGSatisfiesAdm A g S2) ∧
    (∃ t, S2.physicalStep Ch.d0 t ∧
      ¬ g t ∧ ¬ S2.cov Ch.d0) := by
  exact ⟨
    (grbs_isolates_latent_bypass A).1,
    (grbs_isolates_latent_bypass A).2.2
  ⟩

#print axioms GRBS.R3dBehavioralIsolation.behavioral_AG_cannot_recover_latent_coverage
#print axioms GRBS.R3dBehavioralIsolation.latent_coverage_is_not_behaviorally_visible

end R3dBehavioralIsolation
end GRBS
