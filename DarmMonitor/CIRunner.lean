import DarmMonitor.LLMToolCall

/-
  CIRunner — second instantiation of the discrete stratum.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHY A SECOND ONE. `LLMToolCall` showed the discrete stratum transfers, but
  its permission map `toolScope` is INJECTIVE — five tools onto five distinct
  scopes. That leaves open whether anything quietly relied on injectivity.

  Here the map is deliberately many-to-one: `lint` and `unitTest` both consume
  `readRepo`; `deploy` and `rollback` both consume `prodAccess`. If the
  inherited theorems still apply, capability gating does not depend on a
  bijection between actions and permissions.

  It also surfaces an EXPRESSIVENESS LIMIT that the first instantiation could
  not: see `deploy_rollback_inseparable` below. Actions sharing a permission
  cannot be separated by the capability channel at all.

  A typeclass extracted from these two instances would be extraction rather
  than invention. That was the point of building a second one before Step 3.
-/

namespace DARM
namespace CIRunner

/-! ## 1. The concrete types -/

/-- Jobs a CI runner may execute. -/
inductive Job
  | lint
  | unitTest
  | integrationTest
  | deploy
  | rollback
deriving DecidableEq, Repr

/-- Permissions. Deliberately coarser than the job set. -/
inductive Perm
  | readRepo
  | writeArtifacts
  | prodAccess
deriving DecidableEq, Repr

/-- Maintainer approval for widening the job set. -/
inductive Signoff
  | none
  | maintainer
deriving DecidableEq, Repr

/-- **Non-injective permission map.** Two jobs share `readRepo`, two share
    `prodAccess`. This is the structural difference from `LLMToolCall`. -/
def jobPerm : Job → Perm
  | .lint             => .readRepo
  | .unitTest         => .readRepo
  | .integrationTest  => .writeArtifacts
  | .deploy           => .prodAccess
  | .rollback         => .prodAccess

def validSignoff (t : Signoff) : Prop := t = Signoff.maintainer

instance : DecidablePred validSignoff := by
  intro t
  unfold validSignoff
  infer_instance

/-- **The deployment bound.** A pull-request runner: it may read the repo and
    write build artifacts. It has no production access. -/
def prGrant : Finset Perm := {Perm.readRepo, Perm.writeArtifacts}

abbrev CIState := State Perm Job
abbrev CIEvent := Event Perm Job Signoff

abbrev ciStep : CIState → CIEvent → CIState :=
  step jobPerm prGrant validSignoff

/-! ## 2. Inherited guarantees — unchanged despite non-injectivity

  Identical applications to the `LLMToolCall` versions, with a many-to-one
  permission map substituted. No proof content. -/

theorem job_perm_confined
    (s : CIState) (j : Job)
    (hCap : capInvariant prGrant s)
    (hExec : canExecute jobPerm s j) :
    jobPerm j ∈ prGrant :=
  execution_confined_by_cap_bound
    (requires := jobPerm) (allowedCapLimit := prGrant)
    (s := s) (a := j) (hCap := hCap) (hExec := hExec)

theorem runner_cannot_widen_jobs
    (s : CIState) (e : CIEvent) (hAgent : actor e = Actor.agent) :
    (ciStep s e).policy ⊆ s.policy :=
  step_agent_policy_monotone
    (requires := jobPerm) (allowedCapLimit := prGrant)
    (validToken := validSignoff) (s := s) (e := e) (hAgent := hAgent)

/-! ## 3. Negative results for this deployment -/

/-- A PR runner provably cannot deploy. -/
theorem deploy_never_executable
    (s : CIState) (hCap : capInvariant prGrant s) :
    ¬ canExecute jobPerm s Job.deploy := by
  intro hExec
  have h : jobPerm Job.deploy ∈ prGrant := job_perm_confined s Job.deploy hCap hExec
  simp [jobPerm, prGrant] at h

/-- Nor roll back — same permission, same conclusion. -/
theorem rollback_never_executable
    (s : CIState) (hCap : capInvariant prGrant s) :
    ¬ canExecute jobPerm s Job.rollback := by
  intro hExec
  have h : jobPerm Job.rollback ∈ prGrant := job_perm_confined s Job.rollback hCap hExec
  simp [jobPerm, prGrant] at h

/-- The runner cannot grant itself production access. -/
theorem cannot_self_grant_prod (s : CIState) :
    (ciStep s (Event.autonomousExpandCap Perm.prodAccess)).cap = s.cap := by
  simp [ciStep, step, prGrant]

/-! ## 4. The expressiveness limit — new, and only visible here

  This is what the non-injective map exposes and the first instantiation
  could not. -/

/-- **Permissions cannot separate jobs that share one.**

    `deploy` and `rollback` both consume `prodAccess`. Executability is
    membership in the policy conjoined with holding the required permission,
    and the requirement is identical for both. So for any state permitting
    both jobs, either both are executable or neither is. No assignment of
    capabilities distinguishes them.

    CONSEQUENCE FOR DEPLOYMENT DESIGN. "Allow rollback but not deploy" — a
    reasonable and common incident-response posture — is NOT expressible
    through the capability channel. It can only be expressed through `policy`,
    which agent events can shrink but only ratification can widen. So the
    coarseness of the permission lattice pushes that decision onto the human
    channel, which is exactly the channel `Ratification.lean` shows is the
    sole coherence-breaking transition.

    This is a limitation of the model as specified, not a defect in the
    proofs. Making it expressible would require `requires` to return a set of
    permissions, or an explicit per-action permission relation. -/
theorem deploy_rollback_inseparable
    (s : CIState)
    (hd : Job.deploy ∈ s.policy) (hr : Job.rollback ∈ s.policy) :
    canExecute jobPerm s Job.deploy ↔ canExecute jobPerm s Job.rollback := by
  unfold canExecute allowedActions
  split
  · simp only [Finset.mem_filter, jobPerm]
    exact ⟨fun h => ⟨hr, h.2⟩, fun h => ⟨hd, h.2⟩⟩
  · simp only [Finset.mem_filter, jobPerm]
    exact ⟨fun h => ⟨hr, h.2⟩, fun h => ⟨hd, h.2⟩⟩
  · simp
  · simp
  · simp

/-! ## 5. What this instantiation establishes

  1. Capability gating does NOT depend on the permission map being injective.
     Every inherited theorem applies unchanged with a many-to-one map.

  2. The permission lattice's granularity is a hard limit on what the
     capability channel can express. Jobs sharing a permission are
     capability-indistinguishable, so any policy requiring finer separation
     must route through ratification.

  3. Two independent instances now exist, so a `ReferenceMonitor` typeclass
     can be extracted from their shared structure rather than guessed at.
     What they actually share: `requires`, `allowedCapLimit`, a validity
     predicate on approval artifacts, and nothing else. Notably NOT
     noninterference, which is false in the base model
     (`Interference.not_noninterfering_basic`) and would render any class
     containing it uninhabited.

  UNINSTANTIATED, as in `LLMToolCall`: the entire continuous stratum. A CI
  runner has no conserved multiplicatively-updated authority measure either.
  Two out of two instantiations reject it, which strengthens the reading that
  the continuous stratum is domain-specific rather than general.
-/

end CIRunner
end DARM

#print axioms DARM.CIRunner.job_perm_confined
#print axioms DARM.CIRunner.runner_cannot_widen_jobs
#print axioms DARM.CIRunner.deploy_never_executable
#print axioms DARM.CIRunner.rollback_never_executable
#print axioms DARM.CIRunner.cannot_self_grant_prod
#print axioms DARM.CIRunner.deploy_rollback_inseparable
