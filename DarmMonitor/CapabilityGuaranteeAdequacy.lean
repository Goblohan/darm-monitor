import DarmMonitor.BehavioralTransitionDARM
import DarmMonitor.TrajectoryGuaranteeAdequacy
import DarmMonitor.TrajectorySafety

namespace DARM

variable {CapId ActionId Token : Type}
  [DecidableEq CapId]
  [DecidableEq ActionId]
  [DecidableEq Token]

/--
The list of all prefixes of a finite event trace, including the empty
prefix and the complete trace.
-/
def tracePrefixes :
    List (Event CapId ActionId Token) →
      List (List (Event CapId ActionId Token))
  | [] => [[]]
  | e :: es =>
      [] :: (tracePrefixes es).map (List.cons e)

/--
Every member of `tracePrefixes es` is an actual prefix of `es`.
-/
theorem tracePrefix_is_prefix
    (es pre : List (Event CapId ActionId Token))
    (hPre : pre ∈ tracePrefixes es) :
    ∃ suf, es = pre ++ suf := by
  induction es generalizing pre with
  | nil =>
      simp [tracePrefixes] at hPre
      subst pre
      exact ⟨[], rfl⟩
  | cons e es ih =>
      simp only [tracePrefixes, List.mem_cons, List.mem_map] at hPre
      cases hPre with
      | inl hEmpty =>
          subst pre
          exact ⟨e :: es, by simp⟩
      | inr hMapped =>
          obtain ⟨pre', hPre', hEq⟩ := hMapped
          subst pre
          obtain ⟨suf, hSuffix⟩ := ih pre' hPre'
          exact ⟨suf, by simp [hSuffix]⟩

/--
Authorization behavior observed along every prefix of a finite trace.
Each element records the actions currently authorized by the
reference monitor at that prefix.
-/
def authorizationTrajectory
    (reqs : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (s : State CapId ActionId)
    (es : List (Event CapId ActionId Token)) :
    List (Finset ActionId) :=
  (tracePrefixes es).map
    (fun pre =>
      authorizationObservation reqs
        (pre.foldl
          (step reqs allowedCapLimit validToken)
          s))

/--
The execution representation preserves authorization behavior at
every prefix of the same event trace.

This combines concrete transition congruence with adequacy of the
execution representation for the authorization observation.
-/
theorem executionRepresentation_authorizationTrajectory_preserved
    (reqs : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    {s₁ s₂ : State CapId ActionId}
    (hRep : RepresentationEq executionRepresentation s₁ s₂) :
    authorizationTrajectory
      reqs allowedCapLimit validToken s₁ es =
    authorizationTrajectory
      reqs allowedCapLimit validToken s₂ es := by
  unfold authorizationTrajectory
  apply List.map_congr_left
  intro pre hPre
  exact executionRepresentation_traceAuthorizationAdequacy
    reqs allowedCapLimit validToken pre hRep

/--
An ungranted action is absent from every authorization observation
in a trajectory.
-/
def neverAuthorizedInTrajectory
    (a : ActionId)
    (authorizationTrace : List (Finset ActionId)) : Prop :=
  ∀ actions ∈ authorizationTrace, a ∉ actions

/--
An ungranted action is excluded from every authorization observation
along a finite pure-agent trajectory satisfying the initial
capability invariant.
-/
theorem neverAuthorizedInTrajectory_of_neverExecutable
    (reqs : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (es : List (Event CapId ActionId Token))
    (s : State CapId ActionId)
    (a : ActionId)
    (hCap : capInvariant allowedCapLimit s)
    (hAgent : AgentTrace es)
    (hUngranted : reqs a ∉ allowedCapLimit) :
    neverAuthorizedInTrajectory
      a
      (authorizationTrajectory
        reqs allowedCapLimit validToken s es) := by
  intro actions hActions

  unfold authorizationTrajectory at hActions
  simp only [List.mem_map] at hActions

  obtain ⟨pre, hPre, hActionsEq⟩ := hActions
  subst actions

  have hPrefix :
      ∃ suf, es = pre ++ suf :=
    tracePrefix_is_prefix es pre hPre

  obtain ⟨suf, hDecomp⟩ := hPrefix

  have hNeverExecutable :
      ¬ canExecute reqs
          (pre.foldl
            (step reqs allowedCapLimit validToken)
            s) a :=
    trace_prefixes_never_executable_of_ungranted
      reqs
      allowedCapLimit
      validToken
      es
      s
      hCap
      hAgent
      a
      hUngranted
      pre
      suf
      hDecomp

  intro hAuthorized

  exact hNeverExecutable hAuthorized

/--
The capability-confinement guarantee is invariant under the execution
representation for any fixed trace and action.

The guarantee is expressed through the authorization trajectory.
The underlying capability-confinement result remains an independent
DARM safety theorem.
-/
theorem executionRepresentation_capabilityTrajectory_adequate
    (reqs : ActionId → CapId)
    (allowedCapLimit : Finset CapId)
    (validToken : Token → Prop)
    [DecidablePred validToken]
    (a : ActionId) :
    TrajectoryGuaranteeAdequate
      executionRepresentation
      (fun s trace =>
        neverAuthorizedInTrajectory
          a
          (authorizationTrajectory
            reqs allowedCapLimit validToken s trace)) := by
  apply trajectoryGuaranteeAdequate_of_behaviorallyAdequate
    (G :=
      fun s trace =>
        neverAuthorizedInTrajectory
          a
          (authorizationTrajectory
            reqs allowedCapLimit validToken s trace))
    (Q :=
      fun behavior =>
        neverAuthorizedInTrajectory a behavior)
  · intro s₁ s₂ trace hRep
    exact executionRepresentation_authorizationTrajectory_preserved
      reqs allowedCapLimit validToken trace hRep
  · intro s trace
    rfl

end DARM

#print axioms DARM.tracePrefix_is_prefix
#print axioms DARM.executionRepresentation_authorizationTrajectory_preserved
#print axioms DARM.neverAuthorizedInTrajectory_of_neverExecutable
#print axioms DARM.executionRepresentation_capabilityTrajectory_adequate
