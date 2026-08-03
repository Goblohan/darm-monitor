import DarmMonitor.Interference

/-
  LLMToolCall — the discrete stratum instantiated on an LLM tool-caller.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  PURPOSE. Test whether the abstractions in `Basic.lean` are genuinely reusable
  or merely shaped around their one example. Nothing in this module edits
  existing code; it only instantiates.

  WHAT MAPS. The discrete stratum maps without strain:

      ActionId          ->  tool name
      CapId             ->  API scope / permission
      requires          ->  which scope a tool consumes
      cap               ->  scopes currently held
      policy            ->  tools currently permitted
      allowedCapLimit   ->  scopes granted by the deployment (the TCB bound)
      Token             ->  human approval artifact
      opState           ->  operational status, incl. suspension

  WHAT DOES NOT MAP. The continuous stratum has no referent here. See the
  "UNINSTANTIATED" section at the end of this file. That is reported rather
  than papered over: choosing a weight semantics to make the Z-bound apply
  would be fitting the model to the theorem.

  THE DEPLOYMENT MODELLED. A research assistant granted filesystem-read and
  network access, and NOT granted shell or write or email. The interesting
  results are the negative ones: what such an agent provably cannot do.
-/

namespace DARM
namespace LLMToolCall

/-! ## 1. The concrete types -/

/-- Tools the agent may attempt to invoke. -/
inductive Tool
  | readFile
  | writeFile
  | bashExec
  | httpGet
  | sendEmail
deriving DecidableEq, Repr

/-- API scopes. Each tool consumes exactly one. -/
inductive Scope
  | fsRead
  | fsWrite
  | shell
  | network
  | comms
deriving DecidableEq, Repr

/-- Human approval artifacts. `absent` stands for an unapproved request. -/
inductive Approval
  | absent
  | humanSigned
deriving DecidableEq, Repr

/-- The permission matrix: `requires`, instantiated. -/
def toolScope : Tool → Scope
  | .readFile  => .fsRead
  | .writeFile => .fsWrite
  | .bashExec  => .shell
  | .httpGet   => .network
  | .sendEmail => .comms

/-- Only human-signed approvals are valid. -/
def validApproval (t : Approval) : Prop := t = Approval.humanSigned

instance : DecidablePred validApproval := by
  intro t
  unfold validApproval
  infer_instance

/-- **The deployment bound.** A research assistant: read files, reach the
    network. No shell, no writes, no email. -/
def granted : Finset Scope := {Scope.fsRead, Scope.network}

abbrev LLMState := State Scope Tool
abbrev LLMEvent := Event Scope Tool Approval

/-- The instantiated monitor. -/
abbrev llmStep : LLMState → LLMEvent → LLMState :=
  step toolScope granted validApproval

/-! ## 2. Inherited guarantees

  Each of these is the corresponding theorem from `Basic.lean`, applied. No
  new proof content — that is the point. If the abstraction is real, the
  security properties come across for free. -/

/-- **Scope confinement.** Any tool the monitor will execute consumes a scope
    the deployment granted. Inherited from `execution_confined_by_cap_bound`. -/
theorem tool_scope_confined
    (s : LLMState) (t : Tool)
    (hCap : capInvariant granted s)
    (hExec : canExecute toolScope s t) :
    toolScope t ∈ granted :=
  execution_confined_by_cap_bound
    (requires := toolScope) (allowedCapLimit := granted)
    (s := s) (a := t) (hCap := hCap) (hExec := hExec)

/-- **The agent cannot widen its own tool set.** Inherited from
    `step_agent_policy_monotone`. Widening requires a non-agent event. -/
theorem agent_cannot_widen_tools
    (s : LLMState) (e : LLMEvent) (hAgent : actor e = Actor.agent) :
    (llmStep s e).policy ⊆ s.policy :=
  step_agent_policy_monotone
    (requires := toolScope) (allowedCapLimit := granted)
    (validToken := validApproval) (s := s) (e := e) (hAgent := hAgent)

/-! ## 3. The negative results — what this deployment provably cannot do

  These are the statements a security reviewer actually wants, and they are
  consequences of the gating rather than new assumptions. -/

/-- **Shell execution is unreachable.** `bashExec` consumes `shell`, which the
    deployment did not grant, so no scope-confined state can execute it — no
    matter what the policy says.

    This is the concrete payoff of making `cap` causally live. Before gating,
    `cap` was write-only and this theorem could not be stated. -/
theorem bash_never_executable
    (s : LLMState) (hCap : capInvariant granted s) :
    ¬ canExecute toolScope s Tool.bashExec := by
  intro hExec
  have h : toolScope Tool.bashExec ∈ granted :=
    tool_scope_confined s Tool.bashExec hCap hExec
  simp [toolScope, granted] at h

/-- **Email exfiltration is unreachable**, for the same reason. Stated
    separately because it is the channel a reviewer asks about. -/
theorem email_never_executable
    (s : LLMState) (hCap : capInvariant granted s) :
    ¬ canExecute toolScope s Tool.sendEmail := by
  intro hExec
  have h : toolScope Tool.sendEmail ∈ granted :=
    tool_scope_confined s Tool.sendEmail hCap hExec
  simp [toolScope, granted] at h

/-- **The agent cannot self-grant shell access.** `autonomousExpandCap` is
    bounded by the deployment grant, so attempting to acquire `shell` is a
    no-op on capability. -/
theorem cannot_self_grant_shell (s : LLMState) :
    (llmStep s (Event.autonomousExpandCap Scope.shell)).cap = s.cap := by
  simp [llmStep, step, granted]

/-- **Unapproved widening is a no-op.** A ratification event carrying no
    human signature leaves the state untouched, so the approval channel
    cannot be bypassed by simply omitting the artifact. -/
theorem unapproved_ratification_is_noop (s : LLMState) (p : Finset Tool) :
    llmStep s (Event.authenticatedRatification Approval.absent p) = s := by
  simp [llmStep, step, validApproval]

/-! ## 4. What did NOT instantiate — the continuous stratum

  `BoundaryMargin`, `StratumComposition`, `Ratification`, `StrictExpansion`,
  `NontrivialExpansion`, and `Reachability` all require a weight vector
  `w : ι -> R` with a partition function `Z w = sum of w`, updated
  multiplicatively by `reweight eta loss w i = w i * exp (-eta * loss i)`.

  No such object exists in a tool-caller, and the candidates all fail:

    * MODEL CONFIDENCE. Not conserved, and there is no operational reading of
      `Z` as total confidence. Normalizing confidences to unit mass would make
      the capacity bound `|active| <= 1/delta` a statement about how many tools
      can be simultaneously "confident", which means nothing.

    * RISK BUDGET. Closer — a budget is conserved. But the update rule is
      wrong: `exp(-eta * loss)` is a multiplicative-weights step from online
      learning, and there is no reason a risk budget would evolve that way.
      Adopting it would be assuming the conclusion.

    * NEXT-TOKEN PROBABILITIES. These are distributions over tokens, not over
      tools, and they are recomputed each step rather than reweighted. The
      index type does not even match.

  CONSEQUENCE FOR THE ARCHITECTURE. The delta-margin floor, the O(n) -> O(1)
  collapse, `safe_signal_equiv`, cross-stratum coherence, and the capacity
  bound have NO INTERPRETATION for this deployment. They are not wrong; they
  are about a different kind of system — one where authority is backed by a
  conserved quantity that evolves multiplicatively.

  This is the honest finding of the instantiation: the DISCRETE stratum is a
  general-purpose reference monitor and transfers cleanly. The CONTINUOUS
  stratum is domain-specific and does not. Any claim that DARM as a whole
  applies to LLM tool-calling would be false.

  OPEN. Whether some agent architecture supplies a genuine conserved,
  multiplicatively-updated authority measure — a rate limiter with exponential
  backoff and a fixed global budget is the closest candidate I can name — and
  whether the margin floor then has an operational meaning. Not investigated.
-/

end LLMToolCall
end DARM

#print axioms DARM.LLMToolCall.tool_scope_confined
#print axioms DARM.LLMToolCall.agent_cannot_widen_tools
#print axioms DARM.LLMToolCall.bash_never_executable
#print axioms DARM.LLMToolCall.email_never_executable
#print axioms DARM.LLMToolCall.cannot_self_grant_shell
#print axioms DARM.LLMToolCall.unapproved_ratification_is_noop
