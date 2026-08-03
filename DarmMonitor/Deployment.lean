import DarmMonitor.CIRunner

/-
  Deployment — the reusable content that a `ReferenceMonitor` typeclass was
  meant to provide, extracted without the abstraction.

  STATUS: VERIFIED. See the #print axioms declarations at the end of this file.

  WHY NOT A TYPECLASS. The proposal was:

      class ReferenceMonitor (State Action : Type) where
        capability_gate : ...
        non_interference : ...

  Two objections, the second decisive.

  1. UNINHABITED CLASS. A field asserting noninterference would make the class
     instantiable by nothing. Noninterference is FALSE in this development —
     `Interference.not_noninterfering_basic` proves it fails on the reference
     monitor itself, and `Assumptions.A4_fails_for_modelled_channel` proves it
     fails for the modelled channel. Every theorem quantified over such a class
     would be vacuously true, which is worse than having no theorem.

  2. ONE INSTANCE PER TYPE TRIPLE. A class keyed on `(CapId, ActionId, Token)`
     admits a single instance for those types. Comparing two deployments over
     the same action space — the same permission map under grants `G₁` and `G₂`
     — becomes unstatable. `unreachable_antitone` below is exactly such a
     theorem, and it is the kind a governance calculus most wants: it says
     tightening a grant can only enlarge the set of actions that can never run.
     The class form would forbid stating it.

     Explicit parameters are therefore not merely adequate here but strictly
     more expressive.

  WHAT WAS ACTUALLY MISSING. `LLMToolCall` and `CIRunner` each hand-wrote the
  same negative result twice — four near-identical proofs differing only in
  constants. That duplication is real. The remedy is a general lemma, which is
  what this module supplies. Both instantiations collapse to one-line
  applications of `never_executable_of_ungranted`.
-/

namespace DARM
namespace Deployment

/-! ## 1. The general negative result

  Generalizes `LLMToolCall.bash_never_executable`,
  `LLMToolCall.email_never_executable`, `CIRunner.deploy_never_executable`,
  and `CIRunner.rollback_never_executable`. -/

/-- **An action whose permission was never granted can never execute**, in any
    capability-confined state, whatever the policy says.

    This is the general form of every "provably unreachable action" result in
    the instantiations. -/
theorem never_executable_of_ungranted
    {CapId ActionId : Type} [DecidableEq CapId] [DecidableEq ActionId]
    (requires : ActionId → CapId) (grant : Finset CapId)
    (a : ActionId) (hUngranted : requires a ∉ grant)
    (s : State CapId ActionId) (hCap : capInvariant grant s) :
    ¬ canExecute requires s a := by
  intro hExec
  exact hUngranted
    (execution_confined_by_cap_bound
      (requires := requires) (allowedCapLimit := grant)
      (s := s) (a := a) (hCap := hCap) (hExec := hExec))

/-! ## 2. The unreachable set

  Naming the set makes deployment comparison expressible. -/

/-- Actions that can never execute under this grant, whatever the policy. -/
def unreachable {CapId ActionId : Type} [DecidableEq CapId] [Fintype ActionId]
    (requires : ActionId → CapId) (grant : Finset CapId) : Finset ActionId :=
  Finset.univ.filter (fun a => requires a ∉ grant)

theorem mem_unreachable_iff
    {CapId ActionId : Type} [DecidableEq CapId] [Fintype ActionId]
    (requires : ActionId → CapId) (grant : Finset CapId) (a : ActionId) :
    a ∈ unreachable requires grant ↔ requires a ∉ grant := by
  simp [unreachable]

/-- Membership in `unreachable` delivers the impossibility. -/
theorem not_executable_of_mem_unreachable
    {CapId ActionId : Type} [DecidableEq CapId] [DecidableEq ActionId]
    [Fintype ActionId]
    (requires : ActionId → CapId) (grant : Finset CapId)
    (a : ActionId) (ha : a ∈ unreachable requires grant)
    (s : State CapId ActionId) (hCap : capInvariant grant s) :
    ¬ canExecute requires s a :=
  never_executable_of_ungranted requires grant a
    ((mem_unreachable_iff requires grant a).mp ha) s hCap

/-! ## 3. Deployment comparison — the theorem a typeclass would forbid

  Two grants, one permission map, quantified together. -/

/-- **Tightening a grant can only enlarge what is unreachable.**

    `unreachable` is antitone in the grant: a smaller grant forbids at least as
    much. This is the monotonicity property a deployment operator reasons with
    when narrowing permissions, and it is stated over TWO grants at once —
    which a typeclass keyed on the type triple could not express, since it
    admits only one grant per action space. -/
theorem unreachable_antitone
    {CapId ActionId : Type} [DecidableEq CapId] [Fintype ActionId]
    (requires : ActionId → CapId) (G₁ G₂ : Finset CapId) (h : G₁ ⊆ G₂) :
    unreachable requires G₂ ⊆ unreachable requires G₁ := by
  intro a ha
  rw [mem_unreachable_iff] at ha ⊢
  exact fun hmem => ha (h hmem)

/-- Capability confinement is monotone in the grant: a state confined by a
    tighter bound is confined by a looser one. The dual of the above. -/
theorem capInvariant_mono
    {CapId ActionId : Type}
    (G₁ G₂ : Finset CapId) (h : G₁ ⊆ G₂) (s : State CapId ActionId)
    (hCap : capInvariant G₁ s) : capInvariant G₂ s := by
  unfold capInvariant at hCap ⊢
  exact hCap.trans h

/-! ## 4. The instantiations collapse

  Every hand-written unreachability proof in `LLMToolCall` and `CIRunner` is
  now a one-line application. Kept there as written, since rewriting verified
  files for tidiness is not worth the rebuild — but a THIRD instantiation would
  need no bespoke proofs at all, which was the actual goal of the typeclass
  proposal. -/

example (s : State DARM.LLMToolCall.Scope DARM.LLMToolCall.Tool)
    (hCap : capInvariant DARM.LLMToolCall.granted s) :
    ¬ canExecute DARM.LLMToolCall.toolScope s DARM.LLMToolCall.Tool.bashExec :=
  never_executable_of_ungranted _ _ _ (by decide) s hCap

example (s : State DARM.CIRunner.Perm DARM.CIRunner.Job)
    (hCap : capInvariant DARM.CIRunner.prGrant s) :
    ¬ canExecute DARM.CIRunner.jobPerm s DARM.CIRunner.Job.deploy :=
  never_executable_of_ungranted _ _ _ (by decide) s hCap

/-! ## Registered status

  RESOLVED: the typeclass question. A class is not merely unnecessary but
  strictly less expressive, because it cannot quantify over two deployments
  sharing an action space. `unreachable_antitone` is the witness. The reusable
  content the proposal was after is `never_executable_of_ungranted`, which
  needs no abstraction layer.

  OPEN: whether a bundling STRUCTURE (not class) would reduce instantiation
  boilerplate enough to be worth it. That is an ergonomics question, not a
  mathematical one, and should be decided by writing a third instantiation and
  counting lines — not by argument.
-/

end Deployment
end DARM

#print axioms DARM.Deployment.never_executable_of_ungranted
#print axioms DARM.Deployment.mem_unreachable_iff
#print axioms DARM.Deployment.not_executable_of_mem_unreachable
#print axioms DARM.Deployment.unreachable_antitone
#print axioms DARM.Deployment.capInvariant_mono
