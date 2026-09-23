/-
  K3b — KERNEL CORRESPONDENCE TO R22 (stratum S2 -> S1)

  R22 proves that DARM Guard v0.1's tool-name observation collapses
  demo(0) and demo(1), and that no tool-name-only authorizer is
  semantically correct. K3b proves the K1 kernel escapes that class:

    * On R22's canonical pair, the kernel separates the two calls,
      in agreement with R22's semanticAuthorized.
    * No function of the tool name alone reproduces the kernel's decisions.

  Scope: the general refinement (K3b-G, below) holds for every tool and
  every numeric argument, via Mathlib's Nat.repr_inj. R22's predicate
  ignores the tool, so the biconditional holds only on the governed tool;
  elsewhere the kernel is strictly more conservative (false rejects only).
  The embedding labels R22 arguments as authoritative (R22 has no
  provenance). E15's causal lift is out of scope (rests on TMC).
-/
import K1DecisionKernel
import R22RuntimeImplementationCorrespondence

namespace GRBS.K3bKernelR22

open DARM.Kernel
open GRBS.R22RuntimeImplementationCorrespondence
  (RuntimeInvocation currentRuntimeRequest semanticAuthorized
   current_runtime_observation_collapses_semantic_distinction
   collapsed_invocations_have_different_semantic_authority)

/-- Embed an R22 invocation (tool + numeric argument) as a kernel invocation. -/
def embed (r : RuntimeInvocation) : Invocation :=
  { tool := r.tool,
    args := [{ key := "argument", value := toString r.argument,
               prov := Provenance.authoritative }] }

def r22Policy : Policy :=
  { tools := [{ tool := "demo",
                rules := [{ key := "argument", allowedValues := ["0"],
                            allowedPrefixes := [] }] }] }

def r22Cred : Credential := { tools := ["demo"], expired := false }

def r0 : RuntimeInvocation := { tool := "demo", argument := 0 }
def r1 : RuntimeInvocation := { tool := "demo", argument := 1 }

theorem kernel_admits_r0 :
    kernelDecide r22Policy r22Cred (embed r0) = Decision.admit := by
  decide +kernel

theorem kernel_rejects_r1 :
    kernelDecide r22Policy r22Cred (embed r1) = Decision.reject Failure.semantic := by
  decide +kernel

/-- R22's collapsed pair: identical to v0.1, semantically different,
    and separated by the kernel in agreement with R22. -/
theorem kernel_separates_r22_collapsed_pair :
    currentRuntimeRequest r0 = currentRuntimeRequest r1 ∧
    semanticAuthorized r0 ∧ ¬ semanticAuthorized r1 ∧
    kernelDecide r22Policy r22Cred (embed r0) = Decision.admit ∧
    kernelDecide r22Policy r22Cred (embed r1) = Decision.reject Failure.semantic :=
  ⟨current_runtime_observation_collapses_semantic_distinction,
   collapsed_invocations_have_different_semantic_authority.1,
   collapsed_invocations_have_different_semantic_authority.2,
   kernel_admits_r0, kernel_rejects_r1⟩

/-- The kernel is not a tool-name authorizer: no function of the tool name
    alone reproduces its decisions. This is the class R22 proves insufficient. -/
theorem kernel_not_tool_name_factorizable :
    ¬ ∃ f : String → Decision, ∀ r : RuntimeInvocation,
        kernelDecide r22Policy r22Cred (embed r) = f r.tool := by
  rintro ⟨f, hf⟩
  have h0 := hf r0
  have h1 := hf r1
  rw [kernel_admits_r0] at h0
  rw [kernel_rejects_r1] at h1
  have htool : r0.tool = r1.tool := rfl
  have hbad : Decision.admit = Decision.reject Failure.semantic := by
    rw [h0, h1, htool]
  cases hbad

end GRBS.K3bKernelR22

#print axioms GRBS.K3bKernelR22.kernel_separates_r22_collapsed_pair
#print axioms GRBS.K3bKernelR22.kernel_not_tool_name_factorizable

/-! ## K3b-G: the general refinement, for every tool and every argument -/

namespace GRBS.K3bKernelR22

open DARM.Kernel
open GRBS.R22RuntimeImplementationCorrespondence (RuntimeInvocation semanticAuthorized)

/-- The kernel admits embed(tool, arg) exactly when tool = "demo" and arg = 0. -/
theorem kernel_embed_admit_iff (tool : String) (arg : Nat) :
    kernelDecide r22Policy r22Cred (embed ⟨tool, arg⟩) = Decision.admit ↔
      tool = "demo" ∧ arg = 0 := by
  rw [kernel_admit_iff]
  by_cases ht : tool = "demo"
  · subst ht
    simp [admissible, toolKnown, findTool, argsAllowed, argsTrusted, argAllowed,
          ruleAllows, embed, r22Policy, r22Cred]
    constructor
    · intro h
      have h0 : arg.repr = (0 : Nat).repr := h.trans (by decide +kernel)
      exact Nat.repr_inj.mp h0
    · intro h
      subst h
      decide +kernel
  · simp [admissible, toolKnown, findTool, argsAllowed, argsTrusted,
          embed, r22Policy, r22Cred, ht, Ne.symm ht]

/-- Soundness, for every invocation: kernel admission implies R22 authorization. -/
theorem k3b_sound (r : RuntimeInvocation)
    (h : kernelDecide r22Policy r22Cred (embed r) = Decision.admit) :
    semanticAuthorized r := by
  rcases r with ⟨tool, arg⟩
  exact ((kernel_embed_admit_iff tool arg).mp h).2

/-- Completeness on the governed tool. -/
theorem k3b_complete_on_governed_tool (r : RuntimeInvocation)
    (ht : r.tool = "demo") (hs : semanticAuthorized r) :
    kernelDecide r22Policy r22Cred (embed r) = Decision.admit := by
  rcases r with ⟨tool, arg⟩
  exact (kernel_embed_admit_iff tool arg).mpr ⟨ht, hs⟩

/-- The kernel never admits anything R22 forbids. -/
theorem k3b_no_false_admits :
    ¬ ∃ r : RuntimeInvocation,
        kernelDecide r22Policy r22Cred (embed r) = Decision.admit ∧
        ¬ semanticAuthorized r := by
  rintro ⟨r, hAdmit, hNot⟩
  exact hNot (k3b_sound r hAdmit)

def rOther : RuntimeInvocation := { tool := "other", argument := 0 }

/-- Where they diverge, the kernel is more conservative: R22 authorizes
    other(0), the kernel rejects an ungoverned tool. -/
theorem k3b_divergence_is_conservative :
    semanticAuthorized rOther ∧
    kernelDecide r22Policy r22Cred (embed rOther) = Decision.reject Failure.observation := by
  constructor
  · rfl
  · decide +kernel

end GRBS.K3bKernelR22

#print axioms GRBS.K3bKernelR22.kernel_embed_admit_iff
#print axioms GRBS.K3bKernelR22.k3b_no_false_admits
#print axioms GRBS.K3bKernelR22.k3b_divergence_is_conservative
