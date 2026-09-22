/-
  K3b — KERNEL CORRESPONDENCE TO R22 (stratum S2 -> S1)

  R22 proves that DARM Guard v0.1's tool-name observation collapses
  demo(0) and demo(1), and that no tool-name-only authorizer is
  semantically correct. K3b proves the K1 kernel escapes that class:

    * On R22's canonical pair, the kernel separates the two calls,
      in agreement with R22's semanticAuthorized.
    * No function of the tool name alone reproduces the kernel's decisions.

  Scope: proved on R22's canonical witnesses. The embedding labels
  R22 arguments as authoritative (R22 has no provenance). A version for
  every numeric argument needs a Nat-to-string injectivity lemma and is
  deferred. E15's causal lift is out of scope (rests on TMC).
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
