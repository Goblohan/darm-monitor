import E32AuthorizationTransformation

namespace DARM.E32RoleSensitive

open DARM.Kernel
open DARM.Kernel4

/--
A transformation preserves K4 authorization when it preserves the
tool identity and the two authorization-relevant argument predicates.
-/
def AuthorizationRelevantPreserved
    (pol : Kernel4.Policy)
    (inv inv' : Invocation) : Prop :=
  inv'.tool = inv.tool ∧
  Kernel4.argsAllowed pol inv' = Kernel4.argsAllowed pol inv ∧
  Kernel4.selectorsTrusted pol inv' = Kernel4.selectorsTrusted pol inv

/--
For a fixed tool policy, a payload rewrite preserves the
authorization-relevant predicates.
-/
theorem payload_rewrite_authorization_relevant
    (pol : Kernel4.Policy)
    (inv : Invocation)
    (tp : Kernel4.ToolPolicy)
    (newVal : Arg → String)
    (newProv : Arg → Provenance)
    (htp : Kernel4.findTool pol inv.tool = some tp)
    (hrule :
      Kernel4.argsAllowed
        pol
        (Kernel4.rewritePayload tp newVal newProv inv)
      =
      Kernel4.argsAllowed pol inv) :
    AuthorizationRelevantPreserved
      pol
      inv
      (Kernel4.rewritePayload tp newVal newProv inv) := by
  constructor
  · rfl
  · constructor
    · exact hrule
    · exact Kernel4.selectorsTrusted_rewrite
        pol tp newVal newProv inv htp

/--
Authorization-relevant preservation implies K4 admissibility preservation.
-/
theorem admissible_preserved_of_authorization_relevant
    (pol : Kernel4.Policy)
    (cred : Credential)
    (inv inv' : Invocation)
    (h :
      AuthorizationRelevantPreserved pol inv inv') :
    Kernel4.admissible pol cred inv'
      =
    Kernel4.admissible pol cred inv := by
  unfold AuthorizationRelevantPreserved at h
  rcases h with ⟨hTool, hArgs, hSelectors⟩

  unfold Kernel4.admissible
  simp only [hTool, hArgs, hSelectors]

/--
Authorization-relevant preservation implies K4 decision preservation.
-/
theorem decision_preserved_of_authorization_relevant
    (pol : Kernel4.Policy)
    (cred : Credential)
    (inv inv' : Invocation)
    (h :
      AuthorizationRelevantPreserved pol inv inv') :
    Kernel4.kernelDecide pol cred inv'
      =
    Kernel4.kernelDecide pol cred inv := by
  unfold AuthorizationRelevantPreserved at h
  rcases h with ⟨hTool, hArgs, hSelectors⟩

  have hadm :
      Kernel4.admissible pol cred inv'
        =
      Kernel4.admissible pol cred inv := by
    unfold Kernel4.admissible
    simp only [hTool, hArgs, hSelectors]

  have hclass :
      Kernel4.classify pol cred inv'
        =
      Kernel4.classify pol cred inv := by
    unfold Kernel4.classify
    simp only [hTool, hArgs]

  simp only [Kernel4.kernelDecide, hadm, hclass]

/--
Payload provenance relabeling is a concrete E32 role-preserving
authorization transformation.
-/
theorem payload_provenance_preserves_decision
    (pol : Kernel4.Policy)
    (cred : Credential)
    (inv : Invocation)
    (tp : Kernel4.ToolPolicy)
    (newProv : Arg → Provenance)
    (htp : Kernel4.findTool pol inv.tool = some tp) :
    Kernel4.kernelDecide pol cred
        (Kernel4.rewritePayload
          tp
          (fun a => a.value)
          newProv
          inv)
      =
    Kernel4.kernelDecide pol cred inv := by
  exact Kernel4.payload_provenance_irrelevant
    pol cred inv tp newProv htp

end DARM.E32RoleSensitive
