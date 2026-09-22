/-
  K3a — KERNEL CORRESPONDENCE TO E17 AND E18 (stratum S2 -> S1)

  Proves how the K1 decision kernel relates to the E17 gate and the E18
  ODATS failure classifier. Findings, each stated as a theorem:

    * Admission agrees with E18 whenever argument provenance is trusted.
    * Diagnosis can DIFFER: the kernel checks T first, E18 checks O first,
      so multi-failure inputs get different first-failure labels.
    * Provenance (P) strictly extends ODATS: some input E18 admits, the
      kernel rejects.
    * Domain completeness (D) is ASSUMED by the kernel, never checked.
    * On E17's whole proposal space, the kernel decides exactly as E17's
      gate, and the kernel-gated step inherits E17's safety theorem.

  NOT covered: E15's causal lift, which rests on causal coverage and
  hence on TMC. The kernel does not and cannot refine it.
-/
import K1DecisionKernel
import GRBS.E18AssuranceFailureWitness

namespace GRBS.K3aKernelCorrespondence

open DARM.Kernel
open GRBS.E18AssuranceFailureWitness (evaluateTransfer ODATSCheck TransferResult FailureKind)
open GRBS.E17ProposalAuthoritySeparation
  (Proposal St resolve authorized step G GatedStep gated_step_preserves_safety)

/-! ## E18 -/

/-- The failure kind reported by an E18 result; `none` means admitted. -/
def resultKind : TransferResult → Option FailureKind
  | .admitted => none
  | .rejected w => some w.kind

/-- Translate a kernel request into E18's five ODATS flags.
    D is set to true: the kernel assumes domain completeness. -/
def toODATS (pol : Policy) (cred : Credential) (inv : Invocation) : ODATSCheck :=
  { observationHolds := toolKnown pol inv.tool
    domainHolds := true
    authorityHolds := cred.tools.contains inv.tool
    freshnessHolds := !cred.expired
    semanticHolds := argsAllowed pol inv }

theorem domain_is_assumed (pol : Policy) (cred : Credential) (inv : Invocation) :
    (toODATS pol cred inv).domainHolds = true := rfl

/-- E18 admits exactly when all five flags hold (independent of check order). -/
theorem e18_admits_iff (c : ODATSCheck) :
    resultKind (evaluateTransfer c) = none ↔
      c.observationHolds = true ∧ c.domainHolds = true ∧ c.authorityHolds = true ∧
      c.freshnessHolds = true ∧ c.semanticHolds = true := by
  rcases c with ⟨o, d, a, f, s⟩
  cases o <;> cases d <;> cases a <;> cases f <;> cases s <;>
    simp [evaluateTransfer, resultKind]

/-- With trusted provenance, the kernel and E18 agree on admission. -/
theorem kernel_admits_iff_e18_admits (pol : Policy) (cred : Credential)
    (inv : Invocation) (hTrusted : argsTrusted inv = true) :
    kernelDecide pol cred inv = Decision.admit ↔
      resultKind (evaluateTransfer (toODATS pol cred inv)) = none := by
  rw [kernel_admit_iff, admissible_iff, e18_admits_iff]
  simp [toODATS, hTrusted] <;> constructor <;> intro h <;> simp_all

/-! ## Findings, as kernel-checked witnesses -/

def expiredCred : Credential := { tools := ["file_read"], expired := true }

def unknownTool : Invocation :=
  { tool := "code_exec",
    args := [{ key := "cmd", value := "ls", prov := Provenance.authoritative }] }

/-- Diagnosis order differs: for an expired credential AND an unknown tool,
    the kernel reports temporal (T first), E18 reports observation (O first). -/
theorem diagnosis_order_differs :
    kernelDecide examplePolicy expiredCred unknownTool =
        Decision.reject Failure.temporal ∧
    resultKind (evaluateTransfer (toODATS examplePolicy expiredCred unknownTool)) =
        some FailureKind.observation := by
  constructor <;> decide +kernel

/-- Provenance strictly extends ODATS: E18 admits this invocation,
    the kernel rejects it as a provenance failure. -/
theorem provenance_extends_odats :
    resultKind (evaluateTransfer (toODATS examplePolicy exampleCred injectedRead)) = none ∧
    kernelDecide examplePolicy exampleCred injectedRead =
        Decision.reject Failure.provenance := by
  constructor <;> decide +kernel

/-! ## E17: the kernel on E17's whole proposal space -/

def e17Tool : Proposal → String
  | .readFile => "readFile"
  | .execCode => "execCode"
  | .exfilData => "exfilData"

def e17Invocation (p : Proposal) : Invocation := { tool := e17Tool p, args := [] }

def e17Policy : Policy :=
  { tools := [{ tool := "readFile", rules := [] },
              { tool := "execCode", rules := [] },
              { tool := "exfilData", rules := [] }] }

def e17Cred : Credential := { tools := ["readFile"], expired := false }

/-- For every proposal an agent can generate, the kernel admits exactly
    what E17's gate authorizes. -/
theorem kernel_matches_e17_gate (p : Proposal) :
    kernelDecide e17Policy e17Cred (e17Invocation p) = Decision.admit ↔
      authorized (resolve p) = true := by
  cases p <;> decide +kernel

def kernelGatedStep (p : Proposal) (s : St) : St :=
  if kernelDecide e17Policy e17Cred (e17Invocation p) = Decision.admit
  then step s (resolve p) else s

theorem kernelGatedStep_eq_e17 (p : Proposal) (s : St) :
    kernelGatedStep p s = GatedStep p s := by
  cases p <;> cases s <;> decide +kernel

/-- E17's safety theorem transfers to the kernel-gated system. -/
theorem kernel_gate_preserves_e17_safety (s : St) (hs : G s) (p : Proposal) :
    G (kernelGatedStep p s) := by
  rw [kernelGatedStep_eq_e17]
  exact gated_step_preserves_safety s hs p

end GRBS.K3aKernelCorrespondence

#print axioms GRBS.K3aKernelCorrespondence.kernel_admits_iff_e18_admits
#print axioms GRBS.K3aKernelCorrespondence.diagnosis_order_differs
#print axioms GRBS.K3aKernelCorrespondence.provenance_extends_odats
#print axioms GRBS.K3aKernelCorrespondence.kernel_matches_e17_gate
#print axioms GRBS.K3aKernelCorrespondence.kernel_gate_preserves_e17_safety
