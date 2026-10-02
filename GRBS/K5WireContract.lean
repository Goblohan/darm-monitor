/-
  K5 — THE WIRE CONTRACT BETWEEN THE KERNEL AND THE BROKER

  The released kernel (darmkernel) is K4DecisionServer compiled: each request
  line is parsed and decided by DARM.Kernel4.kernelDecide, the definition the
  K-series theorems are about, and the decision is rendered by decisionJson4.
  The broker (Darm-Guard's KernelClient.decide) admits if and only if the
  reply's "decision" field is exactly the string "admit"; everything else,
  including malformed replies, timeouts and a dead kernel, is a rejection.
  pyAdmits mirrors that rule.

  Proved: every reply is the kernel's decision on the parsed request, or an
  error rejection (reply_cases); rendered decisions read back exactly
  (admit_decodes, reject_decodes, reject_failure_decodes, and failure names
  are injective); an error reply never reads as admit, whatever its text
  (error_decodes); hence if the broker reads admit, the line parsed into a
  request that kernelDecide admitted (admit_only_by_kernel), and conversely
  (kernel_admit_reaches_python).

  Trusted, and NOT proved: the Lean compiler and runtime; Lean's Json.parse and
  the derived FromJson instances (what a line parses to); the I/O loop; Python's
  json.loads; and that pyAdmits mirrors KernelClient.decide (a finite contract,
  tested exhaustively in Darm-Guard). Not covered here: that the request the
  broker encodes is the invocation it means (the encoding side).
-/
import K4DecisionServer

open Lean

namespace DARM.K5

/-- The broker's reading of a reply: admitted iff "decision" is exactly "admit". -/
def pyAdmits (j : Json) : Bool :=
  match j.getObjVal? "decision" with
  | .ok (.str s) => s == "admit"
  | _ => false

/-- The failure class the broker reports for a rejection. -/
def pyFailure (j : Json) : Option String :=
  match j.getObjVal? "failure" with
  | .ok (.str s) => some s
  | _ => none

/-- The server's reply when a line does not parse into a request. -/
def errorJson (e : String) : Json :=
  Json.mkObj [("decision", Json.str "reject"), ("error", Json.str e)]

/-- Every reply is the kernel's decision on the parsed request, or an error rejection. -/
theorem reply_cases (line : String) :
    (∃ req, (Json.parse line >>= fromJson? : Except String KernelRequest4) = .ok req ∧
        handleLine4 line =
          decisionJson4 (DARM.Kernel4.kernelDecide req.policy req.credential req.invocation)) ∨
    ∃ e, handleLine4 line = errorJson e := by
  unfold handleLine4
  cases h : (Json.parse line >>= fromJson? : Except String KernelRequest4) with
  | ok req => exact Or.inl ⟨req, rfl, rfl⟩
  | error e => exact Or.inr ⟨e, rfl⟩

theorem admit_decodes : pyAdmits (decisionJson4 .admit) = true := by rfl

theorem reject_decodes (f : DARM.Kernel.Failure) :
    pyAdmits (decisionJson4 (.reject f)) = false := by
  cases f <;> rfl

theorem reject_failure_decodes (f : DARM.Kernel.Failure) :
    pyFailure (decisionJson4 (.reject f)) = some (failureName4 f) := by
  cases f <;> rfl

theorem failureName4_injective : Function.Injective failureName4 := by
  intro a b h
  cases a <;> cases b <;> simp_all [failureName4]

/-- An error reply never reads as admit, whatever the error says. -/
theorem error_decodes (e : String) : pyAdmits (errorJson e) = false := by rfl

/-- If the broker reads admit, the line parsed into a request and the proved
    kernelDecide admitted it. -/
theorem admit_only_by_kernel (line : String) (h : pyAdmits (handleLine4 line) = true) :
    ∃ req, (Json.parse line >>= fromJson? : Except String KernelRequest4) = .ok req ∧
      DARM.Kernel4.kernelDecide req.policy req.credential req.invocation = .admit := by
  rcases reply_cases line with ⟨req, hp, hr⟩ | ⟨e, hr⟩
  · refine ⟨req, hp, ?_⟩
    rw [hr] at h
    cases hd : DARM.Kernel4.kernelDecide req.policy req.credential req.invocation with
    | admit => rfl
    | reject f =>
      rw [hd, reject_decodes] at h
      exact absurd h (by decide)
  · rw [hr, error_decodes] at h
    exact absurd h (by decide)

/-- Conversely, what the kernel admits, the broker reads as admitted. -/
theorem kernel_admit_reaches_python (line : String) (req : KernelRequest4)
    (hp : (Json.parse line >>= fromJson? : Except String KernelRequest4) = .ok req)
    (hk : DARM.Kernel4.kernelDecide req.policy req.credential req.invocation = .admit) :
    pyAdmits (handleLine4 line) = true := by
  have hr : handleLine4 line =
      decisionJson4 (DARM.Kernel4.kernelDecide req.policy req.credential req.invocation) := by
    unfold handleLine4
    rw [hp]
  rw [hr, hk]
  exact admit_decodes

end DARM.K5

#print axioms DARM.K5.reply_cases
#print axioms DARM.K5.error_decodes
#print axioms DARM.K5.failureName4_injective
#print axioms DARM.K5.admit_only_by_kernel
#print axioms DARM.K5.kernel_admit_reaches_python
