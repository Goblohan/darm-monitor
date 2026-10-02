/-
  K6 DECISION SERVER (kernel-v0.3.0)

  The kernel's root executable. It accepts two request forms, one per line:

  new: {"policy", "credential", "registry", "proposal": {"tool", "args": [[k, v], ...]}}
       The kernel computes K6's step itself: wellFormed (no repeated keys;
       path and destination in strict normal form), then B3's canonicalize
       (provenance by B2a's assignProv), then kernelDecide. An admission
       carries the canonical invocation, so the broker executes exactly what
       was decided instead of recomputing it.
  old: {"policy", "credential", "invocation"}, decided exactly as K4DecisionServer
       always has (handleLine4). Any line that is not a valid new-form request
       falls through to it.

  Proved: the malformed reply never reads as admit; if the broker reads admit
  from a new-form reply, k6Step admitted (admit6_only_by_k6) and the reply
  carries exactly the canonical invocation (admit6_returns_canonical); for any
  line of either form, a read admission implies k6Step admitted the parsed
  new-form request or kernelDecide admitted the parsed old-form one
  (admit_only_by_kernel6).

  Trusted, and NOT proved: as K5 (the Lean compiler and runtime, Json.parse and
  the derived FromJson and ToJson instances, the I/O loop, the broker's
  json.loads and its decoder matching pyAdmits); and that the broker executes
  the invocation it decodes from the reply.
-/
import K4DecisionServer
import K5WireContract
import K6KernelCanonicalization

open Lean

deriving instance FromJson for DARM.BrokerDerived.Registry
deriving instance FromJson for DARM.Broker.Proposal
deriving instance ToJson for DARM.Kernel.Provenance
deriving instance ToJson for DARM.Kernel.Arg
deriving instance ToJson for DARM.Kernel.Invocation

structure KernelRequest6 where
  policy : DARM.Kernel4.Policy
  credential : DARM.Kernel.Credential
  registry : DARM.BrokerDerived.Registry
  proposal : DARM.Broker.Proposal
  deriving FromJson

def cfgOf (req : KernelRequest6) : DARM.Broker3.Config :=
  { policy := req.policy, credential := req.credential, registry := req.registry }

/-- An admission carries the invocation that was decided. -/
def replyFor (inv : DARM.Kernel.Invocation) : DARM.Kernel.Decision → Json
  | .admit => Json.mkObj [("decision", Json.str "admit"), ("invocation", toJson inv)]
  | .reject f => decisionJson4 (.reject f)

def malformedJson : Json := DARM.K5.errorJson "malformed proposal"

def handleRequest6 (req : KernelRequest6) : Json :=
  if DARM.K6.wellFormed req.proposal then
    replyFor (DARM.Broker3.canonicalize (cfgOf req) req.proposal)
      (DARM.Kernel4.kernelDecide (cfgOf req).policy (cfgOf req).credential
        (DARM.Broker3.canonicalize (cfgOf req) req.proposal))
  else malformedJson

def handleLine6 (line : String) : Json :=
  match (Json.parse line >>= fromJson? : Except String KernelRequest6) with
  | .ok req => handleRequest6 req
  | .error _ => handleLine4 line

partial def serveLoop6 (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let t := line.trim
  unless t.isEmpty do
    stdout.putStrLn (handleLine6 t).compress
    stdout.flush
  serveLoop6 stdin stdout

def main : IO Unit := do
  serveLoop6 (← IO.getStdin) (← IO.getStdout)

namespace DARM.K6Server

theorem replyFor_admit_decodes (inv : DARM.Kernel.Invocation) :
    DARM.K5.pyAdmits (replyFor inv .admit) = true := by rfl

theorem replyFor_reject_decodes (inv : DARM.Kernel.Invocation) (f : DARM.Kernel.Failure) :
    DARM.K5.pyAdmits (replyFor inv (.reject f)) = false :=
  DARM.K5.reject_decodes f

theorem malformed_decodes : DARM.K5.pyAdmits malformedJson = false :=
  DARM.K5.error_decodes _

/-- A read admission of a new-form reply means k6Step admitted. -/
theorem admit6_only_by_k6 (req : KernelRequest6) (h : DARM.K5.pyAdmits (handleRequest6 req) = true) :
    DARM.K6.k6Step (cfgOf req) req.proposal =
      some (DARM.Broker3.canonicalize (cfgOf req) req.proposal) := by
  unfold handleRequest6 at h
  by_cases hw : DARM.K6.wellFormed req.proposal = true
  · rw [if_pos hw] at h
    unfold DARM.K6.k6Step DARM.Broker3.brokerStep
    rw [if_pos hw]
    cases hd : DARM.Kernel4.kernelDecide (cfgOf req).policy (cfgOf req).credential
        (DARM.Broker3.canonicalize (cfgOf req) req.proposal) with
    | admit => rw [if_pos rfl]
    | reject f =>
      rw [hd, replyFor_reject_decodes] at h
      exact absurd h (by decide)
  · rw [if_neg hw, malformed_decodes] at h
    exact absurd h (by decide)

/-- And the reply carries exactly the canonical invocation. -/
theorem admit6_returns_canonical (req : KernelRequest6)
    (h : DARM.K5.pyAdmits (handleRequest6 req) = true) :
    handleRequest6 req = replyFor (DARM.Broker3.canonicalize (cfgOf req) req.proposal) .admit := by
  have hw : DARM.K6.wellFormed req.proposal = true := by
    by_cases hw : DARM.K6.wellFormed req.proposal = true
    · exact hw
    · unfold handleRequest6 at h
      rw [if_neg hw, malformed_decodes] at h
      exact absurd h (by decide)
  unfold handleRequest6 at h ⊢
  rw [if_pos hw] at h ⊢
  cases hd : DARM.Kernel4.kernelDecide (cfgOf req).policy (cfgOf req).credential
      (DARM.Broker3.canonicalize (cfgOf req) req.proposal) with
  | admit => rfl
  | reject f =>
    rw [hd, replyFor_reject_decodes] at h
    exact absurd h (by decide)

/-- Every line is handled by the new path or by the old one. -/
theorem reply6_cases (line : String) :
    (∃ req, (Json.parse line >>= fromJson? : Except String KernelRequest6) = .ok req ∧
        handleLine6 line = handleRequest6 req) ∨
    handleLine6 line = handleLine4 line := by
  unfold handleLine6
  cases h : (Json.parse line >>= fromJson? : Except String KernelRequest6) with
  | ok req => exact Or.inl ⟨req, rfl, rfl⟩
  | error e => exact Or.inr rfl

/-- For any line of either form, a read admission means the proved kernel admitted. -/
theorem admit_only_by_kernel6 (line : String) (h : DARM.K5.pyAdmits (handleLine6 line) = true) :
    (∃ req, (Json.parse line >>= fromJson? : Except String KernelRequest6) = .ok req ∧
        DARM.K6.k6Step (cfgOf req) req.proposal =
          some (DARM.Broker3.canonicalize (cfgOf req) req.proposal)) ∨
    (∃ req, (Json.parse line >>= fromJson? : Except String KernelRequest4) = .ok req ∧
        DARM.Kernel4.kernelDecide req.policy req.credential req.invocation = .admit) := by
  rcases reply6_cases line with ⟨req, hp, hr⟩ | hr
  · rw [hr] at h
    exact Or.inl ⟨req, hp, admit6_only_by_k6 req h⟩
  · rw [hr] at h
    exact Or.inr (DARM.K5.admit_only_by_kernel line h)

end DARM.K6Server

#print axioms DARM.K6Server.malformed_decodes
#print axioms DARM.K6Server.admit6_only_by_k6
#print axioms DARM.K6Server.admit6_returns_canonical
#print axioms DARM.K6Server.reply6_cases
#print axioms DARM.K6Server.admit_only_by_kernel6
