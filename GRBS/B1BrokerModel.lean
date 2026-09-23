/-
  B1 — DARM BROKER MODEL (specification for DARM Guard v0.5)

  The broker receives agent proposals, builds ONE canonical invocation,
  asks the K1 kernel, and executes that same invocation only if admitted.

  Claims proved here:
    A1  decided = executed: every executed invocation was admitted by the
        kernel and is exactly the canonical form of the proposal.
    P   the agent cannot vouch for itself: Proposal has no provenance
        field; the broker assigns provenance from a trusted registry, and
        any unregistered value blocks execution.
    Authority bounded: anything executed is within the broker's credential
        and fully trusted, whatever the agent proposes.

  NOT claimed:
    A2  complete mediation. That the agent has no other route to the
        effect is a deployment property (credentials held only by the
        broker, sandboxing), evidenced by tests, never proved here.
    A1.5 in deployment: the configuration is a parameter the agent cannot
        reach in this model; in a real system that rests on file
        permissions and a hash-pinned kernel.
    That a Python broker implements this model (needs its own IC1-style
        correspondence).

  Design trade-off, stated deliberately: exact-value registration is safe
  but strict. The agent cannot compose a new value, even one the policy
  would allow, unless the principal registered it.
-/
import K1DecisionKernel

namespace DARM.Broker

open DARM.Kernel

/-- What the agent can send. Note: no provenance field. -/
structure Proposal where
  tool : String
  args : List (String × String)
  deriving Repr

/-- Values the principal registered through a channel the agent cannot write. -/
structure TrustedRegistry where
  values : List String

/-- Broker configuration. The agent has no way to supply or modify it. -/
structure Config where
  policy : Policy
  credential : Credential
  registry : TrustedRegistry

/-- The broker, not the agent, assigns provenance. -/
def assignProv (reg : TrustedRegistry) (v : String) : Provenance :=
  if reg.values.contains v then Provenance.authoritative else Provenance.untrusted

/-- The single canonical invocation built from a proposal. -/
def canonicalize (cfg : Config) (p : Proposal) : Invocation :=
  { tool := p.tool,
    args := p.args.map (fun kv =>
      { key := kv.1, value := kv.2, prov := assignProv cfg.registry kv.2 }) }

/-- One broker step: decide on the canonical invocation, and if admitted,
    return that same invocation as the one to execute. -/
def brokerStep (cfg : Config) (p : Proposal) : Option Invocation :=
  if kernelDecide cfg.policy cfg.credential (canonicalize cfg p) = Decision.admit
  then some (canonicalize cfg p) else none

/-! ## A1: decided = executed -/

/-- Every executed invocation was admitted by the kernel. -/
theorem executed_is_admitted (cfg : Config) (p : Proposal) (e : Invocation)
    (h : brokerStep cfg p = some e) :
    kernelDecide cfg.policy cfg.credential e = Decision.admit := by
  unfold brokerStep at h
  split at h
  · rename_i hadm
    cases h
    exact hadm
  · cases h

/-- The executed invocation is exactly the canonical form of the proposal. -/
theorem executed_is_canonical (cfg : Config) (p : Proposal) (e : Invocation)
    (h : brokerStep cfg p = some e) : e = canonicalize cfg p := by
  unfold brokerStep at h
  split at h
  · cases h
    rfl
  · cases h

/-- A rejected proposal produces no effect. -/
theorem rejected_not_executed (cfg : Config) (p : Proposal)
    (h : kernelDecide cfg.policy cfg.credential (canonicalize cfg p) ≠ Decision.admit) :
    brokerStep cfg p = none := by
  unfold brokerStep
  simp [h]

/-! ## P-integrity: the agent cannot vouch for itself -/

/-- Every argument's provenance is set by the broker from the registry. -/
theorem prov_assigned_by_broker (cfg : Config) (p : Proposal) (a : Arg)
    (ha : a ∈ (canonicalize cfg p).args) :
    a.prov = assignProv cfg.registry a.value := by
  unfold canonicalize at ha
  obtain ⟨kv, _, rfl⟩ := List.mem_map.mp ha
  rfl

/-- Any argument value the principal did not register blocks execution. -/
theorem unregistered_value_never_executed (cfg : Config) (p : Proposal)
    (kv : String × String) (hkv : kv ∈ p.args)
    (hreg : cfg.registry.values.contains kv.2 = false) :
    brokerStep cfg p = none := by
  apply rejected_not_executed
  apply untrusted_argument_never_admitted cfg.policy cfg.credential (canonicalize cfg p)
    { key := kv.1, value := kv.2, prov := assignProv cfg.registry kv.2 }
  · unfold canonicalize
    exact List.mem_map.mpr ⟨kv, hkv, rfl⟩
  · simpa [assignProv] using hreg

/-! ## Authority bounded, whatever the agent proposes -/

theorem broker_authority_bounded (cfg : Config) (p : Proposal) (e : Invocation)
    (h : brokerStep cfg p = some e) :
    cfg.credential.tools.contains e.tool = true ∧ argsTrusted e = true :=
  ⟨(admit_sound cfg.policy cfg.credential e (executed_is_admitted cfg p e h)).2.2.1,
   (admit_sound cfg.policy cfg.credential e (executed_is_admitted cfg p e h)).2.2.2.2⟩

/-! ## Witnesses: filesystem domain -/

def fsPolicy : Policy :=
  { tools := [{ tool := "read_file",
                rules := [{ key := "path", allowedValues := [],
                            allowedPrefixes := ["/workspace/"] }] }] }

def fsCred : Credential := { tools := ["read_file"], expired := false }

def fsCfg : Config :=
  { policy := fsPolicy, credential := fsCred,
    registry := { values := ["/workspace/notes.txt"] } }

/-- The user asked for this path: executed. -/
def userAsked : Proposal := { tool := "read_file", args := [("path", "/workspace/notes.txt")] }

/-- The agent invented this path. The policy prefix would allow it,
    but its value is unregistered, so it is untrusted: not executed. -/
def agentInvented : Proposal := { tool := "read_file", args := [("path", "/workspace/other.txt")] }

theorem user_requested_read_executes :
    (brokerStep fsCfg userAsked).isSome = true := by
  decide +kernel

theorem agent_invented_value_not_executed :
    (brokerStep fsCfg agentInvented).isNone = true := by
  decide +kernel

end DARM.Broker

#print axioms DARM.Broker.executed_is_admitted
#print axioms DARM.Broker.executed_is_canonical
#print axioms DARM.Broker.unregistered_value_never_executed
#print axioms DARM.Broker.broker_authority_bounded
#print axioms DARM.Broker.agent_invented_value_not_executed
