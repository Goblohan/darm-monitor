/-
  B3 — THE COMPLETE BROKER MODEL (B2a registry + K4 kernel)

  The broker as actually built in DARM Guard 0.6: the principal registers
  exact values (authoritative) and prefix patterns (derived); the broker
  assigns provenance; the K4 role-aware kernel decides, gating selectors
  on provenance and letting payload through within its rules.

  Proved: decided = executed; an untrusted SELECTOR (neither registered nor
  matched by a registered pattern) blocks execution; witnesses for a
  report write and for content failing to buy an unmatched path.
  Not claimed: mediation (deployment property), payload truth or harm.
-/
import K4RoleKernel
import B2aDerivedProvenance

namespace DARM.Broker3

open DARM.Kernel (Provenance Arg Invocation Credential Decision Failure)
open DARM.Broker (Proposal)
open DARM.BrokerDerived (Registry assignProv)

structure Config where
  policy : DARM.Kernel4.Policy
  credential : Credential
  registry : Registry

def canonicalize (cfg : Config) (p : Proposal) : Invocation :=
  { tool := p.tool,
    args := p.args.map (fun kv =>
      { key := kv.1, value := kv.2, prov := assignProv cfg.registry kv.2 }) }

def brokerStep (cfg : Config) (p : Proposal) : Option Invocation :=
  if DARM.Kernel4.kernelDecide cfg.policy cfg.credential (canonicalize cfg p) = Decision.admit
  then some (canonicalize cfg p) else none

/-! ## K4 lemmas -/

theorem k4_admit_iff (pol : DARM.Kernel4.Policy) (cred : Credential) (inv : Invocation) :
    DARM.Kernel4.kernelDecide pol cred inv = Decision.admit ↔
      DARM.Kernel4.admissible pol cred inv = true := by
  unfold DARM.Kernel4.kernelDecide
  split <;> simp_all

/-- K4: an untrusted SELECTOR can never authorize an invocation. -/
theorem k4_untrusted_selector_never_admitted (pol : DARM.Kernel4.Policy) (cred : Credential)
    (inv : Invocation) (tp : DARM.Kernel4.ToolPolicy) (a : Arg)
    (htp : DARM.Kernel4.findTool pol inv.tool = some tp) (ha : a ∈ inv.args)
    (hsel : DARM.Kernel4.isPayload tp a = false) (hu : a.prov = Provenance.untrusted) :
    DARM.Kernel4.kernelDecide pol cred inv ≠ Decision.admit := by
  intro h
  have hadm := (k4_admit_iff pol cred inv).mp h
  have hst : DARM.Kernel4.selectorsTrusted pol inv = true := by
    simp only [DARM.Kernel4.admissible, Bool.and_eq_true] at hadm
    exact hadm.2
  unfold DARM.Kernel4.selectorsTrusted at hst
  simp only [htp] at hst
  rw [List.all_eq_true] at hst
  have hx := hst a ha
  rw [hsel, hu] at hx
  exact absurd hx (by decide)

/-! ## The broker -/

theorem executed_is_admitted (cfg : Config) (p : Proposal) (e : Invocation)
    (h : brokerStep cfg p = some e) :
    DARM.Kernel4.kernelDecide cfg.policy cfg.credential e = Decision.admit := by
  unfold brokerStep at h
  split at h
  · rename_i hadm
    cases h
    exact hadm
  · cases h

theorem executed_is_canonical (cfg : Config) (p : Proposal) (e : Invocation)
    (h : brokerStep cfg p = some e) : e = canonicalize cfg p := by
  unfold brokerStep at h
  split at h
  · cases h
    rfl
  · cases h

theorem rejected_not_executed (cfg : Config) (p : Proposal)
    (h : DARM.Kernel4.kernelDecide cfg.policy cfg.credential (canonicalize cfg p) ≠
      Decision.admit) :
    brokerStep cfg p = none := by
  unfold brokerStep
  simp [h]

/-- A selector value neither registered nor under a registered pattern blocks execution. -/
theorem unmatched_selector_never_executed (cfg : Config) (p : Proposal)
    (tp : DARM.Kernel4.ToolPolicy) (kv : String × String)
    (htp : DARM.Kernel4.findTool cfg.policy p.tool = some tp) (hkv : kv ∈ p.args)
    (hsel : DARM.Kernel4.isPayload tp
      { key := kv.1, value := kv.2, prov := assignProv cfg.registry kv.2 } = false)
    (hv : cfg.registry.values.contains kv.2 = false)
    (hp : cfg.registry.prefixes.any (fun q => kv.2.startsWith q) = false) :
    brokerStep cfg p = none := by
  apply rejected_not_executed
  apply k4_untrusted_selector_never_admitted cfg.policy cfg.credential (canonicalize cfg p) tp
    { key := kv.1, value := kv.2, prov := assignProv cfg.registry kv.2 }
  · exact htp
  · unfold canonicalize
    exact List.mem_map.mpr ⟨kv, hkv, rfl⟩
  · exact hsel
  · show assignProv cfg.registry kv.2 = Provenance.untrusted
    unfold assignProv
    rw [hv, hp]
    simp

/-! ## Witnesses -/

def writeCfg : Config :=
  { policy := DARM.Kernel4.writePolicy,
    credential := DARM.Kernel4.writeCred,
    registry := { values := ["/workspace/notes.txt"], prefixes := ["/workspace/reports/"] } }

def agentWritesReport : Proposal :=
  { tool := "write_file", args := [("path", "/workspace/reports/q3.md"), ("content", "Q3 summary")] }

def contentBuysNothing : Proposal :=
  { tool := "write_file", args := [("path", "/workspace/other.txt"), ("content", "/workspace/notes.txt")] }

theorem report_write_executes :
    (brokerStep writeCfg agentWritesReport).isSome = true := by
  decide +kernel

/-- A registered value used as content cannot buy an unmatched path. -/
theorem registered_content_cannot_buy_path :
    (brokerStep writeCfg contentBuysNothing).isNone = true := by
  decide +kernel

end DARM.Broker3

#print axioms DARM.Broker3.k4_untrusted_selector_never_admitted
#print axioms DARM.Broker3.executed_is_canonical
#print axioms DARM.Broker3.unmatched_selector_never_executed
#print axioms DARM.Broker3.report_write_executes
#print axioms DARM.Broker3.registered_content_cannot_buy_path
