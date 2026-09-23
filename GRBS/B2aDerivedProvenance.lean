/-
  B2a — PATTERN-DERIVED PROVENANCE (extends B1)

  The principal may register exact values (authoritative) and prefix
  patterns (derived). A selector the agent composes that matches a
  principal-registered pattern is trusted as derived; anything else is
  untrusted. The agent still cannot vouch: Proposal has no provenance.

  Claims proved: decided = executed (as in B1); a value that is neither
  registered nor matched by a registered pattern blocks execution;
  derived provenance arises only from a principal-registered pattern.

  Stated plainly: the guarantee keeps its form ("every selector lies in a
  principal-registered set"), but the set is as large as the patterns the
  principal chooses. Pattern breadth is the principal's responsibility.
  Payload arguments are B2b.
-/
import K1DecisionKernel
import B1BrokerModel

namespace DARM.BrokerDerived

open DARM.Kernel
open DARM.Broker (Proposal)

/-- Exact values are authoritative; prefix patterns yield derived. -/
structure Registry where
  values : List String
  prefixes : List String

structure Config where
  policy : Policy
  credential : Credential
  registry : Registry

/-- The broker, not the agent, assigns provenance. -/
def assignProv (reg : Registry) (v : String) : Provenance :=
  if reg.values.contains v then Provenance.authoritative
  else if reg.prefixes.any (fun p => v.startsWith p) then Provenance.derived
  else Provenance.untrusted

def canonicalize (cfg : Config) (p : Proposal) : Invocation :=
  { tool := p.tool,
    args := p.args.map (fun kv =>
      { key := kv.1, value := kv.2, prov := assignProv cfg.registry kv.2 }) }

def brokerStep (cfg : Config) (p : Proposal) : Option Invocation :=
  if kernelDecide cfg.policy cfg.credential (canonicalize cfg p) = Decision.admit
  then some (canonicalize cfg p) else none

theorem executed_is_admitted (cfg : Config) (p : Proposal) (e : Invocation)
    (h : brokerStep cfg p = some e) :
    kernelDecide cfg.policy cfg.credential e = Decision.admit := by
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
    (h : kernelDecide cfg.policy cfg.credential (canonicalize cfg p) ≠ Decision.admit) :
    brokerStep cfg p = none := by
  unfold brokerStep
  simp [h]

/-! ## Derived provenance comes only from the principal -/

/-- A value is labeled derived only if a principal-registered pattern matches it. -/
theorem derived_requires_pattern (reg : Registry) (v : String)
    (h : assignProv reg v = Provenance.derived) :
    reg.prefixes.any (fun p => v.startsWith p) = true := by
  unfold assignProv at h
  split at h
  · cases h
  · split at h
    · assumption
    · cases h

/-- A value neither registered nor matched by a registered pattern blocks execution. -/
theorem unregistered_unmatched_never_executed (cfg : Config) (p : Proposal)
    (kv : String × String) (hkv : kv ∈ p.args)
    (hv : cfg.registry.values.contains kv.2 = false)
    (hp : cfg.registry.prefixes.any (fun q => kv.2.startsWith q) = false) :
    brokerStep cfg p = none := by
  apply rejected_not_executed
  apply untrusted_argument_never_admitted cfg.policy cfg.credential (canonicalize cfg p)
    { key := kv.1, value := kv.2, prov := assignProv cfg.registry kv.2 }
  · unfold canonicalize
    exact List.mem_map.mpr ⟨kv, hkv, rfl⟩
  · show assignProv cfg.registry kv.2 = Provenance.untrusted
    unfold assignProv
    rw [hv, hp]
    simp

/-! ## Witnesses -/

def fsPolicy : Policy :=
  { tools := [{ tool := "read_file",
                rules := [{ key := "path", allowedValues := [],
                            allowedPrefixes := ["/workspace/"] }] }] }

def fsCfg : Config :=
  { policy := fsPolicy,
    credential := { tools := ["read_file"], expired := false },
    registry := { values := ["/workspace/notes.txt"],
                  prefixes := ["/workspace/reports/"] } }

/-- The agent composed this path; it matches the principal's pattern: executed. -/
def composedReport : Proposal := { tool := "read_file", args := [("path", "/workspace/reports/q3.md")] }

/-- The policy allows this path, but no registered value or pattern covers it: not executed. -/
def outsidePattern : Proposal := { tool := "read_file", args := [("path", "/workspace/other.txt")] }

theorem composed_report_executes :
    (brokerStep fsCfg composedReport).isSome = true := by
  decide +kernel

theorem outside_pattern_not_executed :
    (brokerStep fsCfg outsidePattern).isNone = true := by
  decide +kernel

end DARM.BrokerDerived

#print axioms DARM.BrokerDerived.derived_requires_pattern
#print axioms DARM.BrokerDerived.unregistered_unmatched_never_executed
#print axioms DARM.BrokerDerived.composed_report_executes
#print axioms DARM.BrokerDerived.outside_pattern_not_executed
