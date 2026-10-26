import AgentSandbox.Initialization
import AgentSandbox.Conformance

namespace AgentSandbox.Adapter

/-! # Adapter Interface — The Trust Boundary

This module defines the **narrow interface** between the untrusted agent runtime
and the verified DARM kernel. The adapter is the choke point: every tool
request must pass through `classify` → `decide` before any OS syscall.

The adapter is **not** verified in Lean (it is Rust/C). This module specifies
what the adapter must do, so that the proof boundary is clear:

```
Agent Runtime (untrusted)
    ↓  RawRequest
Adapter (Rust/C — trusted, minimal)
    ↓  Option ActionId
DARM Kernel (Lean-extracted — verified)
    ↓  ALLOW / BLOCK
OS Driver (trusted, but only receives ALLOWED)
```

The adapter's job is to **never** convert `BLOCK` into execution. -/

/-- Raw request from the untrusted runtime.
    These strings come from the agent; they are not trusted. -/
structure RawRequest where
  method : String
  path   : String
  params : List (String × String)
  deriving Repr

/-- Classification is **partial**. If the runtime invents a new effect,
    it maps to `none`. There is **no default case**.

    This is the critical boundary: `classify` is the *only* path from
    raw strings to governed `ActionId`s. If classification fails, the
    request is treated as `UNKNOWN` → `BLOCK`. -/
def classify : RawRequest → Option ActionId
  | ⟨"GET",    "/file",        _⟩ => some .readFile
  | ⟨"POST",   "/file",        _⟩ => some .writeFile
  | ⟨"GET",    "/artifactory", _⟩ => some .artifactoryFetch
  | ⟨"POST",   "/artifactory", _⟩ => some .artifactoryUpload
  | ⟨"LIST",   "/artifactory", _⟩ => some .artifactoryList
  | ⟨"CAPTURE","/screen",      _⟩ => some .screenshotCapture
  | ⟨"GET",    "/http",        _⟩ => some .httpGet
  | ⟨"EXEC",   "/shell",       _⟩ => some .bashExec
  | ⟨"POST",   "/email",       _⟩ => some .sendEmail
  | ⟨"APPEND", "/audit",       _⟩ => some .appendAuditLog
  | ⟨"MODIFY", "/audit",       _⟩ => some .modifyAuditLog
  | _                              => none

/-- Enforcement decision. `unknown` is distinct from `blocked` so that
    the adapter can emit different audit events and security alerts. -/
inductive EnforcementDecision
  | allow
  | block
  | unknown   -- runtime effect not in verified universe
  deriving DecidableEq, Repr

/-- The DARM shim applies this logic.

    INVARIANT: No capability lookup for unknowns. No "best guess." No fallback.
    An unknown request is blocked at the classification boundary, before any
    policy or capability check occurs. -/
def decide (req : RawRequest) (state : MonitorState) : EnforcementDecision :=
  match classify req with
  | none => .unknown
  | some action =>
      if action ∈ state.policy ∧ requiredCap action ∈ state.cap ∧ !state.suspended
      then .allow
      else .block

/-- Operational semantics: `unknown` maps to `BLOCK` + security event.
    It does NOT map to "let the runtime handle it." -/
def decide_to_bool (req : RawRequest) (state : MonitorState) : Bool :=
  match decide req state with
  | .allow  => true
  | .block  => false
  | .unknown => false   -- FAIL CLOSED

/-- The audit event that the adapter must emit for every decision.
    This is the provenance record that enables historical replay. -/
structure AuditEvent where
  task           : String
  action         : String
  requiredCap    : String
  decision       : String   -- "ALLOWED" | "BLOCKED" | "UNKNOWN_BLOCKED"
  policyVersion  : String
  capabilityRoot : String
  darmVersion    : String
  artifactHash   : String
  timestamp      : String
  deriving Repr

/-- Generate an audit event from a decision. The adapter calls this after
    every `decide` and logs the result immutably. -/
def auditEvent (task : String) (req : RawRequest) (state : MonitorState)
    (dec : EnforcementDecision) (version : String) (hash : String) : AuditEvent :=
  let actionStr := match classify req with
    | none   => "UNKNOWN"
    | some a => reprStr a
  let capStr := match classify req with
    | none   => "N/A"
    | some a => reprStr (requiredCap a)
  let decStr := match dec with
    | .allow   => "ALLOWED"
    | .block   => "BLOCKED"
    | .unknown => "UNKNOWN_BLOCKED"
  {
    task           := task
    action         := actionStr
    requiredCap    := capStr
    decision       := decStr
    policyVersion  := "P17"
    capabilityRoot := reprStr state.cap
    darmVersion    := version
    artifactHash   := hash
    timestamp      := "2026-08-27T18:02:00Z"  -- adapter fills with real time
  }

end AgentSandbox.Adapter
