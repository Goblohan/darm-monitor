# AgentSandbox Profile for DARM

**Vendor-agnostic, domain-specific instantiation of the DARM core for autonomous agent sandboxes.**

This profile governs the action boundary of AI agents in a sandboxed environment
where agents may be adversarial, collective, and adaptive. It is the formal
specification layer underneath a runtime enforcement shim.

## What This Profile Proves

| Property | Core Theorem | Profile Instantiation |
|---|---|---|
| Capability confinement | `execution_confined_by_cap_bound` | Every executable action's required capability is in the environment-supplied bound |
| Permanent unreachability | `never_executable_of_ungranted` | `bashExec`, `modifyAuditLog`, `screenshotCapture`, `sendEmail`, `artifactoryUpload` are **never** executable in any task |
| Anti-monotonicity | `unreachable_antitone` | Tightening grants enlarges the unreachable set |
| Trajectory safety | `generateTrajectory_preserves_capInvariant` | Capability confinement holds against unrestricted adaptive adversaries over any finite trace |
| Policy monotonicity | `policy_monotonicity` | Agent events can only **shrink** policy; expansion requires ratification |
| Ratification guard necessity | `unguarded_ratification_counterexample` | Without the guard, coherence breaks; the guard is **exactly** the required condition |

## What This Profile Does NOT Prove

Per the DARM core negative results:
- **Noninterference is false.** Agents can observe policy state. The claim is that they cannot *exploit* it.
- **No state-independent algebraic bridge.** Policy is not derived from continuous weights.
- **No exactly-computable update composes.** The discrete stratum is used; no `reweight`/`normalize` for LLM agents.

## Directory Structure

```
Profiles/AgentSandbox/
├── ActionSurface.lean      -- Closed ActionId/CapId universe, requiredCap mapping
├── TaskPolicy.lean         -- TaskId → CapabilityBound, unreachability proofs
├── Initialization.lean     -- MonitorState factory, init invariants
├── Theorems.lean           -- Core theorem instantiation for this profile
├── Conformance.lean        -- Tool-surface attestation, deployment validation
└── AdapterInterface.lean   -- Shim specification, classify/decide/audit
```

## Dependency Rule

```
Core (DarmMonitor/*.lean)
  ↑ imported by
Profile (Profiles/AgentSandbox/*.lean)
  ↑ imported by
Adapter (Adapters/AgentSandbox/ — Rust/C shim)
```

**The core never imports the profile.** This preserves the proof boundary.

## Adding a New Tool

1. Add constructor to `ActionId` in `ActionSurface.lean`
2. Add constructor to `CapId` in `ActionSurface.lean`
3. Add clause to `requiredCap` in `ActionSurface.lean`
4. Update `taskCapBound` in `TaskPolicy.lean` if the new capability is ever granted
5. Add unreachability proof in `TaskPolicy.lean` if the capability is dangerous
6. Add classification case in `AdapterInterface.lean`
7. Rebuild and re-run axiom audit
8. Update `verifiedSurface` in `Conformance.lean`
9. Update `RuntimeManifest` hash in CI

**Lean's exhaustive pattern matching guarantees that steps 3 and 6 cannot be forgotten.**
The compiler will reject incomplete pattern matches.

## Deployment Assumptions

| ID | Assumption | Violation |
|---|---|---|
| A1 | Every governed tool invocation enters the DARM shim | Bypass → arbitrary execution |
| A2 | The agent cannot directly invoke governed drivers | Direct syscall → bypass |
| A3 | CapabilityRoot originates outside the agent-controlled state | Agent self-grants → escape |
| A4 | CapabilityRoot cannot be expanded by agent execution | Collective voting → privilege escalation |
| A5 | The adapter cannot convert BLOCKED into execution | Shim bug → fail-open |
| A6 | The production artifact corresponds to the audited source revision | Unverified binary → proof irrelevant |
| A7 | RuntimeTools ⊆ VerifiedActions | Shadow tools → ungoverned execution |
| A8 | No permitted action manufactures effects outside verifiedSurface | Shell escape → capability amplification |

## Build

```powershell
# From the DARM repository root
powershell -ExecutionPolicy Bypass -File build.ps1
```

Or manually:
```bash
lake build AgentSandbox
# Check axiom traces
lake build 2>&1 | grep "depends on axioms"
```

## License

Same as DARM core (see repository root).
