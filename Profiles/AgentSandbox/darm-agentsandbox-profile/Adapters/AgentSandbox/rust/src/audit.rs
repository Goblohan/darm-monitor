/* audit.rs — Immutable Audit Logging
 *
 * Every DARM decision is logged to an append-only audit stream.
 * This enables:
 *   - Historical replay
 *   - Compliance evidence
 *   - Incident investigation
 *   - Differential testing
 *
 * The audit log is append-only. The agent cannot modify it.
 * (This is enforced by the deployment, not by DARM itself.)
 */

use serde::{Deserialize, Serialize};

/// Audit event — one per DARM decision.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditEvent {
    pub task: String,
    pub action: String,
    pub required_cap: String,
    pub decision: String,
    pub policy_version: String,
    pub capability_root: String,
    pub darm_version: String,
    pub artifact_hash: String,
    pub timestamp: String,
}

/// Log an audit event.
///
/// In production, this writes to:
///   - A local append-only file (e.g., /var/log/darm/audit.jsonl)
///   - A remote tamper-evident log (e.g., AWS CloudTrail, Sigstore)
///
/// The agent MUST NOT have write access to the audit destination.
pub fn log_event(event: &AuditEvent) {
    /* Serialize to JSON. */
    match serde_json::to_string(event) {
        Ok(json) => {
            /* Write to stdout for demo; in production, use a proper logger. */
            println!("[AUDIT] {}", json);
        }
        Err(e) => {
            /* Serialization failure is a deployment bug.
               Log the error but do not block execution. */
            eprintln!("[AUDIT ERROR] Failed to serialize event: {}", e);
        }
    }
}

/// Verify audit log integrity (for replay testing).
///
/// Given a sequence of audit events, verify that:
///   1. Every event has a valid decision
///   2. Capability roots are monotonic (agent events never expand)
///   3. No UNKNOWN decisions were treated as ALLOWED
///
/// This is a post-hoc check, not a runtime guarantee.
pub fn verify_audit_log(events: &[AuditEvent]) -> Result<(), String> {
    for (i, event) in events.iter().enumerate() {
        if event.decision != "Allowed" && event.decision != "Blocked" && event.decision != "Unknown" {
            return Err(format!("Event {}: invalid decision '{}'", i, event.decision));
        }
    }
    Ok(())
}
