/* shim.rs — Main Enforcement Logic
 *
 * The `DarmEnforcer` is the single point of contact between the agent runtime
 * and the DARM kernel. Every tool request MUST pass through here.
 *
 * INVARIANT: No governed effect occurs unless DARM authorized it.
 */

use crate::*;
use crate::audit::*;
use std::ffi::CString;

/// The enforcement handle for a single agent session.
pub struct DarmEnforcer {
    task_id: u8,
    state: DarmState,
    version: String,
    artifact_hash: String,
}

impl DarmEnforcer {
    /// Create a new enforcer for a task.
    /// This is the ONLY way to initialize a governed session.
    pub fn new(task: TaskId, version: &str, artifact_hash: &str) -> Self {
        init_darm_runtime();

        let mut state = DarmState {
            cap_mask: 0,
            policy_mask: 0,
            op_state: 0,
            suspended: 0,
        };

        unsafe {
            darm_init_state(task as u8, &mut state);
        }

        /* Verify: the C initialization matches the Lean-verified masks.
           This is a differential test at startup. */
        let expected_cap = unsafe { darm_init_cap_mask(task as u8) };
        let expected_policy = unsafe { darm_init_policy_mask(task as u8) };
        assert_eq!(state.cap_mask, expected_cap,
            "CRITICAL: C cap_mask does not match Lean-verified cap_mask");
        assert_eq!(state.policy_mask, expected_policy,
            "CRITICAL: C policy_mask does not match Lean-verified policy_mask");

        DarmEnforcer {
            task_id: task as u8,
            state,
            version: version.to_string(),
            artifact_hash: artifact_hash.to_string(),
        }
    }

    /// Check a raw request. This is the choke point.
    ///
    /// Returns `Decision::Allowed` only if ALL of the following hold:
    ///   1. The request classifies to a known ActionId
    ///   2. The action is in the current policy
    ///   3. The required capability is in the current capability set
    ///   4. The state is not suspended
    ///
    /// Otherwise returns `Decision::Blocked` or `Decision::Unknown`.
    /// BOTH are treated as blocked by the caller.
    pub fn check(&self, method: &str, path: &str) -> Decision {
        let method_c = CString::new(method).expect("method contains null byte");
        let path_c = CString::new(path).expect("path contains null byte");

        let result = unsafe {
            darm_decide(method_c.as_ptr(), path_c.as_ptr(), &self.state)
        };

        match result {
            0 => Decision::Blocked,
            1 => Decision::Allowed,
            2 => Decision::Unknown,
            _ => {
                /* Invalid return value is a deployment bug — fail closed. */
                log::error!("DARM returned invalid decision code: {}", result);
                Decision::Blocked
            }
        }
    }

    /// Check and log. This is the production entry point.
    ///
    /// 1. Calls `check` to get the DARM decision
    /// 2. Emits an immutable audit event
    /// 3. Returns the decision
    ///
    /// The caller MUST enforce the decision.
    pub fn check_and_log(&self, method: &str, path: &str) -> Decision {
        let decision = self.check(method, path);

        let event = AuditEvent {
            task: format!("T{}", self.task_id),
            action: format!("{} {}", method, path),
            required_cap: self.infer_capability(method, path),
            decision: format!("{:?}", decision),
            policy_version: "P17".to_string(),
            capability_root: format!("0x{:04X}", self.state.cap_mask),
            darm_version: self.version.clone(),
            artifact_hash: self.artifact_hash.clone(),
            timestamp: chrono::Utc::now().to_rfc3339(),
        };

        audit::log_event(&event);
        decision
    }

    /// Infer the required capability for a request (for audit logging only).
    /// This is NOT used for enforcement — the Lean kernel does that.
    fn infer_capability(&self, method: &str, path: &str) -> String {
        match (method, path) {
            ("GET",    "/file")        => "fsRead",
            ("POST",   "/file")        => "fsWrite",
            ("GET",    "/artifactory") => "artifactoryRead",
            ("POST",   "/artifactory") => "artifactoryWrite",
            ("LIST",   "/artifactory") => "artifactoryRead",
            ("CAPTURE","/screen")      => "screenshot",
            ("GET",    "/http")        => "networkHttp",
            ("EXEC",   "/shell")       => "shellExec",
            ("POST",   "/email")       => "emailSend",
            ("APPEND", "/audit")       => "logAppend",
            ("MODIFY", "/audit")       => "logModify",
            _                            => "UNKNOWN",
        }.to_string()
    }

    /// Suspend the session. Agent events cannot unsuspend.
    /// Only the environment (scorer) can ratify a new state.
    pub fn suspend(&mut self) {
        self.state.suspended = 1;
    }

    /// Ratify a new capability set. This is the ONLY way to expand authority.
    /// The discrete guard is verified in Lean; this function just applies it.
    pub fn ratify(&mut self, new_cap_mask: u16, new_policy_mask: u16) {
        /* In a production system, this would verify the discrete guard
           before applying. For now, we trust the caller (the scorer). */
        self.state.cap_mask = new_cap_mask;
        self.state.policy_mask = new_policy_mask;
    }
}

/// Convenience: check a request and enforce the result.
/// If ALLOWED, returns Ok(()).
/// If BLOCKED or UNKNOWN, returns Err with an error message.
pub fn enforce(enforcer: &DarmEnforcer, method: &str, path: &str) -> Result<(), String> {
    let decision = enforcer.check_and_log(method, path);
    if decision.is_allowed() {
        Ok(())
    } else {
        Err(format!("DARM {}: {} {}",
            if matches!(decision, Decision::Unknown) { "UNKNOWN" } else { "BLOCKED" },
            method, path))
    }
}
