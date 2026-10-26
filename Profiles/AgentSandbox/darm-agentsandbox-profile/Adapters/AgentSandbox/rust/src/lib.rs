/* lib.rs — DARM AgentSandbox Rust Shim
 *
 * This library provides the runtime enforcement layer that sits between
 * the untrusted agent and the verified DARM kernel.
 *
 * Architecture:
 *   Agent Runtime → Rust Shim → C FFI → Lean-extracted DARM Kernel
 *
 * The shim is the choke point. It:
 *   1. Receives raw tool requests from the agent
 *   2. Serializes them into C-compatible structs
 *   3. Calls the verified DARM decision function via FFI
 *   4. Enforces ALLOW/BLOCK/UNKNOWN → BLOCK
 *   5. Logs immutable audit events
 *   6. Forwards ALLOWED requests to the actual tool driver
 *
 * SAFETY INVARIANT: The shim NEVER converts BLOCKED or UNKNOWN into execution.
 */

pub mod shim;
pub mod audit;

use std::sync::Once;

/* One-time Lean runtime initialization. */
static INIT: Once = Once::new();

pub fn init_darm_runtime() {
    INIT.call_once(|| unsafe {
        darm_init_runtime();
    });
}

/* FFI declarations — link against the C wrapper and Lean runtime. */
#[link(name = "darm_shim")]
extern "C" {
    fn darm_init_runtime();
    fn darm_shutdown();
    fn darm_init_state(task_id: u8, state: *mut DarmState);
    fn darm_decide(method: *const i8, path: *const i8, state: *const DarmState) -> u8;
    fn darm_decide_raw(method: *const i8, path: *const i8,
                       cap_mask: u16, policy_mask: u16, suspended: u8) -> u8;
    fn darm_init_cap_mask(task_id: u8) -> u16;
    fn darm_init_policy_mask(task_id: u8) -> u16;
}

/* Re-export C structs for Rust consumers. */
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DarmState {
    pub cap_mask: u16,
    pub policy_mask: u16,
    pub op_state: u32,
    pub suspended: u8,
}

/* Decision enum — maps to C return values. */
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Decision {
    Blocked = 0,
    Allowed = 1,
    Unknown = 2,  /* MUST be treated as Blocked */
}

impl Decision {
    pub fn is_allowed(self) -> bool {
        matches!(self, Decision::Allowed)
    }

    /* FAIL-CLOSED: Unknown is NOT allowed. */
    pub fn is_blocked(self) -> bool {
        !self.is_allowed()
    }
}

/* Task IDs — must match C constants and Lean indices. */
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskId {
    ExploitGymReadOnly = 0,
    ExploitGymWithNetwork = 1,
    TrustedAudit = 2,
}

/* CapId bit flags — must match C constants and Lean indices. */
pub mod caps {
    pub const FS_READ: u16           = 1 << 0;
    pub const FS_WRITE: u16          = 1 << 1;
    pub const ARTIFACTORY_READ: u16  = 1 << 2;
    pub const ARTIFACTORY_WRITE: u16 = 1 << 3;
    pub const SCREENSHOT: u16        = 1 << 4;
    pub const NETWORK_HTTP: u16      = 1 << 5;
    pub const SHELL_EXEC: u16        = 1 << 6;
    pub const EMAIL_SEND: u16        = 1 << 7;
    pub const LOG_APPEND: u16         = 1 << 8;
    pub const LOG_MODIFY: u16         = 1 << 9;
}

/* ActionId bit flags — must match C constants and Lean indices. */
pub mod actions {
    pub const READ_FILE: u16           = 1 << 0;
    pub const WRITE_FILE: u16          = 1 << 1;
    pub const ARTIFACTORY_FETCH: u16   = 1 << 2;
    pub const ARTIFACTORY_UPLOAD: u16  = 1 << 3;
    pub const ARTIFACTORY_LIST: u16    = 1 << 4;
    pub const SCREENSHOT_CAPTURE: u16  = 1 << 5;
    pub const HTTP_GET: u16            = 1 << 6;
    pub const BASH_EXEC: u16           = 1 << 7;
    pub const SEND_EMAIL: u16          = 1 << 8;
    pub const APPEND_AUDIT_LOG: u16    = 1 << 9;
    pub const MODIFY_AUDIT_LOG: u16    = 1 << 10;
}
