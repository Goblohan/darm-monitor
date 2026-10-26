/* darm_shim.h — C FFI Bridge for AgentSandbox Profile
 *
 * This header defines the public C API that the Rust shim calls.
 * The implementation (darm_shim.c) wraps Lean-exported functions.
 *
 * The Lean runtime must be initialized before any DARM function is called.
 * Call darm_init_runtime() once at program startup.
 */

#ifndef DARM_SHIM_H
#define DARM_SHIM_H

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ============================================================================
 * INITIALIZATION
 * ============================================================================ */

/* Initialize the Lean runtime. Must be called exactly once before any
 * other darm_* function. Safe to call multiple times (idempotent). */
void darm_init_runtime(void);

/* Shutdown the Lean runtime. Call at program exit. */
void darm_shutdown(void);

/* ============================================================================
 * STATE
 * ============================================================================ */

typedef struct {
    uint16_t cap_mask;      /* Bitmask of granted CapIds */
    uint16_t policy_mask;   /* Bitmask of permitted ActionIds */
    uint32_t op_state;      /* Compute budget (discrete stratum) */
    uint8_t  suspended;     /* 0 = active, 1 = suspended */
} DarmState;

/* Initialize state for a task.
 * task_id: 0 = exploitGymReadOnly, 1 = exploitGymWithNetwork, 2 = trustedAudit
 * Returns state via out parameter. */
void darm_init_state(uint8_t task_id, DarmState* out_state);

/* ============================================================================
 * DECISION
 * ============================================================================ */

/* Decide whether a raw request is allowed.
 *
 * method, path: raw request strings (null-terminated UTF-8)
 * state: current monitor state (cap_mask, policy_mask, suspended)
 *
 * Returns:
 *   0 = BLOCKED
 *   1 = ALLOWED
 *   2 = UNKNOWN (classification failed — runtime effect not in verified universe)
 *
 * The caller MUST treat UNKNOWN as BLOCKED. This function never returns
 * an error code; all failures are fail-closed (return 0 or 2). */
uint8_t darm_decide(const char* method,
                    const char* path,
                    const DarmState* state);

/* Convenience: decide with unpacked state fields. */
uint8_t darm_decide_raw(const char* method,
                        const char* path,
                        uint16_t cap_mask,
                        uint16_t policy_mask,
                        uint8_t suspended);

/* ============================================================================
 * VERIFICATION HELPERS (for testing / attestation)
 * ============================================================================ */

/* Get the initial cap mask for a task. For verifying C hardcoding matches Lean. */
uint16_t darm_init_cap_mask(uint8_t task_id);

/* Get the initial policy mask for a task. */
uint16_t darm_init_policy_mask(uint8_t task_id);

/* ============================================================================
 * CONSTANTS (must stay in sync with Lean bit indices)
 * ============================================================================ */

/* CapId bit indices — MUST match AgentSandbox.FFI.capIdToIndex */
#define DARM_CAP_FS_READ            (1u << 0)
#define DARM_CAP_FS_WRITE           (1u << 1)
#define DARM_CAP_ARTIFACTORY_READ   (1u << 2)
#define DARM_CAP_ARTIFACTORY_WRITE  (1u << 3)
#define DARM_CAP_SCREENSHOT         (1u << 4)
#define DARM_CAP_NETWORK_HTTP       (1u << 5)
#define DARM_CAP_SHELL_EXEC         (1u << 6)
#define DARM_CAP_EMAIL_SEND         (1u << 7)
#define DARM_CAP_LOG_APPEND         (1u << 8)
#define DARM_CAP_LOG_MODIFY         (1u << 9)

/* ActionId bit indices — MUST match AgentSandbox.FFI.actionIdToIndex */
#define DARM_ACT_READ_FILE          (1u << 0)
#define DARM_ACT_WRITE_FILE         (1u << 1)
#define DARM_ACT_ARTIFACTORY_FETCH  (1u << 2)
#define DARM_ACT_ARTIFACTORY_UPLOAD (1u << 3)
#define DARM_ACT_ARTIFACTORY_LIST   (1u << 4)
#define DARM_ACT_SCREENSHOT_CAPTURE (1u << 5)
#define DARM_ACT_HTTP_GET           (1u << 6)
#define DARM_ACT_BASH_EXEC          (1u << 7)
#define DARM_ACT_SEND_EMAIL         (1u << 8)
#define DARM_ACT_APPEND_AUDIT_LOG   (1u << 9)
#define DARM_ACT_MODIFY_AUDIT_LOG   (1u << 10)

/* Task IDs — MUST match AgentSandbox.FFI.taskIdToIndex */
#define DARM_TASK_EXPLOIT_GYM_READONLY    0
#define DARM_TASK_EXPLOIT_GYM_WITH_NETWORK 1
#define DARM_TASK_TRUSTED_AUDIT            2

#ifdef __cplusplus
}
#endif

#endif /* DARM_SHIM_H */
