import AgentSandbox.AdapterInterface
import AgentSandbox.Initialization

namespace AgentSandbox.FFI

/-! # FFI — Foreign Function Interface

This module exports DARM decision logic to C via `@[export]`.

The C runtime (and thus the Rust shim) calls these functions to:
1. Initialize a `MonitorState` from a task ID
2. Classify a raw request and decide ALLOW/BLOCK/UNKNOWN

All type conversions (bitmask ↔ Finset, UInt8 ↔ TaskId) happen here.
The C/Rust side only sees primitive types.

This is the **only** Lean module that knows about FFI. It sits at the
boundary between the verified profile and the unverified runtime. -/

-- ============================================================================
-- BITMASK ENCODING (C ↔ Lean)
-- ============================================================================

/-- Map CapId to bit index for UInt16 bitmask.
    Must stay in sync with C/Rust bit definitions. -/
def capIdToIndex : CapId → Nat
  | .fsRead           => 0
  | .fsWrite          => 1
  | .artifactoryRead  => 2
  | .artifactoryWrite=> 3
  | .screenshot       => 4
  | .networkHttp      => 5
  | .shellExec        => 6
  | .emailSend        => 7
  | .logAppend        => 8
  | .logModify        => 9

/-- Map ActionId to bit index for UInt16 bitmask. -/
def actionIdToIndex : ActionId → Nat
  | .readFile          => 0
  | .writeFile         => 1
  | .artifactoryFetch  => 2
  | .artifactoryUpload => 3
  | .artifactoryList   => 4
  | .screenshotCapture => 5
  | .httpGet           => 6
  | .bashExec          => 7
  | .sendEmail         => 8
  | .appendAuditLog    => 9
  | .modifyAuditLog    => 10

/-- Convert a UInt16 bitmask to `Finset CapId`.
    Bit i is set ↔ CapId with index i is in the set. -/
def capMaskToFinset (mask : UInt16) : Finset CapId :=
  Finset.filter (fun c => (mask.toNat &&& (1 <<< capIdToIndex c)) != 0) Finset.univ

/-- Convert a UInt16 bitmask to `Finset ActionId`. -/
def policyMaskToFinset (mask : UInt16) : Finset ActionId :=
  Finset.filter (fun a => (mask.toNat &&& (1 <<< actionIdToIndex a)) != 0) Finset.univ

/-- Convert `TaskId` to UInt8 index. -/
def taskIdToIndex : TaskId → UInt8
  | .exploitGymReadOnly    => 0
  | .exploitGymWithNetwork => 1
  | .trustedAudit          => 2

/-- Convert UInt8 index to `TaskId`. -/
def taskIdFromIndex (i : UInt8) : Option TaskId :=
  match i.val with
  | 0 => some .exploitGymReadOnly
  | 1 => some .exploitGymWithNetwork
  | 2 => some .trustedAudit
  | _ => none

/-- Pack a `MonitorState` into a UInt64 for C consumption.
    Layout:
    bits 0-15   : cap_mask
    bits 16-31  : policy_mask
    bits 32-63  : op_state (truncated to 32 bits)
    Note: suspended is not packed; it is passed separately.
    -/
def packState (s : MonitorState) : UInt64 :=
  let capMask : UInt64 := Finset.fold (fun acc c => acc ||| (1 <<< capIdToIndex c).toUInt64) 0 s.cap
  let policyMask : UInt64 := Finset.fold (fun acc a => acc ||| (1 <<< actionIdToIndex a).toUInt64) 0 s.policy
  let opState : UInt64 := s.opState.toUInt64
  (capMask &&& 0xFFFF) ||| ((policyMask &&& 0xFFFF) <<< 16) ||| ((opState &&& 0xFFFFFFFF) <<< 32)

-- ============================================================================
-- EXPORTED FUNCTIONS (called from C)
-- ============================================================================

/-- Initialize state for a task. Returns a packed UInt64.
    C signature: `uint64_t lean_darm_init_state(uint8_t task_id);`

    The Rust/C shim unpacks the result into a `DarmState` struct. -/
@[export lean_darm_init_state]
def darmInitState (taskIdx : UInt8) : UInt64 :=
  match taskIdFromIndex taskIdx with
  | none => 0  -- invalid task ID → zeroed state (fail-closed)
  | some task => packState (initMonitorState task)

/-- Decide whether a raw request is allowed.
    C signature:
    `uint8_t lean_darm_decide(lean_obj_arg method, lean_obj_arg path, uint16_t cap_mask, uint16_t policy_mask, uint8_t suspended);`

    Returns:
    0 = BLOCK
    1 = ALLOW
    2 = UNKNOWN (classification failed — runtime effect not in verified universe)

    The C wrapper converts C strings to Lean strings before calling this. -/
@[export lean_darm_decide]
def darmDecide (method : String) (path : String)
    (capMask : UInt16) (policyMask : UInt16) (suspended : UInt8) : UInt8 :=
  let req : Adapter.RawRequest := ⟨method, path, []⟩
  let state : MonitorState := {
    cap       := capMaskToFinset capMask
    policy    := policyMaskToFinset policyMask
    opState   := 0  -- opState does not affect discrete decision
    suspended := suspended != 0
  }
  match Adapter.decide req state with
  | .allow   => 1
  | .block   => 0
  | .unknown => 2

/-- Get the initial capability mask for a task (for verification against C hardcoding).
    C signature: `uint16_t lean_darm_init_cap_mask(uint8_t task_id);` -/
@[export lean_darm_init_cap_mask]
def darmInitCapMask (taskIdx : UInt8) : UInt16 :=
  match taskIdFromIndex taskIdx with
  | none => 0
  | some task =>
      let s := initMonitorState task
      Finset.fold (fun acc c => acc ||| (1 <<< capIdToIndex c).toUInt16) 0 s.cap

/-- Get the initial policy mask for a task.
    C signature: `uint16_t lean_darm_init_policy_mask(uint8_t task_id);` -/
@[export lean_darm_init_policy_mask]
def darmInitPolicyMask (taskIdx : UInt8) : UInt16 :=
  match taskIdFromIndex taskIdx with
  | none => 0
  | some task =>
      let s := initMonitorState task
      Finset.fold (fun acc a => acc ||| (1 <<< actionIdToIndex a).toUInt16) 0 s.policy

end AgentSandbox.FFI
