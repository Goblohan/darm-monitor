# DARM: Dynamic Actuation Reference Monitor

`darm-monitor` is a formally verified reference monitor architecture designed for high-integrity autonomous system control. It provides microkernel-enforced boundary isolation and fixed-point mathematical bounds to guarantee that unverified stochastic policy inputs cannot drive actuation targets past verified envelope limits.

## System Architecture

The DARM architecture is organized into three distinct verification and execution layers:

```
[ Stochastic AI Policy ]
           │ (Untrusted Payload)
           ▼
[ CAmkES RPC Boundary ] ───► [ Lean 4 Fixed64 Tower ] ───► [ Hardware Actuator ]
(O_mediation Isolation)        (Formally Verified Bounds)     (MMIO Real-Time Output)
```

1. **Formal Proof Layer (Lean 4):**
   - **`Fixed64Tower`**: Evaluates invariant envelopes over 64-bit fixed-point representations.
   - **`Fixed64Bracket` & `Fixed64ZhiN`**: Proves upper and lower bounds (`ZhiN64_eq`, `wpHiN64_eq`) with zero non-standard kernel axioms.
   - **`Fixed64Evaluator`**: Proves mathematical equivalence between fixed-point evaluation and ideal real-valued bounds (`evaluator_sound_tower64`).

2. **Microkernel Isolation (seL4 / CAmkES):**
   - **`DarmInterface`**: Typed CAmkES IDL defining explicit RPC boundaries between untrusted AI controllers and execution interfaces.
   - **`DarmMonitor`**: Enforces O_mediation and O_authority properties, preventing unverified state-space transitions.

3. **Target Execution & C-ABI Layer:**
   - **`darm_shim`**: Zero-overhead unboxed C-ABI translation layer interfacing C-native microkernel handlers to formal state evaluators.

---

## Build and Verification

### 1. Formal Proof Verification (Lean 4)
Build and verify all Lean 4 proof towers:
```bash
lake build
```

### 2. C-ABI Boundary Unit Tests
Compile and run host-side FFI boundary unit tests:
```bash
gcc -Iinclude tests/test_darm_shim.c -o tests/test_darm_shim
./tests/test_darm_shim
```

### 3. Cross-Compiling for seL4 / ARMv8-A
Build the bootable system image targeting ARMv8-A (Cortex-A53):
```bash
./build.sh
```

### 4. Local QEMU Simulation
Run the verified binary inside a virtualized ARM environment:
```bash
./qemu-run.sh
```

---

## CI/CD Pipeline

The repository enforces automated verification via GitHub Actions (`.github/workflows/ci.yml`):
- **Lean 4 Build Gate**: Re-verifies all proof towers on every push.
- **C-ABI Gate**: Validates host-side scalar boundary safety before pull requests are merged.
