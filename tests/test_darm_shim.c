#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <stdint.h>
#include "darm_shim.h"

// Mock Lean evaluator export if compiling host-side without Lean runtime link
#ifndef DARM_LINK_LEAN
uint64_t darm_validate_actuation(uint64_t raw_request) {
    const uint64_t MAX_SAFE_BOUND = 0x0000FFFFFFFFFFFFULL;
    if (raw_request > MAX_SAFE_BOUND) {
        return 0x0ULL; // Fallback to safe state
    }
    return raw_request;
}
#endif

int main(void) {
    printf("[DARM C-ABI] Executing scalar translation boundary test suite...\n");

    // Test 1: In-bounds payload preservation (O_refinement pass)
    uint64_t valid_req = 0x0000000000FF0000ULL;
    uint64_t res1 = darm_validate_actuation(valid_req);
    assert(res1 == valid_req);
    printf("  [PASS] Nominal payload preserved: 0x%016lX\n", (unsigned long)res1);

    // Test 2: Out-of-bounds saturation clamp (Scenario A rejection)
    uint64_t oob_req = 0xFFFFFFFFFFFFFFFFULL;
    uint64_t res2 = darm_validate_actuation(oob_req);
    assert(res2 == 0x0ULL);
    printf("  [PASS] Adversarial payload clamped to zero: 0x%016lX\n", (unsigned long)res2);

    // Test 3: Upper threshold boundary
    uint64_t edge_req = 0x0000FFFFFFFFFFFFULL;
    uint64_t res3 = darm_validate_actuation(edge_req);
    assert(res3 == edge_req);
    printf("  [PASS] Upper bound edge accepted: 0x%016lX\n", (unsigned long)res3);

    printf("[DARM C-ABI] All unboxed scalar boundary checks passed.\n");
    return 0;
}
