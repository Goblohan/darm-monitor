#include <camkes.h>
#include <stdio.h>
#include <stdint.h>
#include "darm_shim.h"

/**
 * @brief CAmkES RPC handler for incoming untrusted AI actuation commands.
 * Intercepts calls on the `monitor_ep` interface prior to hardware execution.
 */
uint64_t monitor_ep_evaluate_actuation(uint64_t raw_payload) {
    // 1. Intercept raw scalar at the microkernel RPC boundary
    uint64_t validated_payload = darm_validate_actuation(raw_payload);

    if (validated_payload == 0x0ULL && raw_payload != 0x0ULL) {
        printf("[DARM MONITOR] ALERT: Boundary violation detected! Blocked payload 0x%016lX\n", 
               (unsigned long)raw_payload);
        // Discharge O_mediation: drop invalid actuation attempt
        return 0x0ULL;
    }

    // 2. Forward verified command downstream to physical hardware interface
    printf("[DARM MONITOR] Boundary check PASSED. Dispatching payload 0x%016lX to HardwareActuator.\n",
           (unsigned long)validated_payload);
    
    return actuator_ep_dispatch(validated_payload);
}
