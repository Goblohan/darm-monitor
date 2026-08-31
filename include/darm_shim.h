#ifndef DARM_SHIM_H
#define DARM_SHIM_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Evaluates raw actuation command against verified Lean 4 fixed-point bounds.
 * @param raw_request Unboxed 64-bit scalar payload from stochastic policy.
 * @return Safe clamped uint64_t actuation payload (0x0 on boundary violation).
 */
extern uint64_t darm_validate_actuation(uint64_t raw_request);

#ifdef __cplusplus
}
#endif

#endif // DARM_SHIM_H
