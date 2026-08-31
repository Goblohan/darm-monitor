#!/usr/bin/env bash
set -euo pipefail

IMAGE_PATH="build/images/capdl-loader-image-arm-virt"

# Check for custom image name output if default isn't present
if [ ! -f "${IMAGE_PATH}" ]; then
    IMAGE_PATH=$(find build/images/ -type f 2>/dev/null | head -n 1)
fi

if [ -z "${IMAGE_PATH}" ] || [ ! -f "${IMAGE_PATH}" ]; then
    echo "[DARM QEMU] Error: Target image not found in build/images/. Run ./build.sh first."
    exit 1
fi

echo "[DARM QEMU] Booting seL4/CAmkES ARMv8-A binary in QEMU (Cortex-A53)..."
echo "[DARM QEMU] Press Ctrl+A followed by X to exit emulation."

qemu-system-aarch64 \
    -machine virt,virtualization=on,secure=off \
    -cpu cortex-a53 \
    -m 2048M \
    -nographic \
    -kernel "${IMAGE_PATH}"
