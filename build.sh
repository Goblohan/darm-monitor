#!/usr/bin/env bash
set -euo pipefail

BUILD_DIR="build"
CROSS_PREFIX="aarch64-linux-gnu-"

echo "[DARM BUILD] Preparing build directory: ${BUILD_DIR}"
mkdir -p "${BUILD_DIR}"
cd "${BUILD_DIR}"

echo "[DARM BUILD] Configuring CMake for ARMv8-A target with Ninja..."
cmake -G Ninja \
    -DCMAKE_TOOLCHAIN_FILE=../gcc.cmake \
    -DCROSS_COMPILER_PREFIX="${CROSS_PREFIX}" \
    -DAARCH64=ON \
    -DARM_CPU=cortex-a53 \
    ..

echo "[DARM BUILD] Compiling bootable seL4/CAmkES image..."
ninja

echo "[DARM BUILD] Verification build succeeded. Image ready in ${BUILD_DIR}/images/"
