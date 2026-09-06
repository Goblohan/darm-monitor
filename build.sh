#!/bin/bash
set -e

echo "[DARM BUILD] Preparing build directory: build"
rm -rf build
mkdir -p build
cd build

echo "[DARM BUILD] Configuring CMake with local CAmkES path..."
cmake -G "Unix Makefiles" -Dcamkes_DIR="$(pwd)/../camkes" ..

echo "[DARM BUILD] Building image..."
cmake --build . -- -j$(nproc)
