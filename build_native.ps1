# build_native.ps1 - compile the native widening-multiply library for DARM.
#
# Lake does not build the C (see lakefile.lean). This runs the two toolchain
# commands a fresh clone needs before `lake exe darmdemo` will link.
#
# It locates leanc.exe and llvm-ar.exe via `lean --print-prefix` rather than
# assuming they are on PATH: leanc is shimmed into ~/.elan/bin, but llvm-ar
# lives only in the toolchain's own bin directory and is not on PATH.
#
# Run from the repository root:
#     powershell -ExecutionPolicy Bypass -File build_native.ps1

$ErrorActionPreference = 'Stop'

$prefix = (& lean --print-prefix).Trim()
$bin    = Join-Path $prefix 'bin'
$leanc  = Join-Path $bin 'leanc.exe'
$ar     = Join-Path $bin 'llvm-ar.exe'

if (-not (Test-Path $leanc)) { throw "leanc.exe not found at $leanc" }
if (-not (Test-Path $ar))    { throw "llvm-ar.exe not found at $ar" }

Write-Host "Toolchain bin: $bin"
Write-Host "Compiling c/darm_native.c ..."
& $leanc -c c/darm_native.c -o c/darm_native.o -O2
if ($LASTEXITCODE -ne 0) { throw "leanc failed with exit code $LASTEXITCODE" }

Write-Host "Archiving c/libdarm_native.a ..."
& $ar rcs c/libdarm_native.a c/darm_native.o
if ($LASTEXITCODE -ne 0) { throw "llvm-ar failed with exit code $LASTEXITCODE" }

Write-Host "Done. Built c/libdarm_native.a"
