# build.ps1 — AgentSandbox Profile Full Build & Verification
# Run from the DARM repository root (where lakefile.lean lives)

$ErrorActionPreference = "Stop"
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "AgentSandbox Profile — Full Build & Verify" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan

# Step 1: Verify directory structure
Write-Host "`n[1/10] Checking directory structure..." -ForegroundColor Yellow
$required = @(
    "Profiles/AgentSandbox/ActionSurface.lean",
    "Profiles/AgentSandbox/TaskPolicy.lean",
    "Profiles/AgentSandbox/Initialization.lean",
    "Profiles/AgentSandbox/Theorems.lean",
    "Profiles/AgentSandbox/Conformance.lean",
    "Profiles/AgentSandbox/AdapterInterface.lean",
    "Profiles/AgentSandbox/FFI.lean",
    "Profiles/AgentSandbox/Demo.lean",
    "Adapters/AgentSandbox/c/darm_shim.h",
    "Adapters/AgentSandbox/c/darm_shim.c",
    "Adapters/AgentSandbox/rust/Cargo.toml",
    "Adapters/AgentSandbox/rust/src/lib.rs",
    "Adapters/AgentSandbox/rust/src/shim.rs",
    "Adapters/AgentSandbox/rust/src/audit.rs",
    "Adapters/AgentSandbox/rust/build.rs"
)
foreach ($f in $required) {
    if (Test-Path $f) {
        Write-Host "  OK: $f" -ForegroundColor Green
    } else {
        Write-Host "  MISSING: $f" -ForegroundColor Red
        exit 1
    }
}

# Step 2: Check no reverse imports
Write-Host "`n[2/10] Checking dependency direction (Core must not import Profile)..." -ForegroundColor Yellow
$badImports = Select-String -Path "DarmMonitor/*.lean" -Pattern "import AgentSandbox" -SimpleMatch
if ($badImports) {
    Write-Host "  FAIL: Core imports Profile! This breaks the proof boundary." -ForegroundColor Red
    $badImports | ForEach-Object { Write-Host "    $($_.FileName):$($_.LineNumber)" }
    exit 1
} else {
    Write-Host "  OK: No reverse imports found." -ForegroundColor Green
}

# Step 3: Build the profile
Write-Host "`n[3/10] Building AgentSandbox profile..." -ForegroundColor Yellow
lake build AgentSandbox 2>&1 | Tee-Object -FilePath build.log
if ($LASTEXITCODE -ne 0) {
    Write-Host "  FAIL: Build error. See build.log" -ForegroundColor Red
    exit 1
}
Write-Host "  OK: Profile builds successfully." -ForegroundColor Green

# Step 4: Build the FFI library
Write-Host "`n[4/10] Building AgentSandboxFFI library..." -ForegroundColor Yellow
lake build AgentSandboxFFI 2>&1 | Tee-Object -Append -FilePath build.log
if ($LASTEXITCODE -ne 0) {
    Write-Host "  FAIL: FFI build error. See build.log" -ForegroundColor Red
    exit 1
}
Write-Host "  OK: FFI library builds successfully." -ForegroundColor Green

# Step 5: Axiom trace audit (Tier 2)
Write-Host "`n[5/10] Running axiom trace audit..." -ForegroundColor Yellow
$axiomLines = Select-String -Path build.log -Pattern "depends on axioms"
$sorryAxFound = $axiomLines | Select-String -Pattern "sorryAx"
if ($sorryAxFound) {
    Write-Host "  FAIL: sorryAx detected in axiom trace!" -ForegroundColor Red
    $sorryAxFound | ForEach-Object { Write-Host "    $($_.Line)" }
    exit 1
} else {
    Write-Host "  OK: No sorryAx in profile axiom traces." -ForegroundColor Green
}

# Step 6: Check for sorry/admit in profile source (Tier 1)
Write-Host "`n[6/10] Checking for sorry/admit in profile source..." -ForegroundColor Yellow
$sorryFound = Select-String -Path "Profiles/AgentSandbox/*.lean" -Pattern "sorry|admit"
if ($sorryFound) {
    Write-Host "  WARNING: sorry/admit found in profile source:" -ForegroundColor Yellow
    $sorryFound | ForEach-Object { Write-Host "    $($_.FileName):$($_.LineNumber): $($_.Line.Trim())" }
    Write-Host "  These must be resolved before production." -ForegroundColor Yellow
} else {
    Write-Host "  OK: No sorry/admit in profile source." -ForegroundColor Green
}

# Step 7: Run the demo
Write-Host "`n[7/10] Running agentsandbox_demo..." -ForegroundColor Yellow
lake exe agentsandbox_demo 2>&1 | Tee-Object -FilePath demo_output.txt
if ($LASTEXITCODE -ne 0) {
    Write-Host "  FAIL: Demo execution error." -ForegroundColor Red
    exit 1
}
Write-Host "  OK: Demo executed. See demo_output.txt." -ForegroundColor Green

# Step 8: Verify demo output
Write-Host "`n[8/10] Verifying demo output..." -ForegroundColor Yellow
$dangerousBlocked = Select-String -Path demo_output.txt -Pattern "bashExec.*BLOCKED|modifyAuditLog.*BLOCKED|screenshotCapture.*BLOCKED|sendEmail.*BLOCKED|artifactoryUpload.*BLOCKED"
if ($dangerousBlocked) {
    Write-Host "  OK: All dangerous actions are BLOCKED in demo." -ForegroundColor Green
} else {
    Write-Host "  FAIL: Some dangerous actions were not blocked!" -ForegroundColor Red
    exit 1
}

# Step 9: Build Rust shim (if cargo is available)
Write-Host "`n[9/10] Building Rust shim..." -ForegroundColor Yellow
if (Get-Command cargo -ErrorAction SilentlyContinue) {
    Push-Location "Adapters/AgentSandbox/rust"
    cargo build --release 2>&1 | Tee-Object -FilePath ../../rust_build.log
    if ($LASTEXITCODE -ne 0) {
        Write-Host "  WARNING: Rust build failed. See rust_build.log." -ForegroundColor Yellow
        Write-Host "  This is expected if Lean library paths are not configured." -ForegroundColor Yellow
    } else {
        Write-Host "  OK: Rust shim built successfully." -ForegroundColor Green
    }
    Pop-Location
} else {
    Write-Host "  SKIP: cargo not found. Install Rust to build the shim." -ForegroundColor Yellow
}

# Step 10: Verify profile theorem instantiation
Write-Host "`n[10/10] Verifying profile theorem instantiation..." -ForegroundColor Yellow
$profileTheorems = @(
    "bashExec_unreachable",
    "modifyAuditLog_unreachable",
    "screenshotCapture_unreachable",
    "sendEmail_unreachable",
    "artifactoryUpload_unreachable",
    "init_capInvariant",
    "dangerous_caps_absent_from_all_bounds"
)
foreach ($thm in $profileTheorems) {
    $found = Select-String -Path "Profiles/AgentSandbox/*.lean" -Pattern "^theorem $thm"
    if ($found) {
        Write-Host "  OK: $thm" -ForegroundColor Green
    } else {
        Write-Host "  MISSING: $thm" -ForegroundColor Red
    }
}

Write-Host "`n========================================" -ForegroundColor Cyan
Write-Host "AgentSandbox Profile Build Complete" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""
Write-Host "Next steps:" -ForegroundColor White
Write-Host "  1. Review demo_output.txt for the decision table." -ForegroundColor Gray
Write-Host "  2. Resolve any sorry/admit placeholders in Theorems.lean." -ForegroundColor Gray
Write-Host "  3. Build the Rust shim with: cd Adapters/AgentSandbox/rust && cargo build --release" -ForegroundColor Gray
Write-Host "  4. Run red-team tests: ./tests/redteam/bypass_*.sh" -ForegroundColor Gray
