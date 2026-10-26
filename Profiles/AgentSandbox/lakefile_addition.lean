-- =============================================================================
-- ADD THESE LINES TO YOUR EXISTING lakefile.lean
-- =============================================================================

-- Profile library: depends on Core, never imported by Core
lean_lib AgentSandbox where
  roots := #[`AgentSandbox]
  srcDir := "Profiles/AgentSandbox"

-- FFI library: exports C-callable functions
lean_lib AgentSandboxFFI where
  roots := #[`AgentSandbox.FFI]
  srcDir := "Profiles/AgentSandbox"

-- Demo executable: prints the decision table
lean_exe agentsandbox_demo where
  root := `AgentSandbox.Demo
  srcDir := "Profiles/AgentSandbox"

-- =============================================================================
-- IMPORTANT: Do NOT add `AgentSandbox` to the `DarmMonitor` root import.
-- The core must remain ignorant of all profiles.
-- =============================================================================
