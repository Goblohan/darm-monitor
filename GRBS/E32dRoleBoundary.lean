/-
  E32d — THE ROLE BOUNDARY: SEPARATE REASONS A TOOL CHANGE BREAKS ADMISSION

  A scratch countermodel meant to show that changing only the tool identity
  breaks admission. Its transformed tool was absent from the policy, so every
  check failed at once (unknown_tool_fails_everything): it isolated nothing.
  This module separates the reasons.

  tool_identity_alone_changes_admission: both tools have identical rules, so
  argsAllowed and selectorsTrusted are unchanged; the credential grants only
  write_file. The source is admitted and the transformed invocation rejected for
  authority. Only the tool differs.

  role_is_tool_relative: both tools are known and the credential grants both;
  the rules differ only in whether content is a payload (write_file) or a
  selector (delete_file). The arguments are allowed alike, selector trust
  differs, and the transformed invocation is rejected. A value's role is
  decided by the tool's rules, so a transformation that changes no argument can
  move an untrusted value across the selector/payload boundary.

  NOT claimed: anything about tool renamings that preserve the rules, the roles
  and the credential (those preserve admission).
-/
import E32RoleSensitive

namespace DARM.E32dRoleBoundary

open DARM.Kernel
open DARM.Kernel4

def source : Invocation :=
  { tool := "write_file",
    args := [{ key := "path", value := "/workspace/report.txt", prov := Provenance.derived },
             { key := "content", value := "hello", prov := Provenance.untrusted }] }

def transformed : Invocation :=
  { tool := "delete_file", args := source.args }

def writeRules : List Kernel4.RoleRule :=
  [{ key := "path", allowedValues := [], allowedPrefixes := ["/workspace/"], payload := false },
   { key := "content", allowedValues := [], allowedPrefixes := [""], payload := true }]

/-- The same keys and allowed values, with content as a selector. -/
def selectorRules : List Kernel4.RoleRule :=
  [{ key := "path", allowedValues := [], allowedPrefixes := ["/workspace/"], payload := false },
   { key := "content", allowedValues := [], allowedPrefixes := [""], payload := false }]

def writeOnly : Kernel4.Policy :=
  { tools := [{ tool := "write_file", rules := writeRules }] }

def bothTools : Kernel4.Policy :=
  { tools := [{ tool := "write_file", rules := writeRules },
              { tool := "delete_file", rules := writeRules }] }

def rolesDiffer : Kernel4.Policy :=
  { tools := [{ tool := "write_file", rules := writeRules },
              { tool := "delete_file", rules := selectorRules }] }

def writeCredential : Credential := { tools := ["write_file"], expired := false }
def bothCredential : Credential := { tools := ["write_file", "delete_file"], expired := false }

/-- Only the tool differs, and admission changes, for authority. -/
theorem tool_identity_alone_changes_admission :
    Kernel4.argsAllowed bothTools transformed = Kernel4.argsAllowed bothTools source ∧
    Kernel4.selectorsTrusted bothTools transformed = Kernel4.selectorsTrusted bothTools source ∧
    Kernel4.kernelDecide bothTools writeCredential source = Decision.admit ∧
    Kernel4.kernelDecide bothTools writeCredential transformed = Decision.reject Failure.authority := by
  decide +kernel

/-- A value's role is tool-relative: allowed alike, but an untrusted payload
    under one tool is an untrusted selector under the other. -/
theorem role_is_tool_relative :
    Kernel4.argsAllowed rolesDiffer transformed = Kernel4.argsAllowed rolesDiffer source ∧
    Kernel4.selectorsTrusted rolesDiffer transformed ≠ Kernel4.selectorsTrusted rolesDiffer source ∧
    Kernel4.kernelDecide rolesDiffer bothCredential source = Decision.admit ∧
    Kernel4.kernelDecide rolesDiffer bothCredential transformed ≠ Decision.admit := by
  decide +kernel

/-- The scratch countermodel, as what it is: for a tool the policy does not
    know, every check fails, and the kernel rejects for observation. -/
theorem unknown_tool_fails_everything :
    Kernel4.argsAllowed writeOnly transformed ≠ Kernel4.argsAllowed writeOnly source ∧
    Kernel4.selectorsTrusted writeOnly transformed ≠ Kernel4.selectorsTrusted writeOnly source ∧
    Kernel4.kernelDecide writeOnly writeCredential transformed = Decision.reject Failure.observation := by
  decide +kernel

end DARM.E32dRoleBoundary

#print axioms DARM.E32dRoleBoundary.tool_identity_alone_changes_admission
#print axioms DARM.E32dRoleBoundary.role_is_tool_relative
#print axioms DARM.E32dRoleBoundary.unknown_tool_fails_everything
