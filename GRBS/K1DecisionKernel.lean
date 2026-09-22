/-
  K1 — DARM DECISION KERNEL

  The single decision function behind DARM Guard and DARM Verify.
  Core Lean only (no Mathlib) so it builds fast and can be compiled
  into a runtime decision server.

  Checks, in order, with the prior result each one operationalizes:
    T  temporal     credential expired                  (E16)
    O  observation  tool unknown to the policy          (E14)
    A  authority    tool not in the credential          (R4b, E17)
    S  semantic     an argument violates its rule       (R22 argument rung)
    P  provenance   an argument value is untrusted      (generation is not warrant)

  Deliberate differences from DARM Guard v0.1:
    * arguments and their provenance are observed (R22 refinement);
    * authority requires the credential -- policy alone never expands it.
-/

namespace DARM.Kernel

/-- Where an argument value came from. -/
inductive Provenance where
  | authoritative   -- the principal's own instruction
  | derived         -- produced by trusted system components
  | untrusted       -- anything a third party can influence
  deriving DecidableEq, Repr

structure Arg where
  key : String
  value : String
  prov : Provenance
  deriving Repr

structure Invocation where
  tool : String
  args : List Arg
  deriving Repr

/-- A value is allowed if it is listed exactly or starts with an allowed prefix. -/
structure ArgRule where
  key : String
  allowedValues : List String
  allowedPrefixes : List String
  deriving Repr

structure ToolPolicy where
  tool : String
  rules : List ArgRule
  deriving Repr

structure Policy where
  tools : List ToolPolicy
  deriving Repr

structure Credential where
  tools : List String
  expired : Bool
  deriving Repr

inductive Failure where
  | temporal
  | observation
  | authority
  | semantic
  | provenance
  deriving DecidableEq, Repr

inductive Decision where
  | admit
  | reject (f : Failure)
  deriving DecidableEq, Repr

def ruleAllows (r : ArgRule) (v : String) : Bool :=
  r.allowedValues.contains v || r.allowedPrefixes.any (fun p => v.startsWith p)

def findTool (pol : Policy) (t : String) : Option ToolPolicy :=
  pol.tools.find? (fun tp => tp.tool == t)

/-- Deny by default: an argument key with no rule is not allowed. -/
def argAllowed (tp : ToolPolicy) (a : Arg) : Bool :=
  match tp.rules.find? (fun r => r.key == a.key) with
  | some r => ruleAllows r a.value
  | none => false

def toolKnown (pol : Policy) (t : String) : Bool :=
  (findTool pol t).isSome

def argsAllowed (pol : Policy) (inv : Invocation) : Bool :=
  match findTool pol inv.tool with
  | some tp => inv.args.all (argAllowed tp)
  | none => false

def argsTrusted (inv : Invocation) : Bool :=
  inv.args.all (fun a => a.prov != Provenance.untrusted)

def admissible (pol : Policy) (cred : Credential) (inv : Invocation) : Bool :=
  !cred.expired && toolKnown pol inv.tool && cred.tools.contains inv.tool &&
    argsAllowed pol inv && argsTrusted inv

/-- The first failed check, in T-O-A-S-P order. -/
def classify (pol : Policy) (cred : Credential) (inv : Invocation) : Failure :=
  if cred.expired then Failure.temporal
  else if !(toolKnown pol inv.tool) then Failure.observation
  else if !(cred.tools.contains inv.tool) then Failure.authority
  else if !(argsAllowed pol inv) then Failure.semantic
  else Failure.provenance

/-- THE decision function. -/
def kernelDecide (pol : Policy) (cred : Credential) (inv : Invocation) : Decision :=
  if admissible pol cred inv then Decision.admit
  else Decision.reject (classify pol cred inv)

/-! ## General properties -/

/-- The kernel admits exactly when every check passes. -/
theorem kernel_admit_iff (pol : Policy) (cred : Credential) (inv : Invocation) :
    kernelDecide pol cred inv = Decision.admit ↔ admissible pol cred inv = true := by
  unfold kernelDecide
  split <;> simp_all

/-- Admissibility decomposed into its five checks. -/
theorem admissible_iff (pol : Policy) (cred : Credential) (inv : Invocation) :
    admissible pol cred inv = true ↔
      cred.expired = false ∧ toolKnown pol inv.tool = true ∧
      cred.tools.contains inv.tool = true ∧ argsAllowed pol inv = true ∧
      argsTrusted inv = true := by
  simp [admissible, and_assoc]

/-- Soundness of admission: an admitted invocation passed all five checks. -/
theorem admit_sound (pol : Policy) (cred : Credential) (inv : Invocation)
    (h : kernelDecide pol cred inv = Decision.admit) :
    cred.expired = false ∧ toolKnown pol inv.tool = true ∧
      cred.tools.contains inv.tool = true ∧ argsAllowed pol inv = true ∧
      argsTrusted inv = true :=
  (admissible_iff pol cred inv).mp ((kernel_admit_iff pol cred inv).mp h)

/-- T: an expired credential never admits anything. -/
theorem expired_never_admitted (pol : Policy) (cred : Credential) (inv : Invocation)
    (he : cred.expired = true) : kernelDecide pol cred inv ≠ Decision.admit := by
  intro h
  have hx := (admit_sound pol cred inv h).1
  rw [he] at hx
  cases hx

/-- A: authority never expands beyond the credential. -/
theorem uncredentialed_tool_never_admitted (pol : Policy) (cred : Credential)
    (inv : Invocation) (hc : cred.tools.contains inv.tool = false) :
    kernelDecide pol cred inv ≠ Decision.admit := by
  intro h
  have hx := (admit_sound pol cred inv h).2.2.1
  rw [hc] at hx
  cases hx

/-- P: an untrusted argument value can never authorize an invocation. -/
theorem untrusted_argument_never_admitted (pol : Policy) (cred : Credential)
    (inv : Invocation) (a : Arg) (ha : a ∈ inv.args)
    (hu : a.prov = Provenance.untrusted) :
    kernelDecide pol cred inv ≠ Decision.admit := by
  intro h
  have hx := (admit_sound pol cred inv h).2.2.2.2
  unfold argsTrusted at hx
  rw [List.all_eq_true] at hx
  have ha' := hx a ha
  rw [hu] at ha'
  exact absurd ha' (by decide)

/-- Expiry is always reported as a T-failure. -/
theorem expired_classified_temporal (pol : Policy) (cred : Credential)
    (inv : Invocation) (he : cred.expired = true) :
    kernelDecide pol cred inv = Decision.reject Failure.temporal := by
  have hna : admissible pol cred inv = false := by
    simp [admissible, he]
  simp [kernelDecide, hna, classify, he]

/-! ## Concrete witnesses -/

def examplePolicy : Policy :=
  { tools := [{ tool := "file_read",
                rules := [{ key := "path", allowedValues := [],
                            allowedPrefixes := ["/workspace/"] }] }] }

def exampleCred : Credential := { tools := ["file_read"], expired := false }

def safeRead : Invocation :=
  { tool := "file_read",
    args := [{ key := "path", value := "/workspace/notes.txt",
               prov := Provenance.authoritative }] }

def forbiddenRead : Invocation :=
  { tool := "file_read",
    args := [{ key := "path", value := "/etc/passwd",
               prov := Provenance.authoritative }] }

def injectedRead : Invocation :=
  { tool := "file_read",
    args := [{ key := "path", value := "/workspace/notes.txt",
               prov := Provenance.untrusted }] }

theorem safe_read_admitted :
    kernelDecide examplePolicy exampleCred safeRead = Decision.admit := by
  decide +kernel

theorem forbidden_read_rejected_semantic :
    kernelDecide examplePolicy exampleCred forbiddenRead =
      Decision.reject Failure.semantic := by
  decide +kernel

theorem injected_read_rejected_provenance :
    kernelDecide examplePolicy exampleCred injectedRead =
      Decision.reject Failure.provenance := by
  decide +kernel

/-- Same tool, different argument, different decision.
    DARM Guard v0.1 provably cannot do this (R22). -/
theorem kernel_is_argument_sensitive :
    safeRead.tool = forbiddenRead.tool ∧
    kernelDecide examplePolicy exampleCred safeRead ≠
      kernelDecide examplePolicy exampleCred forbiddenRead := by
  refine ⟨rfl, ?_⟩
  rw [safe_read_admitted, forbidden_read_rejected_semantic]
  intro h
  cases h

/-- Same tool, same argument value, different provenance, different decision. -/
theorem kernel_is_provenance_sensitive :
    safeRead.tool = injectedRead.tool ∧
    kernelDecide examplePolicy exampleCred safeRead ≠
      kernelDecide examplePolicy exampleCred injectedRead := by
  refine ⟨rfl, ?_⟩
  rw [safe_read_admitted, injected_read_rejected_provenance]
  intro h
  cases h

end DARM.Kernel

#print axioms DARM.Kernel.admit_sound
#print axioms DARM.Kernel.untrusted_argument_never_admitted
#print axioms DARM.Kernel.kernel_is_argument_sensitive
