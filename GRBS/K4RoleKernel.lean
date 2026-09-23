/-
  K4 — ROLE-AWARE DECISION KERNEL (B2b)

  Extends K1: every argument rule has a role.
    * Selector arguments choose WHICH effect happens (a path, a recipient).
      They must have trusted provenance, exactly as in K1.
    * Payload arguments are data carried inside an effect whose selectors
      are authorized (file contents, a message body). They must satisfy
      their rule, but their provenance is not gated.
  Unknown argument keys are selectors, so the default stays strict.

  Targets: (1) with no payload rules, K4 decides exactly as K1, so K1's
  results carry over; (2) payload cannot buy authority: changing payload
  within its rule cannot change the decision.

  NOT claimed: that payload is true, harmless, or free of sensitive data.
  Information flow is a different problem.
-/
import K1DecisionKernel

namespace DARM.Kernel4

open DARM.Kernel (Provenance Arg Invocation Credential Failure Decision)

structure RoleRule where
  key : String
  allowedValues : List String
  allowedPrefixes : List String
  payload : Bool
  deriving Repr

structure ToolPolicy where
  tool : String
  rules : List RoleRule
  deriving Repr

structure Policy where
  tools : List ToolPolicy
  deriving Repr

def ruleAllows (r : RoleRule) (v : String) : Bool :=
  r.allowedValues.contains v || r.allowedPrefixes.any (fun p => v.startsWith p)

def findTool (pol : Policy) (t : String) : Option ToolPolicy :=
  pol.tools.find? (fun tp => tp.tool == t)

def findRule (tp : ToolPolicy) (k : String) : Option RoleRule :=
  tp.rules.find? (fun r => r.key == k)

/-- Deny by default: an argument key with no rule is not allowed. -/
def argAllowed (tp : ToolPolicy) (a : Arg) : Bool :=
  match findRule tp a.key with
  | some r => ruleAllows r a.value
  | none => false

/-- Payload only if its rule says so; unknown keys are selectors. -/
def isPayload (tp : ToolPolicy) (a : Arg) : Bool :=
  match findRule tp a.key with
  | some r => r.payload
  | none => false

def toolKnown (pol : Policy) (t : String) : Bool :=
  (findTool pol t).isSome

def argsAllowed (pol : Policy) (inv : Invocation) : Bool :=
  match findTool pol inv.tool with
  | some tp => inv.args.all (argAllowed tp)
  | none => false

/-- Only selector arguments are provenance-gated. -/
def selectorsTrusted (pol : Policy) (inv : Invocation) : Bool :=
  match findTool pol inv.tool with
  | some tp => inv.args.all (fun a => isPayload tp a || a.prov != Provenance.untrusted)
  | none => false

def admissible (pol : Policy) (cred : Credential) (inv : Invocation) : Bool :=
  !cred.expired && toolKnown pol inv.tool && cred.tools.contains inv.tool &&
    argsAllowed pol inv && selectorsTrusted pol inv

def classify (pol : Policy) (cred : Credential) (inv : Invocation) : Failure :=
  if cred.expired then Failure.temporal
  else if !(toolKnown pol inv.tool) then Failure.observation
  else if !(cred.tools.contains inv.tool) then Failure.authority
  else if !(argsAllowed pol inv) then Failure.semantic
  else Failure.provenance

/-- THE K4 decision function. -/
def kernelDecide (pol : Policy) (cred : Credential) (inv : Invocation) : Decision :=
  if admissible pol cred inv then Decision.admit
  else Decision.reject (classify pol cred inv)

/-! ## Conservative extension: with no payload rules, K4 is exactly K1 -/

def liftRule (r : DARM.Kernel.ArgRule) : RoleRule :=
  { key := r.key, allowedValues := r.allowedValues,
    allowedPrefixes := r.allowedPrefixes, payload := false }

def liftTool (tp : DARM.Kernel.ToolPolicy) : ToolPolicy :=
  { tool := tp.tool, rules := tp.rules.map liftRule }

/-- A K1 policy seen as a K4 policy in which every rule is a selector. -/
def lift (pol : DARM.Kernel.Policy) : Policy :=
  { tools := pol.tools.map liftTool }

theorem findTool_lift (pol : DARM.Kernel.Policy) (t : String) :
    findTool (lift pol) t = (DARM.Kernel.findTool pol t).map liftTool := by
  simp only [findTool, DARM.Kernel.findTool, lift, List.find?_map]
  rfl

theorem findRule_lift (tp : DARM.Kernel.ToolPolicy) (k : String) :
    findRule (liftTool tp) k = (tp.rules.find? (fun r => r.key == k)).map liftRule := by
  simp only [findRule, liftTool, List.find?_map]
  rfl

theorem argAllowed_lift (tp : DARM.Kernel.ToolPolicy) (a : Arg) :
    argAllowed (liftTool tp) a = DARM.Kernel.argAllowed tp a := by
  unfold argAllowed DARM.Kernel.argAllowed
  rw [findRule_lift]
  cases (tp.rules.find? (fun r => r.key == a.key)) <;> rfl

theorem isPayload_lift (tp : DARM.Kernel.ToolPolicy) (a : Arg) :
    isPayload (liftTool tp) a = false := by
  unfold isPayload
  rw [findRule_lift]
  cases (tp.rules.find? (fun r => r.key == a.key)) <;> rfl

theorem toolKnown_lift (pol : DARM.Kernel.Policy) (t : String) :
    toolKnown (lift pol) t = DARM.Kernel.toolKnown pol t := by
  unfold toolKnown DARM.Kernel.toolKnown
  rw [findTool_lift]
  cases (DARM.Kernel.findTool pol t) <;> rfl

theorem argsAllowed_lift (pol : DARM.Kernel.Policy) (inv : Invocation) :
    argsAllowed (lift pol) inv = DARM.Kernel.argsAllowed pol inv := by
  unfold argsAllowed DARM.Kernel.argsAllowed
  rw [findTool_lift]
  cases (DARM.Kernel.findTool pol inv.tool) with
  | none => rfl
  | some tp =>
    show inv.args.all (argAllowed (liftTool tp)) = inv.args.all (DARM.Kernel.argAllowed tp)
    rw [show argAllowed (liftTool tp) = DARM.Kernel.argAllowed tp from
      funext (argAllowed_lift tp)]

theorem selectorsTrusted_lift (pol : DARM.Kernel.Policy) (inv : Invocation)
    (tp : DARM.Kernel.ToolPolicy) (h : DARM.Kernel.findTool pol inv.tool = some tp) :
    selectorsTrusted (lift pol) inv = DARM.Kernel.argsTrusted inv := by
  unfold selectorsTrusted DARM.Kernel.argsTrusted
  rw [findTool_lift, h]
  show inv.args.all (fun a => isPayload (liftTool tp) a || a.prov != Provenance.untrusted) =
       inv.args.all (fun a => a.prov != Provenance.untrusted)
  congr 1
  funext a
  rw [isPayload_lift]
  rfl

theorem admissible_lift (pol : DARM.Kernel.Policy) (cred : Credential) (inv : Invocation) :
    admissible (lift pol) cred inv = DARM.Kernel.admissible pol cred inv := by
  unfold admissible DARM.Kernel.admissible
  rw [toolKnown_lift, argsAllowed_lift]
  cases h : DARM.Kernel.findTool pol inv.tool with
  | none =>
    have hk : DARM.Kernel.toolKnown pol inv.tool = false := by
      simp [DARM.Kernel.toolKnown, h]
    simp [hk]
  | some tp =>
    rw [selectorsTrusted_lift pol inv tp h]

theorem classify_lift (pol : DARM.Kernel.Policy) (cred : Credential) (inv : Invocation) :
    classify (lift pol) cred inv = DARM.Kernel.classify pol cred inv := by
  unfold classify DARM.Kernel.classify
  rw [toolKnown_lift, argsAllowed_lift]

/-- **Conservative extension.** On any K1 policy, K4 decides exactly as K1,
    so every result proved about K1 holds for K4 on such policies. -/
theorem k4_conservative_extension (pol : DARM.Kernel.Policy) (cred : Credential)
    (inv : Invocation) :
    kernelDecide (lift pol) cred inv = DARM.Kernel.kernelDecide pol cred inv := by
  unfold kernelDecide DARM.Kernel.kernelDecide
  rw [admissible_lift, classify_lift]

#print axioms k4_conservative_extension

/-! ## Payload cannot buy authority -/

/-- Rewrite every payload argument (new value, new provenance); selectors untouched. -/
def rewritePayload (tp : ToolPolicy) (newVal : Arg → String) (newProv : Arg → Provenance)
    (inv : Invocation) : Invocation :=
  { tool := inv.tool,
    args := inv.args.map (fun a =>
      if isPayload tp a then { a with value := newVal a, prov := newProv a } else a) }

theorem isPayload_update (tp : ToolPolicy) (a : Arg) (v : String) (q : Provenance) :
    isPayload tp { a with value := v, prov := q } = isPayload tp a := rfl

theorem argAllowed_update (tp : ToolPolicy) (a : Arg) (q : Provenance) :
    argAllowed tp { a with value := a.value, prov := q } = argAllowed tp a := rfl

/-- The provenance check never depends on payload. -/
theorem selectorsTrusted_rewrite (pol : Policy) (tp : ToolPolicy) (newVal : Arg → String)
    (newProv : Arg → Provenance) (inv : Invocation) (htp : findTool pol inv.tool = some tp) :
    selectorsTrusted pol (rewritePayload tp newVal newProv inv) = selectorsTrusted pol inv := by
  unfold selectorsTrusted
  have ht : (rewritePayload tp newVal newProv inv).tool = inv.tool := rfl
  rw [ht, htp]
  show (inv.args.map (fun a =>
          if isPayload tp a then { a with value := newVal a, prov := newProv a } else a)).all
         (fun a => isPayload tp a || a.prov != Provenance.untrusted) =
       inv.args.all (fun a => isPayload tp a || a.prov != Provenance.untrusted)
  rw [List.all_map]
  congr 1
  funext a
  simp only [Function.comp]
  cases hp : isPayload tp a <;> simp [hp, isPayload_update]

/-- **Payload cannot buy authority.** Rewriting payload arguments, while they
    still satisfy their rules, cannot change the decision. -/
theorem payload_cannot_buy_authority (pol : Policy) (cred : Credential) (inv : Invocation)
    (tp : ToolPolicy) (newVal : Arg → String) (newProv : Arg → Provenance)
    (htp : findTool pol inv.tool = some tp)
    (hrule : argsAllowed pol (rewritePayload tp newVal newProv inv) = argsAllowed pol inv) :
    kernelDecide pol cred (rewritePayload tp newVal newProv inv) = kernelDecide pol cred inv := by
  unfold kernelDecide admissible classify
  rw [hrule, selectorsTrusted_rewrite pol tp newVal newProv inv htp] <;> rfl

theorem argsAllowed_relabel (pol : Policy) (tp : ToolPolicy) (newProv : Arg → Provenance)
    (inv : Invocation) (htp : findTool pol inv.tool = some tp) :
    argsAllowed pol (rewritePayload tp (fun a => a.value) newProv inv) = argsAllowed pol inv := by
  unfold argsAllowed
  have ht : (rewritePayload tp (fun a => a.value) newProv inv).tool = inv.tool := rfl
  rw [ht, htp]
  show (inv.args.map (fun a =>
          if isPayload tp a then { a with value := a.value, prov := newProv a } else a)).all
         (argAllowed tp) = inv.args.all (argAllowed tp)
  rw [List.all_map]
  congr 1
  funext a
  simp only [Function.comp]
  cases hp : isPayload tp a <;> simp [argAllowed_update]

/-- Corollary: where payload came from is irrelevant to authorization. -/
theorem payload_provenance_irrelevant (pol : Policy) (cred : Credential) (inv : Invocation)
    (tp : ToolPolicy) (newProv : Arg → Provenance) (htp : findTool pol inv.tool = some tp) :
    kernelDecide pol cred (rewritePayload tp (fun a => a.value) newProv inv) =
      kernelDecide pol cred inv :=
  payload_cannot_buy_authority pol cred inv tp (fun a => a.value) newProv htp
    (argsAllowed_relabel pol tp newProv inv htp)

/-! ## Witnesses: a write tool -/

def writePolicy : Policy :=
  { tools := [{ tool := "write_file",
                rules := [{ key := "path", allowedValues := [],
                            allowedPrefixes := ["/workspace/"], payload := false },
                          { key := "content", allowedValues := [],
                            allowedPrefixes := [""], payload := true }] }] }

def writeCred : Credential := { tools := ["write_file"], expired := false }

/-- Derived path, untrusted content: the content is payload, so admitted. -/
def agentWritesReport : Invocation :=
  { tool := "write_file",
    args := [{ key := "path", value := "/workspace/reports/q3.md", prov := Provenance.derived },
             { key := "content", value := "Q3 summary", prov := Provenance.untrusted }] }

/-- Untrusted path: the path is a selector, so rejected on provenance. -/
def agentPicksPath : Invocation :=
  { tool := "write_file",
    args := [{ key := "path", value := "/workspace/reports/q3.md", prov := Provenance.untrusted },
             { key := "content", value := "Q3 summary", prov := Provenance.untrusted }] }

theorem untrusted_payload_admitted :
    kernelDecide writePolicy writeCred agentWritesReport = Decision.admit := by
  decide +kernel

theorem untrusted_selector_rejected :
    kernelDecide writePolicy writeCred agentPicksPath = Decision.reject Failure.provenance := by
  decide +kernel

end DARM.Kernel4

#print axioms DARM.Kernel4.payload_cannot_buy_authority
#print axioms DARM.Kernel4.payload_provenance_irrelevant
#print axioms DARM.Kernel4.untrusted_payload_admitted
#print axioms DARM.Kernel4.untrusted_selector_rejected
