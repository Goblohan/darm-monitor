import DarmMonitor.Deployment

/-
  Runtime — the executable fragment, and an honest boundary around it.

  STATUS: [SPEC] until `lake build` exits 0 AND `#print axioms` shows no
  `sorryAx`.

  WHAT EXTRACTS AND WHAT DOES NOT.

  EXTRACTS: the discrete monitor. `Basic.step` is a total computable function,
  and both instantiations use finite enumerations with `DecidableEq`, so
  `allowedActions`, `canExecute`, and `step` all generate code. The theorems
  about them — capability confinement, policy monotonicity, suspension
  absorption, unreachability — are guarantees about THIS code, not about a
  re-implementation of it.

  DOES NOT EXTRACT: the entire continuous stratum. `reweight`, `normalize`,
  `active`, and `Ratifiable` are all `noncomputable`, because `Real` in Lean is
  a quotient of Cauchy sequences with no code generation. `Ratifiable` needing
  `noncomputable` is a fact the compiler reported, not a design choice.

  CONSEQUENCE — READ BEFORE BUILDING ON THIS. A deployment wanting the Z-bound
  at runtime must RE-IMPLEMENT it over floating point. That re-implementation is
  new, unverified code, and the relationship between it and
  `safe_signal_equiv` is an argument rather than a theorem. The gap is not
  incidental: `δ ≤ w i` and `δ * Z ≤ w' i` are exact real comparisons, and
  floating-point rounding near the margin is precisely where an implementation
  would diverge from the proof. Anyone claiming a "verified Z-bound monitor"
  compiled from this repository would be overstating what exists.

  A defensible route, not taken here: state the boundary results over an
  interval arithmetic or a fixed-point type with proved error bounds, so the
  computable predicate is conservative with respect to the real one. That is
  its own project.

  HOW TO EXTRACT. Lean 4 emits C for every computable definition during a
  normal build; the artifacts land in `.lake/build/ir/`. A standalone binary
  additionally needs a `main`, which `runMonitorDemo` below supplies as a
  starting point. There is no Rust backend; Rust integration goes through the
  C FFI.
-/

namespace DARM
namespace Runtime

open DARM.LLMToolCall

/-! ## 1. The executable monitor

  `#eval` is the check that matters here. A definition can typecheck and still
  fail to generate code; if these evaluate, the fragment genuinely runs. -/

/-- A research assistant holding exactly the granted scopes. -/
def initialState : LLMState :=
  { cap := granted
    policy := {Tool.readFile, Tool.httpGet, Tool.bashExec}
    opState := OpState.active
    lastExecuted := none }

/-- Decidable executability, as the runtime would call it. -/
def canRun (s : LLMState) (t : Tool) : Bool :=
  decide (t ∈ allowedActions toolScope s)

-- The policy lists bashExec, but the scope was never granted.
#eval canRun initialState Tool.readFile    -- true
#eval canRun initialState Tool.httpGet     -- true
#eval canRun initialState Tool.bashExec    -- false  ← the theorem, executing
#eval canRun initialState Tool.sendEmail   -- false

/-- Stepping the monitor is computable. -/
def runEvent (s : LLMState) (e : LLMEvent) : LLMState :=
  llmStep s e

#eval (runEvent initialState (Event.execute Tool.readFile)).lastExecuted
#eval (runEvent initialState (Event.execute Tool.bashExec)).lastExecuted  -- none
#eval (runEvent initialState (Event.autonomousExpandCap Scope.shell)).cap == granted

/-! ## 2. The link between the code and the theorems

  `canRun` is a `Bool`; `canExecute` is a `Prop`. Without a bridge, the theorems
  say nothing about what the binary does. -/

/-- **The executable predicate agrees with the proposition.** This is what makes
    the theorems statements about the emitted code rather than about a separate
    mathematical object. -/
theorem canRun_iff_canExecute (s : LLMState) (t : Tool) :
    canRun s t = true ↔ canExecute toolScope s t := by
  unfold canRun canExecute
  exact decide_eq_true_iff

/-- **The runtime guarantee.** Under capability confinement, the executable
    check returns `false` for any tool whose scope was not granted.

    `bash_never_executable` is a statement about a `Prop`. This is the same
    statement about the `Bool` the program branches on. -/
theorem canRun_false_of_ungranted
    (s : LLMState) (t : Tool)
    (hCap : capInvariant granted s)
    (hUngranted : toolScope t ∉ granted) :
    canRun s t = false := by
  have h : ¬ canExecute toolScope s t :=
    DARM.Deployment.never_executable_of_ungranted toolScope granted t hUngranted s hCap
  rw [← Bool.not_eq_true, canRun_iff_canExecute]
  exact h

/-- Instantiated at the shell tool: the binary cannot be made to run bash. -/
theorem bash_canRun_false (s : LLMState) (hCap : capInvariant granted s) :
    canRun s Tool.bashExec = false :=
  canRun_false_of_ungranted s Tool.bashExec hCap (by decide)

/-! ## 3. A demo entry point

  `lake build DarmMonitor.Runtime` emits C for everything above into
  `.lake/build/ir/`. To produce a binary, add an executable target to
  `lakefile.toml`:

      [[lean_exe]]
      name = "darmdemo"
      root = "DarmMonitor.Runtime"

  then `lake exe darmdemo`. -/

def toolName : Tool → String
  | .readFile  => "readFile"
  | .writeFile => "writeFile"
  | .bashExec  => "bashExec"
  | .httpGet   => "httpGet"
  | .sendEmail => "sendEmail"

def allTools : List Tool :=
  [.readFile, .writeFile, .bashExec, .httpGet, .sendEmail]

def report (s : LLMState) : List String :=
  allTools.map fun t =>
    toolName t ++ ": " ++ (if canRun s t then "ALLOWED" else "BLOCKED")

def main : IO Unit := do
  IO.println "DARM reference monitor — discrete fragment"
  IO.println "grant: fsRead, network"
  for line in report initialState do
    IO.println line

#eval main

/-! ## Registered status

  DONE: the discrete monitor executes, and `canRun_iff_canExecute` ties the
  emitted `Bool` to the proved `Prop`, so `bash_canRun_false` is a guarantee
  about the running code.

  NOT DONE, and not a small gap:
    * The continuous stratum does not extract at all. See the header.
    * No C FFI wrapper. Lean's emitted C uses its own runtime and boxing
      conventions; exposing `canRun` to a host program means writing and
      testing that boundary, and nothing about it is verified by this
      development.
    * No trace-level runtime guarantee. `policy_monotone_absorbing` covers
      `List.foldl` over events, but a real deployment loop with I/O between
      steps is a different object, and the correspondence is unproved.
-/

end Runtime
end DARM

#print axioms DARM.Runtime.canRun_iff_canExecute
#print axioms DARM.Runtime.canRun_false_of_ungranted
#print axioms DARM.Runtime.bash_canRun_false
