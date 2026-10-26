import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

namespace AgentSandbox

variable (CapId : Type) [DecidableEq CapId] [Fintype CapId]

structure ActionSurface where
  capabilities : Finset CapId
  active : CapId -> Prop

namespace ActionSurface

variable {CapId : Type} [DecidableEq CapId] [Fintype CapId]

def IsBounded (surface : ActionSurface CapId) : Prop :=
   c, surface.active c -> c  surface.capabilities

open Classical in
noncomputable instance (surface : ActionSurface CapId) : Decidable (IsBounded surface) :=
  inferInstance

end ActionSurface

end AgentSandbox