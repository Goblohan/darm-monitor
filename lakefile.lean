import Lake
open Lake DSL

package darmMonitor where
  -- Package configuration options

require mathlib from git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib DarmMonitor where
  roots := #[`DarmMonitor]
  nativeFacets := fun shouldExport => if shouldExport then #[Module.oExportFacet] else #[Module.oFacet]
