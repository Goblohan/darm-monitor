import Lake
open Lake DSL

package darmMonitor where
  -- Package configuration options

@[default_target]
lean_lib DarmMonitor where
  roots := #[`DarmMonitor.Fixed64Evaluator, `DarmMonitor.Fixed64ZhiN, `DarmMonitor.Fixed64Tower]
  -- Enable exporting Lean symbols for external C linking
  nativeFacets := fun shouldExport => if shouldExport then #[Module.oExportFacet] else #[Module.oFacet]
