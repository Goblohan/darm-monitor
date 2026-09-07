import Lake
open Lake DSL

package darmMonitor where
  leanOptions :=
    #[⟨`pp.unicode.fun, true⟩, ⟨`relaxedAutoImplicit, false⟩,
      ⟨`maxSynthPendingDepth, 3⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib DarmMonitor where
  roots := #[`DarmMonitor]
  nativeFacets := fun shouldExport => if shouldExport then #[Module.oExportFacet] else #[Module.oFacet]

/-
  The demo executable links the hand-built static library `c/libdarm_native.a`,
  which supplies the widening fixed-point multiplies bound by `@[extern]` in
  `DarmMonitor/Fixed64Native.lean`.

  LAKE DOES NOT BUILD THE C. It is compiled separately:

      leanc -c c/darm_native.c -o c/darm_native.o -O2
      ar rcs c/libdarm_native.a c/darm_native.o

  CI does exactly this in the "Build the native library" step before running
  the differential tests.
-/
lean_exe darmdemo where
  root := `Main
  moreLinkArgs := #["-L./c", "-ldarm_native"]
