import Lake
open Lake DSL

package «darm-monitor» where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions :=
  #[⟨`pp.unicode.fun, true⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, 3⟩]

require "leanprover-community" / mathlib @ git "v4.32.0"

@[default_target] lean_lib DarmMonitor

/-
  The demo executable links the hand-built static library `c/libdarm_native.a`,
  which supplies the widening fixed-point multiplies bound by `@[extern]` in
  `DarmMonitor/Fixed64Native.lean`.

  LAKE DOES NOT BUILD THE C. It is compiled manually:

      leanc.exe -c c/darm_native.c -o c/darm_native.o -O2
      llvm-ar.exe rcs c/libdarm_native.a c/darm_native.o

  (both from the toolchain's bin directory). Using `extern_lib` with a Lake
  build rule would automate that; it is not done here because the build-rule
  API is version-sensitive and hand-compiling is transparent about what the
  toolchain is actually doing. The trade is that a fresh clone must run those
  two commands before `lake exe darmdemo` will link.
-/
lean_exe darmdemo where
  root := `Main
  moreLinkArgs := #["-L./c", "-ldarm_native"]
