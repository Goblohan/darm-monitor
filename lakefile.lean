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

lean_lib GRBS where
  srcDir := "GRBS"
  roots := #[
    `GRBS,
    `SeL4GRBS,
    `AGBypass,
    `DARMCoreCalculus,
    `R4eDARMAdapter,
    `IC1AbstractionGap,
    `IC1RuntimeSemantics,
    `IC1RuntimeSemanticRepresentation,
    `IC1SemanticDeltaRepresentation,
    `IC1R20CausalCoverage,
    `IC1R20CausalCoverage_refinement,
    `R19BoundaryMediatedTransferSemantics,
    `R19bSemanticDependencyBridge,
    `R19bDARMBridge,
    `R20DARMToSemanticCorrespondence,
    `R21RepairAdequacy,
    `R21RepairAdequacy_minimality,
    `R22RuntimeSemanticCorrespondence,
    `R22PositiveRepair,
    `R22RuntimeImplementationCorrespondence,
    `R8RichContractSeparation,
    `E13CausalSemanticCorrespondence,
    `E14AGContractComparison,
    `E15CausalCoverageContractEquivalence,
    `E16TemporalFreshness,
    `E17ProposalAuthoritySeparation,
    `E18AssuranceFailureWitness,
    `K1DecisionKernel,
    `B1BrokerModel,
    `K4RoleKernel,
    `B3BrokerModel,
    `E24EpistemicPremiseTransfer,
    `E24bResourceIntents,
    `E24cRevocation,
    `B6EffectIntegrity,
    `B5EffectReconciliation,
    `B7IdempotencyKeys,
    `R23DARMGuardCausalCoverage,
    `B8TypedEffectLog,
    `B9RenameProtocol,
    `B6cCompoundRename,
    `B9RecoveryCheck,
    `B9RecoveryTrace,
    `B9RecoveryTraceBad,
    `B8TraceCheck,
    `B8TraceSample300B,
    `B8TraceSample300BBad,
    `B8TraceSample,
    `B8TraceSample300Bad,
    `B2aDerivedProvenance,
    `K3aKernelCorrespondence,
    `K3bKernelR22,
    `E13ExactLiftMissingA1,
    `E13ExactLiftMissingA2,
    `E13ExactLiftMissingA3,
    `E13ExactLiftMissingA4,
    `E13ExactLiftMissingA5,
    `E16aFiniteCausalDomain,
    `E20TemporalFreshnessCertificateBridge,
    `E21ExecutableObligationBridge,
    `E23TMCPhysicalComposition,
    `E23TMCRefinement,
    `R4aScopeExpansion,
    `R4bAuthoritySubstitution,
    `R4cLocusSubstitution,
    `R4dEvidenceCoverage,
    `R4eBoundaryComposition,
    `R4fRelationalAssurance,
    `R5AssuranceConservation,
    `R5DomainPolymorphism,
    `R5R4Correspondence,
    `R5R4bCorrespondence,
    `R5R4cCorrespondence,
    `R5R4dCorrespondence,
    `R6GRBSDeltaBridge,
  ]

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

lean_exe darmkernel where
  srcDir := "GRBS"
  root := `K4DecisionServer
