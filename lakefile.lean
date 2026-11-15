import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "last_bump_for_v4.31.0"

package teichmuller_program where
  srcDir := "lean"

lean_lib Teichmuller

-- Every ErdosStraus* module is standalone (it carries its own namespace), so
-- each is listed as an independent root instead of going through one
-- aggregator module, which would couple unrelated files.
@[default_target]
lean_lib ErdosStraus where
  roots := #[
    `ErdosStraus,
    `ErdosStrausA3EisensteinSplitCriterion,
    `ErdosStrausAdjacentEscape,
    `ErdosStrausCanonicalNormalForm,
    `ErdosStrausCanonicalRemainderNoWrap,
    `ErdosStrausCanonicalResidual,
    `ErdosStrausCarrierBooleanFibration,
    `ErdosStrausCenteredRayReduction,
    `ErdosStrausCommonOrderConstraint,
    `ErdosStrausCommonPlacementCharacter,
    `ErdosStrausCommonTargetSeparatorNoGo,
    `ErdosStrausConditionalFourier,
    `ErdosStrausConductorEscape,
    `ErdosStrausCrossLayerQuadraticNorm,
    `ErdosStrausCrossLayerResidualTransport,
    `ErdosStrausCrossLayerSquarefreeNormFibration,
    `ErdosStrausCrossLayerType0CharacterGraph,
    `ErdosStrausCrossLayerType0ExternalCarrier,
    `ErdosStrausCrossLayerType0RayContraction,
    `ErdosStrausCrossLayerType0RayDefect,
    `ErdosStrausCrossLayerType0ShiftNormalForm,
    `ErdosStrausCrossQFourierLedger,
    `ErdosStrausCrossQSharedSupport,
    `ErdosStrausCrossRatioNewton,
    `ErdosStrausCrossRatioNormSquareclass,
    `ErdosStrausDirectedResidualValuation,
    `ErdosStrausDivisorCapacity,
    `ErdosStrausDualSplitNoGo,
    `ErdosStrausEscapeDescent,
    `ErdosStrausExactCapacity,
    `ErdosStrausF2PhaseNoGo,
    `ErdosStrausFabCoprime,
    `ErdosStrausFctAnchor,
    `ErdosStrausFctBlockNoGo,
    `ErdosStrausFctBlockState,
    `ErdosStrausFctContraction,
    `ErdosStrausFctDescent,
    `ErdosStrausFctInverseBoundary,
    `ErdosStrausFctInverseDivisor,
    `ErdosStrausFctInversePositive,
    `ErdosStrausFctInverseQuotient,
    `ErdosStrausFctInverseTransport,
    `ErdosStrausFctInverseTransportNoGo,
    `ErdosStrausFctTypeP,
    `ErdosStrausFixedEdgeResultant,
    `ErdosStrausFixedEdgeTransport,
    `ErdosStrausFixedOrbitNoGo,
    `ErdosStrausGlobalRadicalDifference,
    `ErdosStrausGlobalSharedDivisorIncidence,
    `ErdosStrausGlobalType0OwnerIncidence,
    `ErdosStrausHajosCenteredCarry,
    `ErdosStrausHajosGlobalBridge,
    `ErdosStrausHeterogeneousTargetSeparator,
    `ErdosStrausIndependentTargetPhase,
    `ErdosStrausKernelPhase,
    `ErdosStrausKummerDirection,
    `ErdosStrausMovingConductor,
    `ErdosStrausMu3Reciprocity,
    `ErdosStrausMultiplicativeLabelKneserNoGo,
    `ErdosStrausMultiquadraticNormReconstruction,
    `ErdosStrausNearQuarter,
    `ErdosStrausOddClassNormDetector,
    `ErdosStrausOddClassNormPresentation,
    `ErdosStrausOddPrismRigidity,
    `ErdosStrausOrderThreeRayExtension,
    `ErdosStrausP35401CubicBoundary,
    `ErdosStrausP35401OddUnitAnnihilator,
    `ErdosStrausPhaseBoxNoGo,
    `ErdosStrausPhaseCapacity,
    `ErdosStrausPhaseTransportFiber,
    `ErdosStrausPrimaryBoundary,
    `ErdosStrausPrivatePrimaryTargetBridge,
    `ErdosStrausQ3EdgeQuadraticRay,
    `ErdosStrausQ3GlobalQuadraticRay,
    `ErdosStrausQ3GlobalSupportDropoutFamily,
    `ErdosStrausQ3GradedFrame,
    `ErdosStrausQ3LocalSquareTwist,
    `ErdosStrausQ3ProfileTransport,
    `ErdosStrausQ3QuadraticTransport,
    `ErdosStrausQ3StabilizerRank,
    `ErdosStrausQ3Type0CompleteEscapeNoGo,
    `ErdosStrausQ3Type0GlobalSupportDropoutBoundary,
    `ErdosStrausQ3Type0GlobalSupportDropoutCycle,
    `ErdosStrausQ3Type0GlobalSupportSync,
    `ErdosStrausQ3Type0MinimalGlobalSupportDropoutBoundary,
    `ErdosStrausQ3Type0MordellHardCompleteEscapeNoGo,
    `ErdosStrausQ3Type0OwnerTransferBoundary,
    `ErdosStrausQ3Type0ShiftGateBoundary,
    `ErdosStrausQuadraticResidueSixthPowerCollapse,
    `ErdosStrausQuadraticSpin,
    `ErdosStrausQuotientTailHalfDensity,
    `ErdosStrausRationalOutputSymmetry,
    `ErdosStrausRayCharacterBoundary,
    `ErdosStrausRelativeKummerBoundary,
    `ErdosStrausRepeatedSupportNoGo,
    `ErdosStrausResidualNearDivisor,
    `ErdosStrausResidualTargetCollision,
    `ErdosStrausSupportIncidence,
    `ErdosStrausTail,
    `ErdosStrausTargetGraphArithmetic,
    `ErdosStrausTargetGraphCapacity,
    `ErdosStrausTargetGraphReciprocity,
    `ErdosStrausType0InvolutionDescent,
    `ErdosStrausTypeIIReciprocity
  ]

-- Standalone results cited by the Erdos-Straus notes that predate the
-- ErdosStraus* naming. Kept in their own library so a failure there cannot
-- hide a regression in the main ErdosStraus library.
@[default_target]
lean_lib ErdosStrausAuxiliary where
  roots := #[
    `FiniteAdditiveMenu,
    `HalfReduction
  ]

@[default_target]
lean_exe teichmuller_demo where
  root := `Main
