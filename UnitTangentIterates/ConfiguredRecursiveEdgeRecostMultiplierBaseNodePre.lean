import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNativeCoreBase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput

/-! # Native pre-cores on the canonical intrinsic base nodes -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre

open ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgePhysicalBaseFinalTailState
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)
  {K0 K1 K2 : ℝ}

/-- The theorem-produced physical geometric input, rebuilt on the truthful
raw diagonal stage after its synchronized unary repackaging. -/
noncomputable def rawGeometricInput (q : ℕ) :
    GeometricInput
      (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage
        (K0 := K0) (K1 := K1) (K2 := K2) J q).asUnary := by
  let G := ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.geometricInput
    (ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
      (K0 := K0) (K1 := K1) (K2 := K2)) q
  refine
    { base := G.base
      bound := G.bound
      terminal := ?_
      output := ?_ }
  · convert G.terminal using 1 <;>
      simp [G, ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage,
        ConfiguredRecursiveEdgeRecostedRawDiagonalBase.unaryStage,
        ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.P0,
        ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.kh,
        ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.khat,
        ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.Qmax,
        ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.P0,
        ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.kh,
        ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.khat,
        ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.Qmax,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat,
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_eq,
        TubeConstants.khat] <;> norm_num
  · convert G.output using 1 <;>
      simp [G, ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage,
        ConfiguredRecursiveEdgeRecostedRawDiagonalBase.unaryStage,
        ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.P0,
        ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.kh,
        ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.khat,
        ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.Qmax,
        ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.P0,
        ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.kh,
        ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.khat,
        ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.Qmax,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat,
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_eq,
        TubeConstants.khat] <;> norm_num

/-- The exact rich physical path uses the normalized time interval. -/
theorem raw_path_time_one (q : ℕ) :
    (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage
      (K0 := K0) (K1 := K1) (K2 := K2) J q).Gamma.T = 1 := by
  simpa [ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage,
    ConfiguredRecursiveEdgeRecostedRawDiagonalBase.unaryStage,
    ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
    ConfiguredRecursiveEdgePhysicalGeometricBase.base,
    ConfiguredRecursiveEdgePhysicalCompositionBase.compositionBaseCorrelated_path]
    using
      (ConfiguredGaugeFirstPhysicalSequence.richStage_spec
        J.scalar.pair.input J.scalar.model_data 1
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
        (q + 1)).2.1

/-- Canonical geometric input on the exact intrinsic base node. -/
noncomputable def baseNodeGeometricInput (n : ℕ) :
    GeometricInput
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage := by
  simpa [baseNode, baseStage] using
    (rawGeometricInput (J := J) (K0 := K0) (K1 := K1) (K2 := K2)
      ((rowOutput R n).N))

/-- Fresh pre-carrier core on the lightweight canonical base node. -/
noncomputable def baseNodePre (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedPreCarrier.Core
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage := by
  let G := baseNodeGeometricInput
    (K0 := K0) (K1 := K1) (K2 := K2) R n
  let H :=
    FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.jointC2_of_exactSource
      G.output.chosen
  refine
    { geometric := G
      eta_continuous := H.eta_continuous
      eta1_continuous := H.eta1_continuous
      eta2_continuous := H.eta2_continuous
      time_one := ?_ }
  exact G.output.chosen.time_eq.trans (by
    simpa [baseNode, baseStage] using
      (raw_path_time_one (J := J) (K0 := K0) (K1 := K1) (K2 := K2)
        ((rowOutput R n).N)))

end ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre
