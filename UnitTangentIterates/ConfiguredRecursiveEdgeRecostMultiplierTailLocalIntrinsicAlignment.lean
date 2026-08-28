import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierRegularityClosure

/-! # Intrinsic-node alignment of the tail-local geometric base -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierTailLocalIntrinsicAlignment

open ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierRegularityClosure
  ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase
  ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)
  {K0 K1 K2 : ℝ}

/-- Unary node obtained from the actual tail-local geometric stage. -/
noncomputable def node (n : ℕ) : Node where
  P0 := P0 R n
  khat := ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat J.scalar
  Qmax := Qmax R n
  stage := by
    let S := (ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state
      (K0 := K0) (K1 := K1) (K2 := K2) R).stage n
    refine
      { start := S.start
        rear := S.rear
        Gamma := S.Gamma
        source := ?_
        applied := ?_
        displayed := S.displayed }
    · convert S.source using 1 <;>
        simp [S, ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state,
          ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.column,
          ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.P0,
          ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.Qmax,
          ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.row,
          Nat.add_assoc]
    · convert S.applied using 1 <;>
        simp [S, ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state,
          ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.column,
          ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.P0,
          ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.Qmax,
          ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.row,
          Nat.add_assoc]

@[simp] theorem node_displayed (n : ℕ) :
    (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.displayed =
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.displayed := by
  rw [baseNode_displayed]
  simpa [node] using
    (ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state_displayed
      (K0 := K0) (K1 := K1) (K2 := K2) R n)

/-- The two unary packages use the same scalar parameters. -/
theorem node_scalars (n : ℕ) :
    (node (K0 := K0) (K1 := K1) (K2 := K2) R n).P0 =
        (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).P0 ∧
      (node (K0 := K0) (K1 := K1) (K2 := K2) R n).khat =
        (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).khat ∧
      (node (K0 := K0) (K1 := K1) (K2 := K2) R n).Qmax =
        (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).Qmax := by
  simp [node, baseNode, P0, Qmax, row,
    ConfiguredRecursiveEdgePhysicalBaseFinalTailState.rowOutput,
    ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.P0,
    ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.khat,
    ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.Qmax,
    ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.P0,
    ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.khat,
    ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.Qmax,
    ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.totalShift,
    ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat,
    ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax,
    ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat,
    ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
    Nat.add_assoc]

/-- The tail-local geometric current and the intrinsic displayed node are the
same unmarked curve. -/
theorem current_range_node (n : ℕ) :
    range (((ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state
      (K0 := K0) (K1 := K1) (K2 := K2) R).current n).1) =
      range ((node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.displayed.1) := by
  have H :=
    (ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.column
      (K0 := K0) (K1 := K1) (K2 := K2) R).initial_range n
  simpa [ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state,
    ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.column] using H.symm

/-- Exact base-node range edge inherited by the aligned unary node. -/
theorem node_range (n : ℕ) :
    range (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.rear.1 =
      range (node (K0 := K0) (K1 := K1) (K2 := K2) R (n + 1)).stage.displayed.1 := by
  have H :=
    (ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state
      (K0 := K0) (K1 := K1) (K2 := K2) R).column.pathEndRange n
  simpa [node, ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state,
    ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.column,
    ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.column,
    ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.row,
    Nat.add_assoc] using H

/-- Physical tail carriers retain the normalized time interval. -/
theorem path_time_one (n : ℕ) :
    ((ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state
      (K0 := K0) (K1 := K1) (K2 := K2) R).column.path n).T = 1 := by
  simpa [ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state,
    ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.column,
    ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.column,
    ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.row,
    ConfiguredRecursiveEdgePhysicalGeometricBase.base,
    ConfiguredRecursiveEdgePhysicalCompositionBase.compositionBaseCorrelated_path]
    using
      (ConfiguredGaugeFirstPhysicalSequence.richStage_spec
        J.scalar.pair.input J.scalar.model_data 1
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
        (R.totalShift + n + 1)).2.1

/-- Native geometric input on the constant-profile/index-zero node.  The
terminal and output are copied only after the source and applied projections
have been rebuilt in `node`; no stage-index equality is used. -/
noncomputable def nodeGeometricInput (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.GeometricInput
      (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage := by
  let X := ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state
    (K0 := K0) (K1 := K1) (K2 := K2) R
  let G := X.geometricInput n
  refine
    { base := G.base
      bound := G.bound
      terminal := ?_
      output := ?_ }
  · convert G.terminal using 1 <;>
      simp [X, G, node,
        ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state,
        ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.column,
        ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.column,
        ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.row,
        ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.P0,
        ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.Qmax,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        Nat.add_assoc]
  · convert G.output using 1 <;>
      simp [X, G, node,
        ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state,
        ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.column,
        ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.column,
        ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.row,
        ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.P0,
        ConfiguredRecursiveEdgeRecostMultiplierTailLocalGeometricBase.Qmax,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.pathKhat,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat,
        ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
        Nat.add_assoc]

theorem node_path_time_one (n : ℕ) :
    (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.Gamma.T = 1 := by
  simpa [node,
    ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state,
    ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.column]
    using path_time_one (K0 := K0) (K1 := K1) (K2 := K2) R n

/-- Exact-source regularity rebuilt on the native unary node. -/
noncomputable def nodeRegularity (n : ℕ) :
    let G := nodeGeometricInput (K0 := K0) (K1 := K1) (K2 := K2) R n
    Continuous (uncurry G.output.chosen.Delta.eta) ∧
      Continuous (uncurry G.output.chosen.c2.eta1) ∧
      Continuous (uncurry G.output.chosen.c2.eta2) ∧
      G.output.chosen.Delta.T = 1 := by
  let G := nodeGeometricInput (K0 := K0) (K1 := K1) (K2 := K2) R n
  let H :=
    FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.jointC2_of_exactSource
      G.output.chosen
  exact ⟨H.eta_continuous, H.eta1_continuous, H.eta2_continuous,
    G.output.chosen.time_eq.trans (node_path_time_one R n)⟩

/-- Fresh pre-core on the native intrinsic node. -/
noncomputable def nodePre (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedPreCarrier.Core
      (node (K0 := K0) (K1 := K1) (K2 := K2) R n).stage := by
  let G := nodeGeometricInput (K0 := K0) (K1 := K1) (K2 := K2) R n
  let H := nodeRegularity (K0 := K0) (K1 := K1) (K2 := K2) R n
  exact
    { geometric := G
      eta_continuous := H.1
      eta1_continuous := H.2.1
      eta2_continuous := H.2.2.1
      time_one := H.2.2.2 }

noncomputable def regularity (n : ℕ) : Regularity
    (ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state
      (K0 := K0) (K1 := K1) (K2 := K2) R) n :=
  regularity_of_path_time_one _ (path_time_one R) n

/-- Canonical base pre-core on the tail-local state. -/
noncomputable def pre (n : ℕ) :=
  core
    (ConfiguredRecursiveEdgeRecostMultiplierTailLocalHybridBase.state
      (K0 := K0) (K1 := K1) (K2 := K2) R)
    n (regularity R n)

/-- The canonical intrinsic reachable layer remains the authoritative
normalized package for the aligned displayed nodes. -/
noncomputable def layer : Layer R 0
    (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R) :=
  ConfiguredRecursiveEdgeRecostMultiplierBaseLayer.layer R

end ConfiguredRecursiveEdgeRecostMultiplierTailLocalIntrinsicAlignment
