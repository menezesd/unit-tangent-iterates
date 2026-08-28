import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawDiagonalBase

/-! # Exact final-tail base layer for intrinsic diagonal nodes -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierBaseLayer

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgePhysicalBaseFinalTailState

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {K0 K1 K2 : ℝ}

/-- The physical base source is retained definitionally; only its four scalar
parameters are named as fields of the intrinsic node. -/
noncomputable def baseNode
    (R : RecostClosingOutput J O) (n : ℕ) : Node where
  P0 := ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.P0
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
      (rowOutput R n).N 0
  khat := ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.khat
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
      (rowOutput R n).N 0
  Qmax := ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.Qmax
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
      (rowOutput R n).N 0
  stage := (baseStage (K0 := K0) (K1 := K1) (K2 := K2) R n).asUnary

@[simp] theorem baseNode_displayed
    (R : RecostClosingOutput J O) (n : ℕ) :
    (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.displayed =
      ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
        (R.totalShift + n) :=
  finalStage_displayed (K0 := K0) (K1 := K1) (K2 := K2) R n

/-- Exact scalar synchronization of the untransported physical base. -/
def baseNode_configured
    (R : RecostClosingOutput J O) (n : ℕ) :
    ConfiguredNode R n
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n) := by
  refine { P0_eq := ?_, khat_eq := ?_, Qmax_eq := ?_ } <;>
    simp [baseNode,
      ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.P0,
      ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.khat,
      ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Profiles.Qmax,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.P0,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.khat,
      ConfiguredRecursiveEdgeRecostedDiagonalRows.Sync.Qmax,
      ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.totalShift,
      Nat.add_assoc]

/-- The callback-free normalized base state, with no source transport. -/
noncomputable def normalized
    (R : RecostClosingOutput J O) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedNormalizedReachableState.State
      ((finalGaugeOutput R).shiftOutput n)
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage
      (rowP1 R n) 0 (rowDefect R n) := by
  convert (ConfiguredRecursiveEdgePhysicalBaseFinalTailState.state
    (K0 := K0) (K1 := K1) (K2 := K2) R n) using 1 <;>
    simp [baseNode, rowP1, rowDefect,
      ConfiguredRecursiveEdgePhysicalBaseFinalTailState.rowOutput,
      ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.totalShift,
      Nat.add_assoc]

/-- Rear of base row `n` is the displayed physical initial of row `n+1`. -/
theorem baseNode_range
    (R : RecostClosingOutput J O) (n : ℕ) :
    range (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.rear.1 =
      range (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R (n + 1)).stage.displayed.1 := by
  change range (baseStage (K0 := K0) (K1 := K1) (K2 := K2) R n).rear.1 =
    range (baseStage (K0 := K0) (K1 := K1) (K2 := K2) R (n + 1)).displayed.1
  simp only [baseStage]
  rw [rowGaugeOutput_N R n, rowGaugeOutput_N R (n + 1)]
  simpa [Nat.add_assoc] using
    (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage_rear_range
      (K0 := K0) (K1 := K1) (K2 := K2) J (R.totalShift + n))

/-- Exact depth-zero reachable layer. -/
noncomputable def layer
    (R : RecostClosingOutput J O) :
    Layer R 0 (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R) where
  configured := baseNode_configured R
  normalized := normalized R

end ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
