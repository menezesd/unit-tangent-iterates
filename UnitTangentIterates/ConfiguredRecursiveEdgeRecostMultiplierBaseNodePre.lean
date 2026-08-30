import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawMetricGeometry
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFiniteColumnBase

/-! # Canonical geometric inputs and raw metrics on intrinsic base nodes -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre

open ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgePhysicalBaseFinalTailState
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)
  {K0 K1 K2 : ℝ}

/-- The canonical physical row already has all three flow ceilings needed by
its raw metric geometry. -/
private noncomputable def canonicalRawMetric (q : ℕ) :
    ConfiguredRecursiveEdgeRecostedRawMetricGeometry.RawMetricGeometry.Bounded
      (ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.geometricInput
        (ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
          (K0 := K0) (K1 := K1) (K2 := K2)) q) := by
  let H := ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
    (K0 := K0) (K1 := K1) (K2 := K2)
  have hflow := ConfiguredRecursiveEdgePhysicalFlowCeilings.source_flowCeilings J
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
    (MA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
    (NA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) q
  exact ConfiguredRecursiveEdgeRecostedRawMetricGeometry.ofCanonicalRow H q
    hflow.1 hflow.2.1 hflow.2.2

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
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage :=
  ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.geometricInput
    (ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
      (K0 := K0) (K1 := K1) (K2 := K2)) (rowOutput R n).N

/-- The canonical terminal input retained at a base node uses the unit-tangent
datum of that exact node's source. -/
theorem baseNodeGeometricInput_frontData_eq_source (n : ℕ) :
    (baseNodeGeometricInput (K0 := K0) (K1 := K1) (K2 := K2) R n).terminal.frontData =
      unitTangentData
        (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source := by
  change
    (FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.geometry
      (ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
        (K0 := K0) (K1 := K1) (K2 := K2)) (rowOutput R n).N).frontData = _
  exact
    (FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.geometry
      (ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
        (K0 := K0) (K1 := K1) (K2 := K2)) (rowOutput R n).N).frontData_eq

/-- The displayed physical base is the source-selected rear at time zero. -/
theorem baseNode_displayed_eq_selectedRearData_zero (n : ℕ) :
    (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.displayed =
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source.selectedRearData 0 := by
  rw [baseNode_displayed]
  change
    ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar
        (R.totalShift + n) =
      ((ConfiguredRecursiveEdgePhysicalGeometricBase.base J
        (K0 := K0) (K1 := K1) (K2 := K2)).source
          (rowOutput R n).N).selectedRearData 0
  rw [rowGaugeOutput_N]
  simpa [ConfiguredRecursiveEdgePhysicalGeometricBase.base,
    ConfiguredRecursiveEdgePhysicalFiniteColumnBase.column] using
    (ConfiguredRecursiveEdgePhysicalFiniteColumnBase.selectedRearData_zero_eq_initial J
        (K0 := K0) (K1 := K1) (K2 := K2) (R.totalShift + n)).symm

/-- The source tangent datum at a base node is the invariant terminal phase
shift of the following displayed physical base. -/
theorem baseNode_unitTangentData_eq_phase_next_displayed (n : ℕ) :
    unitTangentData
        (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source =
      MarkedShift.shiftData
        ((ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
          (K0 := K0) (K1 := K1) (K2 := K2)).terminalFront_phase
            (R.totalShift + n))
        (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R (n + 1)).stage.displayed := by
  rw [baseNode_displayed]
  change
    unitTangentData
        ((ConfiguredRecursiveEdgePhysicalGeometricBase.base J
          (K0 := K0) (K1 := K1) (K2 := K2)).source
            (rowOutput R n).N) = _
  rw [rowGaugeOutput_N]
  simpa [ConfiguredRecursiveEdgePhysicalGeometricBase.base_initial,
    Nat.add_assoc] using
    (ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
      (K0 := K0) (K1 := K1) (K2 := K2)).terminalFront_eq_phase
        (R.totalShift + n)

/-- Canonical raw metric geometry on the final-tail base node. -/
noncomputable def baseNodeRawMetric (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedRawMetricGeometry.RawMetricGeometry.Bounded
      (baseNodeGeometricInput (K0 := K0) (K1 := K1) (K2 := K2) R n) :=
  canonicalRawMetric (J := J) (K0 := K0) (K1 := K1) (K2 := K2)
    (rowOutput R n).N

end ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre
