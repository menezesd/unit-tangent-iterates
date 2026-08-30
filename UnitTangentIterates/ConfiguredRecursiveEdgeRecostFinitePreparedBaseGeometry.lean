import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteBasePreparedProvenance
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFiniteColumnBase

/-! # Geometric provenance for the prepared physical base -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedBaseGeometry

open ConfiguredRecursiveEdgeRecostFiniteBasePreparedStep
  ConfiguredRecursiveEdgeRecostFiniteIntrinsicBaseLayer
  ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
  ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostedRawDiagonalBase
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R) {K0 K1 K2 : ℝ}

/-- The theorem-produced physical base carries complete geometric provenance
without any caller-supplied hypotheses. -/
noncomputable def preparedBaseGeometry :
    PreparedGeometryProvenance H 0
      (preparedBase (K0 := K0) (K1 := K1) (K2 := K2) H) where
  rawMetric := baseRawMetric (K0 := K0) (K1 := K1) (K2 := K2) H
  edgeBudget_le_error := fun n => by
    simpa [baseRawMetric,
      ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing.Output.error,
      Nat.add_assoc] using
      (baseNodePreRawMetric_edgeBudget_le_error
        (K0 := K0) (K1 := K1) (K2 := K2) H.toClosing n)
  displayed_eq_selected := fun n =>
    ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre.baseNode_displayed_eq_selectedRearData_zero
      H.toClosing n
  terminalFrontPhase := fun n =>
    (ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
      (K0 := K0) (K1 := K1) (K2 := K2)).terminalFront_phase
        (H.toClosing.totalShift + n)
  terminalFront_eq_phase := fun n => by
    change
      (ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre.baseNodeGeometricInput
        (K0 := K0) (K1 := K1) (K2 := K2) H.toClosing n).terminal.frontData = _
    rw [ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre.baseNodeGeometricInput_frontData_eq_source]
    exact
      ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre.baseNode_unitTangentData_eq_phase_next_displayed
        H.toClosing n
  rawDiagonalRangeEdge :=
    base_rawDiagonalRangeEdge (K0 := K0) (K1 := K1) (K2 := K2) H
  frontData_eq_source := fun n => by
    change
      (ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre.baseNodeGeometricInput
        (K0 := K0) (K1 := K1) (K2 := K2) H.toClosing n).terminal.frontData = _
    exact
      ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre.baseNodeGeometricInput_frontData_eq_source
        H.toClosing n

end ConfiguredRecursiveEdgeRecostFinitePreparedBaseGeometry
