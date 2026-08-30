import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer

/-! # Geometric provenance for prepared finite recursion -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema

open ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostedRawMetricGeometry

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}

/-- Geometric and phase information retained by a prepared reachable layer. -/
structure PreparedGeometryProvenance
    (H : Output R) (k : ℕ) (Z : PreparedReachable H k) where
  rawMetric : ∀ n, RawMetricGeometry.Bounded (Z.pre H n).geometric
  edgeBudget_le_error : ∀ n, (rawMetric n).edgeBudget ≤ H.error n k
  displayed_eq_selected : ∀ n,
    (Z.nodes n).stage.displayed =
      (Z.nodes n).stage.source.selectedRearData 0
  terminalFrontPhase : ℕ → ℝ
  terminalFront_eq_phase : ∀ n,
    (Z.presented n).terminal.frontData =
      MarkedShift.shiftData (terminalFrontPhase n)
        (Z.nodes (n + 1)).stage.displayed
  rawDiagonalRangeEdge : ∀ n,
    VariableMarkedTube.GeometricUnitTangentRangeEdge
      (Z.nodes (n + 1)).stage.displayed (Z.pre H n).geometric.base
  frontData_eq_source : ∀ n,
    (Z.presented n).terminal.frontData =
      FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
        (Z.nodes n).stage.source

end ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema

namespace ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.InputData

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  FiniteHistoryMajorBudget
  FiniteNonaffineMajorLayer

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R)

/-- Configured scalar synchronization of every finite successor node. -/
def nextConfigured
    {budget : ℕ → MajorBudget
      ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal}
    {k : ℕ}
    {S : ℕ → ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows.Node}
    {L : FiniteNonaffineMajorLayer.Layer budget
      (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.stateP1 H)
      (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.defect H) k S}
    (I : ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.InputData
      J H budget L) (n : ℕ) :
    ConfiguredNode H.toClosing (n + (k + 1)) (I.step.next n) := by
  refine
    { P0_eq := ?_
      khat_eq := ?_
      Qmax_eq := ?_
      stageP0_at_index_eq := rfl
      stageKhat_at_index_eq := rfl
      stageQmax_at_index_eq := rfl }
  · change
      ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
          (globalData (J := J))
          (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal
            H n (k + 1)) =
        ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
          (globalData (J := J)) (H.totalShift + (n + (k + 1)))
    congr 1
    simp [ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · rfl
  · change
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
          (globalData (J := J))
          (ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal
            H n (k + 1)) =
        ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
          (globalData (J := J)) (H.totalShift + (n + (k + 1)))
    congr 1
    simp [ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.InputData
