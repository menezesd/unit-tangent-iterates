import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedNextMetric
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedNextPhase
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

namespace ConfiguredRecursiveEdgeRecostFinitePreparedNextGeometry

open ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal

noncomputable section

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R)
  {k : ℕ} {Z : PreparedReachable H k}

/-- Assemble all successor geometric provenance from the prepared step. -/
noncomputable def nextGeometry
    (I : PreparedStepData H Z)
    (sourceMass_le_allowance : ∀ n,
      FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
          (I.input.analytic n).source ≤
        multiplierRecostSourceAllowance O.data distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2
          (H.toClosing.preShift + H.toClosing.large.N +
            (n + (k + 1)))) :
    PreparedGeometryProvenance H (k + 1) (I.next H) where
  rawMetric :=
    ConfiguredRecursiveEdgeRecostFinitePreparedNextMetric.nextRawMetric
      H I sourceMass_le_allowance
  edgeBudget_le_error :=
    ConfiguredRecursiveEdgeRecostFinitePreparedNextMetric.nextRawMetric_edgeBudget_le_error
      H I sourceMass_le_allowance
  displayed_eq_selected :=
    ConfiguredRecursiveEdgeRecostFinitePreparedNextPhase.nextDisplayed_eq_selected H I
  terminalFrontPhase :=
    ConfiguredRecursiveEdgeRecostFinitePreparedNextPhase.nextTerminalFrontPhase H I
  terminalFront_eq_phase :=
    ConfiguredRecursiveEdgeRecostFinitePreparedNextPhase.nextTerminalFront_eq_phase H I
  rawDiagonalRangeEdge :=
    ConfiguredRecursiveEdgeRecostFinitePreparedNextPhase.nextRawDiagonalRangeEdge H I
  frontData_eq_source :=
    ConfiguredRecursiveEdgeRecostFinitePreparedNextPhase.nextFrontData_eq_source H I

end

end ConfiguredRecursiveEdgeRecostFinitePreparedNextGeometry
