import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedPreCarrier
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization

/-! # Phase normalization retained by the direct recost source -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeDirectRecostPhaseNormalization

open ConfiguredRecursiveEdgeRecostedPreCarrier
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

variable {P0u khu khatu Qmaxu : ℕ → ℝ} {r : ℕ}
  {S : Stage P0u khu khatu Qmaxu r}
  {p0 kh0 khat0 qmax0 : ℝ}
  {C : Core S} (I : Input C p0 kh0 khat0 qmax0)

/-- The direct source has the same time-zero front as its underlying ready
source. -/
theorem source_front_zero : I.source.F 0 = front S.source 0 := by
  simpa [Input.source, directSource, rawSource] using
    (readySource_front_zero C.geometric.output.chosen I.selected I.pre I.gauge
      I.kh_nonnegative I.kh_lt_one I.shifted
      (rawBounds C.geometric.output.chosen I.selected I.pre I.gauge I.shifted
        I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos))

/-- At terminal time direct recosting retains the exact normalized phase of
the predecessor selected rear. -/
theorem source_unitTangentData_eq_shift_selectedRearData :
    unitTangentData I.source = MarkedShift.shiftData
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
        I.selected I.gauge.q C.geometric.output.chosen.Delta.T /
          period S.source C.geometric.output.chosen.Delta.T)
      (S.source.selectedRearData C.geometric.output.chosen.Delta.T) := by
  simpa [Input.source, directSource, rawSource, carrier,
    CanonicalNormalPathRecost.recost] using
    (readySource_unitTangentData_eq_shift_selectedRearData
      C.geometric.output.chosen I.selected I.pre I.gauge
      I.kh_nonnegative I.kh_lt_one I.shifted
      (rawBounds C.geometric.output.chosen I.selected I.pre I.gauge I.shifted
        I.kh_nonnegative I.kh_lt_one I.scalar I.P0_pos))

/-- Physical selected-inverse uniqueness therefore identifies the complete
initial direct-source rear, including its marked derivatives, up to the
explicit physical phase. -/
theorem source_initial_eq_shift_physicalRear
    {rear frontData : Data} {cF kF dF cR kR dR : ℝ}
    (K : PhysicalRearLimitKinematics kh0 rear frontData)
    (hcF : 0 < cF) (hfront : IsTubeMember cF kF dF frontData)
    (hcR : 0 < cR) (hrear : IsTubeMember cR kR dR rear)
    (frontPhase : ℝ)
    (hF : front S.source 0 =
      ev (MarkedShift.shiftData frontPhase frontData))
    (hP : period S.source 0 = perim frontData) :
    I.source.selectedRearData 0 = MarkedShift.shiftData
      (physicalRearPhase K frontPhase) rear := by
  apply selectedRearData_zero_eq_shift_physicalRear I.source K hcF hfront
    hcR hrear frontPhase
  · exact (source_front_zero I).trans hF
  · simpa [Input.source, directSource, rawSource] using hP

end ConfiguredRecursiveEdgeDirectRecostPhaseNormalization
