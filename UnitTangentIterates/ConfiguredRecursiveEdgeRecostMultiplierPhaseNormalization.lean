import UnitTangentIterates.ConfiguredRecursiveEdgeDirectRecostPhaseNormalization
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPreCarrier

/-!
# Phase normalization for the multiplier recost source

The multiplier construction reuses the selected inverse, pretransport, gauge,
and spatial reanchoring of the direct recost source.  It changes only density
envelopes and their quantitative certificates.  Consequently the initial
selected rear and terminal unit-tangent datum retain the phase identities
proved for the unscaled source, without making a second successor choice.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierPhaseNormalization

open ConfiguredRecursiveEdgeDirectRecostPhaseNormalization
  ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

variable {P0u khu khatu Qmaxu : ℕ → ℝ} {r : ℕ}
  {S : Stage P0u khu khatu Qmaxu r}
  {p0 kh0 khat0 qmax0 : ℝ}
  {C : ConfiguredRecursiveEdgeRecostedPreCarrier.Core S}
  (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C
    p0 kh0 khat0 qmax0)

/-- Multiplier scaling leaves the complete terminal unit-tangent datum
unchanged. -/
@[simp] theorem source_unitTangentData_eq_unscaled :
    unitTangentData I.source = unitTangentData (unscaled I).source := by
  rfl

/-- Multiplier scaling leaves the time-zero front unchanged. -/
theorem source_front_zero : I.source.F 0 = front S.source 0 := by
  rw [show I.source.F 0 = (unscaled I).source.F 0 by rfl]
  exact ConfiguredRecursiveEdgeDirectRecostPhaseNormalization.source_front_zero
    (unscaled I)

/-- The multiplier source uses the same selected inverse and gauge, hence its
terminal unit-tangent datum has the same explicit phase and reference as the
unscaled direct recost source. -/
theorem source_unitTangentData_eq_shift_selectedRearData :
    unitTangentData I.source = MarkedShift.shiftData
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
        I.selected I.gauge.q C.geometric.output.chosen.Delta.T /
          period S.source C.geometric.output.chosen.Delta.T)
      (S.source.selectedRearData C.geometric.output.chosen.Delta.T) := by
  rw [source_unitTangentData_eq_unscaled I]
  exact
    ConfiguredRecursiveEdgeDirectRecostPhaseNormalization.source_unitTangentData_eq_shift_selectedRearData
      (unscaled I)

/-- Physical phase normalization of the unscaled direct recost source
transports to the multiplier source without another analytic selection. -/
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
  rw [source_selectedRearData_eq_unscaled I]
  exact
    ConfiguredRecursiveEdgeDirectRecostPhaseNormalization.source_initial_eq_shift_physicalRear
      (unscaled I) K hcF hfront hcR hrear frontPhase hF hP

end ConfiguredRecursiveEdgeRecostMultiplierPhaseNormalization
