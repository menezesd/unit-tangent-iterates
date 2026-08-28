import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPhaseNormalization
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackStages

/-!
# Cross-row phase compatibility for multiplier recost sources

The terminal selected rear of a canonical geometric row is its presented
base.  If the following multiplier source is initially normalized against
that base, the preceding multiplier source's terminal unit-tangent datum is
therefore a single explicit phase shift of the following source's actual
initial datum.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierCrossRowPhaseCompatibility

open ConfiguredRecursiveEdgeRecostMultiplierPhaseNormalization
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

/-- A canonical geometric input presents the predecessor source's terminal
selected rear exactly, including its marked velocity and acceleration. -/
theorem GeometricInput.selectedRearData_terminal_eq_base
    {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
    {S : Stage P0 kh khat Qmax j} (G : GeometricInput S) :
    S.source.selectedRearData G.output.chosen.Delta.T = G.base := by
  have hperiod : rearPeriod S.source G.output.chosen.Delta.T = perim G.base := by
    rw [G.output.chosen.time_eq]
    exact G.terminal.rearPeriod_terminal
  have hper_ne : perim G.base ≠ 0 := by
    rw [← hperiod]
    exact (S.source.rear_period_pos G.output.chosen.Delta.T).ne'
  have hcurve : ∀ u,
      (S.source.selectedRearData G.output.chosen.Delta.T).1 u = G.base.1 u := by
    intro u
    rw [FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.selectedRearData_curve,
      FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.selectedRearCurve]
    rw [G.output.chosen.time_eq]
    rw [← G.terminal.terminal_carrier (rearPeriod S.source S.Gamma.T * u)]
    rw [show rearPeriod S.source S.Gamma.T = perim G.base by
      simpa [G.output.chosen.time_eq] using hperiod]
    field_simp
  have hcurveFun :
      (⇑(S.source.selectedRearData G.output.chosen.Delta.T).1) = G.base.1 :=
    funext hcurve
  have hvel : ∀ u,
      (S.source.selectedRearData G.output.chosen.Delta.T).2.1 u =
        G.base.2.1 u := by
    intro u
    have H := S.source.selectedRearData_curve_deriv
      G.output.chosen.Delta.T u
    rw [hcurveFun] at H
    exact H.unique (G.terminal.zero_floor_tube.hasDerivAt_curve u)
  have hvelFun :
      (⇑(S.source.selectedRearData G.output.chosen.Delta.T).2.1) =
        G.base.2.1 := funext hvel
  have hacc : ∀ u,
      (S.source.selectedRearData G.output.chosen.Delta.T).2.2 u =
        G.base.2.2 u := by
    intro u
    have H := S.source.selectedRearData_velocity_deriv
      G.output.chosen.Delta.T u
    rw [hvelFun] at H
    exact H.unique (G.terminal.zero_floor_tube.hasDerivAt_vel u)
  apply Prod.ext
  · exact BoundedContinuousFunction.ext hcurve
  · apply Prod.ext
    · exact BoundedContinuousFunction.ext hvel
    · exact BoundedContinuousFunction.ext hacc

variable {P0u khu khatu Qmaxu : ℕ → ℝ} {r : ℕ}
  {S : Stage P0u khu khatu Qmaxu r}
  {p0 kh0 khat0 qmax0 : ℝ}
  {C : Core S}
  (I : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C
    p0 kh0 khat0 qmax0)

variable {P0u' khu' khatu' Qmaxu' : ℕ → ℝ} {r' : ℕ}
  {S' : Stage P0u' khu' khatu' Qmaxu' r'}
  {p0' kh0' khat0' qmax0' : ℝ}
  {C' : Core S'}
  (I' : ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input C'
    p0' kh0' khat0' qmax0')

/-- Compose the retained terminal gauge phase with the inverse of the next
row's initial phase.  This is the exact `terminalFront_eq_phase` field needed
by a rowwise intrinsic step when its terminal reference is the following
row's actual displayed datum. -/
theorem source_unitTangentData_eq_shift_nextInitial
    (initialPhase : ℝ)
    (hinitial : I'.source.selectedRearData 0 =
      MarkedShift.shiftData initialPhase C.geometric.base) :
    unitTangentData I.source = MarkedShift.shiftData
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
          I.selected I.gauge.q C.geometric.output.chosen.Delta.T /
          FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period
            S.source C.geometric.output.chosen.Delta.T - initialPhase)
      (I'.source.selectedRearData 0) := by
  rw [source_unitTangentData_eq_shift_selectedRearData I]
  rw [ConfiguredRecursiveEdgeRecostMultiplierCrossRowPhaseCompatibility.GeometricInput.selectedRearData_terminal_eq_base
    C.geometric]
  rw [hinitial, MarkedShift.shiftData_add]
  congr 1
  ring

end ConfiguredRecursiveEdgeRecostMultiplierCrossRowPhaseCompatibility
