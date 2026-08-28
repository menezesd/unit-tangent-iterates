import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalInitialData
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalCompositionBase
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalFrontData

/-! # Exact terminal phase linkage for the configured physical base -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePhysicalTerminalPhaseLink

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily
  ConfiguredBaseProfiledSelectedRearGaugeReanchoring
  ConfiguredBaseProfiledSelectedRearReanchoring
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgePhysicalInitialData
  ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  RichStageDataPhaseRigidTransport

variable {MA NA : ℝ}

/-- The actual normalized carrier phase of the terminal source front.  The
selected-rear gauge coordinate is first converted by `sigma`. -/
def sourceTerminalPhase
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : ℝ :=
  let W := edgeOutput O (n + 1)
  let S := edgeSelected O n
  let G := (edgeReanchoredAt O n (initialRearPhase O n)).gauge
  (sigma W S G.q 1 + frontPhase W 1) /
    perim (O.pair.input.carrier (n + 1)).data

/-- Constant-speed carrier traced by the genuine terminal source front. -/
def sourceTerminalData
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : Data :=
  let A := presentation O n
  move A.translation A.rotation (sourceTerminalPhase O n)
    (O.pair.input.carrier (n + 1)).data

/-- Phase taking the next configured intrinsic initial representative to the
actual terminal source-front representative. -/
def terminalFrontPhase
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : ℝ :=
  sourceTerminalPhase O n -
    ConfiguredGaugeFirstPhysicalSequence.rearPhase O.pair.input O.model_data
      (presentation O n) - rearShift O (n + 1)

theorem sourceTerminalData_tube
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    IsTubeMember (ConfiguredCanonicalPairSource.commonC (data O)) 0
      (ConfiguredCanonicalPairSource.commonDlt (data O))
      (sourceTerminalData O n) := by
  unfold sourceTerminalData
  dsimp only
  rw [O.pair.input_carrier (n + 1)]
  exact MarkedRigid.isTubeMember_rigidData (presentation O n).rotation_norm
    (MarkedShift.isTubeMember_shiftData
      (O.pair.carrier_common (n + 1)) (sourceTerminalPhase O n))

theorem sourceTerminalData_perim
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    perim (sourceTerminalData O n) = 2 * (data O).Hs (n + 1) := by
  rw [show perim (sourceTerminalData O n) =
      perim (MarkedShift.shiftData (sourceTerminalPhase O n)
        (O.pair.input.carrier (n + 1)).data) by
    simp [sourceTerminalData, move, MarkedSpace.perim,
      (presentation O n).rotation_norm]]
  rw [SelectedInverseShiftEquivariance.perim_shiftData
    (O.pair.input.carrier (n + 1)).tube]
  exact (O.pair.input.carrier (n + 1)).perim_eq

theorem source_terminal_front_eq_sourceTerminalData
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    (source O C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n).F 1 =
      ev (sourceTerminalData O n) := by
  funext s
  let R := O.pair.input.carrier (n + 1)
  have hper : perim R.data = 2 * (data O).Hs (n + 1) := R.perim_eq
  have hcurve := congrFun R.curve_eq
    (s + sigma (edgeOutput O (n + 1)) (edgeSelected O n)
      (edgeReanchoredAt O n (initialRearPhase O n)).gauge.q 1 +
      frontPhase (edgeOutput O (n + 1)) 1)
  rw [ev, hper] at hcurve
  simp [source, sourceTerminalData, sourceTerminalPhase,
    ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput,
    edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.F,
    ConfiguredBaseProfiledSelectedRearReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearReanchoring.F,
    ConfiguredBaseProfiledSelectedRearReanchoring.rawF,
    MarkingAwareSource.physicalRigidFields, MarkingAwareSource.phaseRigid,
    TimeDependentSpatialReanchoring.shift, ProfiledInterpolationFields.Y,
    sourceK1, R, hper] at hcurve ⊢
  rw [← hcurve]
  rw [ev]
  have hmoveper : perim
      (move (presentation O n).translation (presentation O n).rotation
        (sourceTerminalPhase O n) (O.pair.input.carrier (n + 1)).data) =
      2 * (data O).Hs (n + 1) := by
    simpa [sourceTerminalData] using sourceTerminalData_perim O n
  simp only [sourceTerminalPhase,
    ConfiguredBaseProfiledSelectedRearReanchoring.frontPhase_eq_phase,
    (O.pair.input.carrier (n + 1)).perim_eq] at hmoveper
  rw [hmoveper]
  simp [move, MarkedRigid.rigidData, MarkedShift.shiftData,
    MarkedShift.shiftMap, sourceTerminalPhase]
  congr 3
  field_simp [ne_of_gt ((data O).model.separation_pos (n + 1))] <;>
    first | ring | simp
  all_goals simp

theorem source_terminal_period_eq_sourceTerminalData
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    (source O C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n).P 1 =
      perim (sourceTerminalData O n) := by
  rw [sourceTerminalData_perim]
  change (edgeSourceAt O n (initialRearPhase O n)).P 1 =
    2 * (data O).Hs (n + 1)
  rw [ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily.edgeSourceAt_period_eq]
  rfl

theorem source_path_time_one
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    (ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.sourcePath O C
      (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2) n).T = 1 := by
  simpa [ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.sourcePath] using
    (edgeOutput O (n + 1)).increment_time_one

theorem source_unitTangentData_eq_sourceTerminalData
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    unitTangentData
      (source O C (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) n) =
      sourceTerminalData O n := by
  let Delta := ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.sourcePath
    O C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2) n
  let A := source O C (MA0 := MA0) (NA0 := NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) n
  have hT : Delta.T = 1 := source_path_time_one O C n
  have hF : A.F Delta.T = ev (sourceTerminalData O n) := by
    rw [hT]
    exact source_terminal_front_eq_sourceTerminalData O C n
  have hP : A.P Delta.T = perim (sourceTerminalData O n) := by
    rw [hT]
    exact source_terminal_period_eq_sourceTerminalData O C n
  have hcurve : ∀ u, (unitTangentData A).1 u = (sourceTerminalData O n).1 u := by
    intro u
    change A.F Delta.T (A.P Delta.T * u) = (sourceTerminalData O n).1 u
    rw [hF, ev, hP]
    have hp : perim (sourceTerminalData O n) ≠ 0 :=
      (perim_pos (data O).separation_zero_pos (sourceTerminalData_tube O n)).ne'
    rw [mul_div_cancel_left₀ u hp]
  have hcurveFun : (⇑(unitTangentData A).1) =
      (sourceTerminalData O n).1 := funext hcurve
  have hvel : ∀ u, (unitTangentData A).2.1 u =
      (sourceTerminalData O n).2.1 u := by
    intro u
    have H : HasDerivAt (⇑(unitTangentData A).1)
        ((unitTangentData A).2.1 u) u := by
      simpa only [unitTangentData_curve, unitTangentData_velocity] using
        (normalizedFront_deriv A u)
    rw [hcurveFun] at H
    exact H.unique ((sourceTerminalData_tube O n).hasDerivAt_curve u)
  have hvelFun : (⇑(unitTangentData A).2.1) =
      (sourceTerminalData O n).2.1 := funext hvel
  have hacc : ∀ u, (unitTangentData A).2.2 u =
      (sourceTerminalData O n).2.2 u := by
    intro u
    have H : HasDerivAt (⇑(unitTangentData A).2.1)
        ((unitTangentData A).2.2 u) u := by
      simpa only [unitTangentData_velocity] using
        (normalizedFrontVelocity_deriv A u)
    rw [hvelFun] at H
    exact H.unique ((sourceTerminalData_tube O n).hasDerivAt_vel u)
  apply Prod.ext
  · exact BoundedContinuousFunction.ext hcurve
  · apply Prod.ext
    · exact BoundedContinuousFunction.ext hvel
    · exact BoundedContinuousFunction.ext hacc

theorem sourceTerminalData_eq_shift_initial
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    sourceTerminalData O n = MarkedShift.shiftData
      (terminalFrontPhase O n) (initial O (n + 1)) := by
  unfold sourceTerminalData terminalFrontPhase
    ConfiguredRecursiveEdgePhysicalInitialData.initial
    ConfiguredRecursiveEdgePhysicalInitialData.unshiftedRear
  dsimp only
  rw [MarkedShift.shiftData_add]
  simp only [previousPresentation, presentation]
  unfold RichStageDataPhaseRigidTransport.move
  rw [ConfiguredGaugeFirstPhysicalSequence.shiftData_rigidData,
    MarkedShift.shiftData_add]
  change MarkedRigid.rigidData _ _
      (MarkedShift.shiftData (sourceTerminalPhase O n) _) =
    MarkedRigid.rigidData _ _ (MarkedShift.shiftData _ _)
  congr 3
  ring

theorem source_unitTangentData_eq_shift_initial
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    unitTangentData
      (source O C (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) n) =
      MarkedShift.shiftData (terminalFrontPhase O n) (initial O (n + 1)) :=
  (source_unitTangentData_eq_sourceTerminalData O C n).trans
    (sourceTerminalData_eq_shift_initial O n)

end ConfiguredRecursiveEdgePhysicalTerminalPhaseLink
