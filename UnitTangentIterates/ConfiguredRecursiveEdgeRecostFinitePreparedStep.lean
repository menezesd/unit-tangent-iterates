import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedInitialPhase
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteBasePreparedStep
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedNextMetric
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedIntrinsicCurvature
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierCrossRowPhaseCompatibility
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPhaseNormalization
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction
import UnitTangentIterates.VariableMarkedTube

/-! # Intrinsic prepared-step data at arbitrary finite depth

`BridgeData` already contains the analytic allowance package and the geometric
provenance of a reached finite layer.  This file assembles every unconditional
field of the next intrinsic input directly from those objects.

The canonical intrinsic input below displays the time-zero selected rear of
the newly recosted analytic source.  The prepared initial-phase theorem
identifies that rear with a marked shift of the retained geometric base.  The
terminal phase is compensated by the following analytic source's initial
phase, so the terminal reference and selected-rear fields are structural.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFinitePreparedStep

open ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic
  ConfiguredRecursiveEdgeRecostFinitePreparedIntrinsicCurvature
  ConfiguredRecursiveEdgeRecostFinitePreparedGeometrySchema
  ConfiguredRecursiveEdgeRecostFinitePreparedInitialPhase
  ConfiguredRecursiveEdgeRecostFiniteNativePresentedInput
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareSource
  VariableMarkedTube

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R)

/-- The selected analytic ceiling is the configured ceiling of its source
node, expressed in the local coordinates of the history-closing output. -/
theorem preparedAnalytic_periodUpper_le_local
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (preparedAnalytic H D n).slice.periodUpper ≤
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap H.data
        (localIndex n k) := by
  calc
    (preparedAnalytic H D n).slice.periodUpper ≤
        ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
          (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
            (J := J)) (diagonal H n (k + 1)) :=
      (ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic.preparedAnalytic_periodUpper_eq
        H D n).le
    _ = ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap H.data
        (localIndex n k) := by
      have hlocal :
          ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap H.data (localIndex n k) =
            ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
              (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
                (J := J)) (H.totalShift + localIndex n k) := by
        simpa only [H.toClosing_data] using
          (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness.edgeSpeedCap_data_local
            H.toClosing (localIndex n k))
      rw [hlocal]
      congr 1
      simp [localIndex,
        ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.diagonal,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The same ceiling at the global diagonal expected by finite intrinsic
`InputData`. -/
theorem preparedAnalytic_periodUpper_le
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (preparedAnalytic H D n).slice.periodUpper ≤
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
          (J := J)) (diagonal H n (k + 1)) :=
  (ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic.preparedAnalytic_periodUpper_eq
    H D n).le

/-- The base scalar comparison is depth-independent, so it also closes the
finite-layer `P1` field at arbitrary depth. -/
theorem preparedAnalytic_periodUpper_le_P1
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (preparedAnalytic H D n).slice.periodUpper ≤
      stateP1 H (n + (k + 1)) := by
  simpa [localIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (preparedAnalytic_periodUpper_le_local H D n).trans
      (ConfiguredRecursiveEdgeRecostFiniteBasePreparedStep.edgeSpeedCap_le_stateP1
        H (localIndex n k))

/-- Canonical terminal phase of the strengthened analytic input relative to
the presented rear of its predecessor source. -/
noncomputable def intrinsicTerminalFrontPhase
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) : ℝ :=
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
      (preparedAnalytic H D n).selected
      (preparedAnalytic H D n).gauge.q
      (sourceCore H Z n).geometric.output.chosen.Delta.T /
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period
      (sourceNode H Z n).stage.source
      (sourceCore H Z n).geometric.output.chosen.Delta.T

/-- Gauge normalization and the native geometric input identify the analytic
terminal datum with the canonical presented rear. -/
theorem preparedAnalytic_terminalFront_eq_phase
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    unitTangentData (preparedAnalytic H D n).source =
      MarkedShift.shiftData (intrinsicTerminalFrontPhase H D n)
        (Z.pre H (n + 1)).geometric.base := by
  simpa only [intrinsicTerminalFrontPhase, sourceCore, sourceNode,
    ConfiguredRecursiveEdgeRecostMultiplierCrossRowPhaseCompatibility.GeometricInput.selectedRearData_terminal_eq_base] using
    (ConfiguredRecursiveEdgeRecostMultiplierPhaseNormalization.source_unitTangentData_eq_shift_selectedRearData
        (preparedAnalytic H D n))

/-- The terminal phase relative to the following prepared analytic source's
time-zero selected rear.  Its initial phase is subtracted so composition
recovers `intrinsicTerminalFrontPhase`. -/
noncomputable def intrinsicTerminalFrontPhaseToNext
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) : ℝ :=
  intrinsicTerminalFrontPhase H D n -
    preparedAnalyticInitialPhase H D (n + 1)

/-- The current prepared analytic terminal datum is the compensated shift of
the following prepared analytic source's selected rear. -/
theorem preparedAnalytic_terminalFront_eq_nextSelectedRear
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    unitTangentData (preparedAnalytic H D n).source =
      MarkedShift.shiftData (intrinsicTerminalFrontPhaseToNext H D n)
        ((preparedAnalytic H D (n + 1)).source.selectedRearData 0) := by
  rw [preparedAnalytic_selectedRearData_zero_eq_shift_base H D (n + 1)]
  simpa [intrinsicTerminalFrontPhaseToNext,
    MarkedShift.shiftData_add] using
    (preparedAnalytic_terminalFront_eq_phase H D n)

/-- The analytic allowance rewritten exactly in the `O.data` coordinates and
shifted index consumed by `PreparedNextMetric.nextRawMetric`. -/
theorem preparedAnalytic_sourceMass_le_allowance_shifted
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        (preparedAnalytic H D n).source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance O.data
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
          (H.toClosing.preShift + H.toClosing.large.N +
            (n + (k + 1))) := by
  refine (ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic.preparedAnalytic_sourceMass_le_allowance
    H D n).trans_eq ?_
  simp only [ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.data,
    ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data,
    ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.data]
  simp_rw [ConfiguredRecursiveEdgeRecostFiniteHistoryJetBudget.multiplierRecostSourceAllowance_shift]
  simp [ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.totalShift,
    localIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The unshifted allowance is one summand of the public successor-cell
error, giving the mapped-cost field independently of phase closure. -/
theorem preparedAnalytic_mappedCost_le
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (∫ t in (0 : ℝ)..(Z.pre H (n + 1)).path.T,
      (preparedAnalytic H D n).source.m t) ≤ H.error n (k + 1) := by
  change FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
    (preparedAnalytic H D n).source ≤ H.error n (k + 1)
  refine (ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic.preparedAnalytic_sourceMass_le_allowance
    H D n).trans ?_
  simpa [localIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.multiplierRecostSourceAllowance_le_error
      H.toClosing n (k + 1))

/-- Recursive sidecars and terminal facts retained by `preparedAnalytic`. -/
noncomputable def recursiveFacts
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    Input.RecursiveFacts (preparedAnalytic H D n) :=
  Input.RecursiveFacts.ofTerminal
    (preparedAnalytic H D n)
    (ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic.preparedAnalytic_terminalCurvature_nonnegative
      H D n)
    (ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic.preparedAnalytic_terminalRange
      H D n)

/-- Unconditional arbitrary-depth intrinsic input.  Its displayed datum is
the prepared analytic source's selected rear at time zero. -/
noncomputable def inputData
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) :
    ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.InputData
      J H (budget H) Z.layer where
  pre := Z.pre H
  analytic := preparedAnalytic H D
  eps_le := ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic.preparedAnalytic_eps_le H D
  periodUpper_le := preparedAnalytic_periodUpper_le H D
  periodUpper_le_P1 := preparedAnalytic_periodUpper_le_P1 H D
  rawMetric := D.geometry.rawMetric
  edgeBudget_le_error := D.geometry.edgeBudget_le_error
  nextDisplayed := fun n =>
    (preparedAnalytic H D n).source.selectedRearData 0
  terminalFrontReference := fun n =>
    (preparedAnalytic H D (n + 1)).source.selectedRearData 0
  terminalFrontPhase := intrinsicTerminalFrontPhaseToNext H D
  terminalFront_eq_phase :=
    preparedAnalytic_terminalFront_eq_nextSelectedRear H D

/-- The shifted allowance in the literal family shape accepted by
`PreparedNextMetric.nextRawMetric`. -/
theorem inputData_sourceMass_le_allowance
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        ((inputData H D).analytic n).source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance O.data
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
          (H.toClosing.preShift + H.toClosing.large.N +
            (n + (k + 1))) := by
  intro n
  exact preparedAnalytic_sourceMass_le_allowance_shifted H D n

/-- The configured half-curvature model, coherent metric prefix, and selected
source-mass tail discharge the successor curvature bound intrinsically. -/
theorem preparedAnalytic_mappedRearCurvature_le
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) (t s : ℝ) :
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (preparedAnalytic H D n).source t s| ≤
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh := by
  let I := inputData H D
  let B : BoundaryFacts I n (H.error n (k + 1)) :=
    { recursiveFacts := recursiveFacts H D n
      displayed_eq := rfl
      cost_le := preparedAnalytic_mappedCost_le H D n }
  let P := B.presentedInput
  let A := (preparedAnalytic H D n).source
  let phase := Z.coherentPhase n - preparedAnalyticInitialPhase H D n
  let model := MarkedShift.shiftData (-phase)
    (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n)
  have hcoherent :
      dist (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n)
          (MarkedShift.shiftData phase (A.selectedRearData 0)) ≤
        H.toClosing.radius n := by
    refine (ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem.PreparedStepData.coherentDistance_step
      H I (preparedAnalyticInitialPhase H D)
      (preparedAnalytic_selectedRearData_zero_eq_shift_base H D) n).trans ?_
    simpa [ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing.Output.error]
      using ConfiguredRecursiveEdgeRecostMultiplierRowBudget.error_partialSum_le_radius
        H.toClosing n (k + 1)
  have hdist : dist model (A.selectedRearData 0) ≤ H.toClosing.radius n := by
    calc
      dist model (A.selectedRearData 0) =
          dist (MarkedShift.shiftData (-phase)
              (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base
                H.toClosing n))
            (MarkedShift.shiftData (-phase)
              (MarkedShift.shiftData phase (A.selectedRearData 0))) := by
                simp [model, MarkedShift.shiftData_add]
      _ = dist (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base
              H.toClosing n)
            (MarkedShift.shiftData phase (A.selectedRearData 0)) :=
        FiniteSmoothRearFamilyMarkingAwareCorrelatedPresentedInfiniteArray.dist_shiftData
          _ _ _
      _ ≤ H.toClosing.radius n := hcoherent
  have hmodel : IsTubeMember (2 * H.toClosing.data.Hs n) 0 0 model := by
    exact MarkedShift.isTubeMember_shiftData
      (configuredBase_exact_tube H.toClosing n) (-phase)
  have hmodelAcc : ∀ u,
      ‖model.2.2 u‖ ≤ (2 * H.toClosing.data.Hs n) ^ 2 * (1 / 2) := by
    intro u
    simpa [model, MarkedShift.shiftData] using
      (configuredBase_acceleration_le_half H.toClosing n (u - phase))
  have hp : IsVariableTubeMember
      (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A 0)
      (perim (A.selectedRearData 0)) 0 0 (A.selectedRearData 0) :=
    variableTube_of_tube
      (MarkingAwareSource.selectedRearData_tube A 0)
  have hmass : (∫ tau in (0 : ℝ)..1, A.m tau) ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.configuredCurvatureSourceMassBudget := by
    have hm := (ConfiguredRecursiveEdgeRecostFinitePreparedAnalytic.preparedAnalytic_sourceMass_le_allowance
      H D n).trans
        (H.mass_curvature_final (localIndex n k))
    have hT : (sourceCore H Z n).path.T = 1 := (sourceCore H Z n).time_one
    rw [FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass,
      hT] at hm
    simpa [A] using hm
  have hsmall :
      (A.d + 2 +
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh ^ 2) *
          (∫ tau in (0 : ℝ)..1, A.m tau) <
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh -
          TubeConstants.kbar (1 / 2) := by
    change ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.configuredCurvatureSourceMassCoeff *
          (∫ tau in (0 : ℝ)..1, A.m tau) < _
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hmass
        ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.configuredCurvatureSourceMassCoeff_nonnegative)
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.configuredCurvatureSourceMassBudget_curvature
  exact all_real_intrinsic_le_sourceKh_of_canonicalModel
    A P.output.chosen (recursiveFacts H D n).spatial
      (preparedAnalytic H D n).slice P.path_time_one
      hmodel hp (positive_speed_margin H.toClosing n) hmodelAcc hdist
      (initial_ratio_le_kbar H.toClosing n) hsmall t s

/-- Existing displayed provenance remains available as a complete marked-data
identity, independently of the new analytic source. -/
theorem reachable_displayed_eq_selected
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (Z.nodes n).stage.displayed =
      (Z.nodes n).stage.source.selectedRearData 0 :=
  D.geometry.displayed_eq_selected n

/-- The retained terminal front is the retained phase shift of the following
configured node's selected rear.  This records exactly what the geometric
provenance proves, without identifying it with the new analytic initial rear. -/
theorem reachable_terminalFront_eq_phase_selected
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (Z.presented n).terminal.frontData =
      MarkedShift.shiftData (D.geometry.terminalFrontPhase n)
        ((Z.nodes (n + 1)).stage.source.selectedRearData 0) := by
  rw [D.geometry.terminalFront_eq_phase n,
    D.geometry.displayed_eq_selected (n + 1)]

/-- The same phase statement with the terminal front rewritten to its source
reference. -/
theorem reachable_sourceTerminal_eq_phase_selected
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    unitTangentData (Z.nodes n).stage.source =
      MarkedShift.shiftData (D.geometry.terminalFrontPhase n)
        ((Z.nodes (n + 1)).stage.source.selectedRearData 0) := by
  rw [← D.geometry.frontData_eq_source n]
  exact reachable_terminalFront_eq_phase_selected H D n

/-- Every `PreparedStepData` field has an unconditional proof for
`inputData`. -/
theorem inputData_pre_eq
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (inputData H D).pre n = Z.pre H n := rfl

theorem inputData_nextDisplayed_eq_selected
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (inputData H D).nextDisplayed n =
      ((inputData H D).analytic n).source.selectedRearData 0 := rfl

theorem inputData_mappedCost_le
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (∫ t in (0 : ℝ)..((inputData H D).pre (n + 1)).path.T,
      ((inputData H D).analytic n).source.m t) ≤ H.error n (k + 1) :=
  preparedAnalytic_mappedCost_le H D n

theorem inputData_nextDisplayed_eq_phase
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (inputData H D).nextDisplayed n =
      MarkedShift.shiftData (preparedAnalyticInitialPhase H D n)
        ((inputData H D).pre n).geometric.base := by
  change (preparedAnalytic H D n).source.selectedRearData 0 =
    MarkedShift.shiftData (preparedAnalyticInitialPhase H D n)
      (Z.pre H n).geometric.base
  exact preparedAnalytic_selectedRearData_zero_eq_shift_base H D n

theorem inputData_rawDiagonalRangeEdge
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    VariableMarkedTube.GeometricUnitTangentRangeEdge
      (Z.nodes (n + 1)).stage.displayed
      ((inputData H D).pre n).geometric.base :=
  D.geometry.rawDiagonalRangeEdge n

theorem inputData_terminalReference_eq
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) (n : ℕ) :
    (inputData H D).terminalFrontReference n =
      (inputData H D).nextDisplayed (n + 1) := rfl

/-- The unconditional prepared step at arbitrary finite depth. -/
noncomputable def preparedStep
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) : PreparedStepData H Z where
  input := inputData H D
  pre_eq := inputData_pre_eq H D
  recursiveFacts := recursiveFacts H D
  nextDisplayed_eq_selected := inputData_nextDisplayed_eq_selected H D
  mappedCost_le := inputData_mappedCost_le H D
  mappedRearCurvature_le := preparedAnalytic_mappedRearCurvature_le H D
  initialPhase := preparedAnalyticInitialPhase H D
  nextDisplayed_eq_phase := inputData_nextDisplayed_eq_phase H D
  rawDiagonalRangeEdge := inputData_rawDiagonalRangeEdge H D
  terminalReference_eq := inputData_terminalReference_eq H D

/-- Every finite prepared bridge has an unconditional prepared successor
step. -/
theorem exists_preparedStep
    {k : ℕ} {Z : PreparedReachable H k}
    (D : BridgeData H Z) : Nonempty (PreparedStepData H Z) :=
  ⟨preparedStep H D⟩

end ConfiguredRecursiveEdgeRecostFinitePreparedStep
