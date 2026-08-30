import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteBasePreparedAnalytic
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedIntrinsicCurvature
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierCrossRowPhaseCompatibility
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPhaseNormalization
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalCompositionBase
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalTerminalPhaseLink
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows
import UnitTangentIterates.GaugeMarkedSelectedInverseEndpoint
import UnitTangentIterates.GaugeRearFamilyVariableTerminal

/-!
# First prepared successor over the finite-history base

The physical depth-zero layer and its exact scaled analytic successors are
already theorem-produced.  This module packages them into the first
`PreparedStepData`.  Row geometry, edge budgets, and terminal presentation are
all supplied canonically; the caller does not choose sources, budgets,
displayed successors, or terminal phases.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFiniteBasePreparedStep

open ConfiguredRecursiveEdgeRecostFiniteBasePreparedAnalytic
  ConfiguredRecursiveEdgeRecostFiniteIntrinsicBaseLayer
  ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostFiniteNativePresentedInput
  ConfiguredRecursiveEdgeRecostFinitePreparedIntrinsicCurvature
  ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem
  ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
  ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierCrossRowPhaseCompatibility
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  VariableMarkedTube

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R) {K0 K1 K2 : ℝ}

/-- The canonical pre-core in base row `n`. -/
abbrev basePre (n : ℕ) :=
  ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness.baseNodePre
    (K0 := K0) (K1 := K1) (K2 := K2) H.toClosing n

/-- The theorem-produced scaled successor attached to rows `n` and `n+1`. -/
abbrev baseAnalytic (n : ℕ) :=
  basePreparedAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n

/-- The next displayed datum is canonical: the selected rear of the scaled
successor at its initial time. -/
noncomputable def nextDisplayed (n : ℕ) : Data :=
  (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).source.selectedRearData 0

/-- The selected-source constructor fixes its period ceiling to the configured
successor speed cap.  This is definitional data, not a geometric residual. -/
theorem baseAnalytic_periodUpper_le (n : ℕ) :
    (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).slice.periodUpper ≤
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap H.data (n + 1) := by
  exact (basePreparedAnalytic_periodUpper_eq H n).le

/-- The configured first-flow majorant already dominates the local successor
speed cap.  This is independent of the geometric step data and will be reused
at every recursive depth. -/
theorem edgeSpeedCap_le_stateP1 (q : ℕ) :
    ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap H.data q ≤ stateP1 H q := by
  have hlocal :
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap H.data q =
        ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
          (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
            (J := J)) (H.totalShift + q) := by
    simpa only [H.toClosing_data] using
      (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicAnalyticReadiness.edgeSpeedCap_data_local
        H.toClosing q)
  rw [hlocal]
  refine le_trans ?_ (le_max_right _ _)
  change
    ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
          (J := J)) (H.totalShift + q) ≤
      ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
          (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
            (J := J)) (H.totalShift + q) *
        Real.exp
          (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
              (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
                (J := J)) * 1)
  have hcap : 0 ≤ ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
      (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
        (J := J)) (H.totalShift + q) :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans
      (ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.one_le_edgeSpeedCap
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
          (J := J)) (H.totalShift + q))
  have hexp : 1 ≤ Real.exp
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
          (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
            (J := J)) * 1) :=
    Real.one_le_exp
      (mul_nonneg
        (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat_nonnegative
          (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
            (J := J))) (by norm_num))
  calc
    ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
          (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
            (J := J)) (H.totalShift + q) =
        ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
            (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData
              (J := J)) (H.totalShift + q) * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hcap

/-- The selected analytic period ceiling is therefore bounded by the finite
layer's `P1` majorant without any caller-supplied hypothesis. -/
theorem baseAnalytic_periodUpper_le_P1 (n : ℕ) :
    (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).slice.periodUpper ≤
      stateP1 H (n + 1) :=
  (baseAnalytic_periodUpper_le H n).trans (edgeSpeedCap_le_stateP1 H (n + 1))

private theorem actualPullback_base_rear_geometric_range
    {P0 kh khat Qmax : ℕ → ℝ} {q : ℕ}
    {S : FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.Stage
      P0 kh khat Qmax q}
    (G : FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.GeometricInput S) :
    range (geometricUnitTangent G.base) =
      range (geometricUnitTangent G.output.jets.rear) := by
  have hcont : Continuous G.output.marking.psi :=
    continuous_iff_continuousAt.2 fun u => (G.output.psi_deriv u).continuousAt
  have hmono : StrictMono G.output.marking.psi := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(G.output.psi_deriv u).deriv]
    exact lt_of_lt_of_le G.terminal.lambda_pos (G.output.marking.lower u)
  have hsurj : Surjective G.output.marking.psi :=
    GaugeMarkedSelectedInverseEndpoint.surjective_of_continuous_strictMono_quasiPeriodic
      one_pos hcont hmono G.output.marking.translate G.output.psi_zero
  have hbase : geometricUnitTangent G.base = normalizedUnitTangent G.base := by
    funext u
    rw [geometricUnitTangent, normalizedUnitTangent,
      norm_vel_eq_perim G.terminal.zero_floor_tube u]
  rw [hbase]
  apply Subset.antisymm
  · rintro z ⟨x, rfl⟩
    obtain ⟨u, hu⟩ := hsurj x
    refine ⟨u, ?_⟩
    rw [GaugeRearFamilyVariableTerminal.geometricUnitTangent_eq_normalized_of_orientedReparametrization
      G.terminal.physical.cq_pos G.terminal.lambda_pos
      G.terminal.zero_floor_tube G.output.marking u, hu]
  · rintro z ⟨u, rfl⟩
    exact ⟨G.output.marking.psi u,
      (GaugeRearFamilyVariableTerminal.geometricUnitTangent_eq_normalized_of_orientedReparametrization
        G.terminal.physical.cq_pos G.terminal.lambda_pos
        G.terminal.zero_floor_tube G.output.marking u).symm⟩

/-- The diagonal range edge at depth zero is already carried by the physical
base node and its presented terminal output. -/
theorem base_rawDiagonalRangeEdge (n : ℕ) :
    GeometricUnitTangentRangeEdge
      (nodes (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)).stage.displayed
      (basePre (K0 := K0) (K1 := K1) (K2 := K2) H n).geometric.base := by
  unfold GeometricUnitTangentRangeEdge
  calc
    Set.range
        (nodes (K0 := K0) (K1 := K1) (K2 := K2) H
          (n + 1)).stage.displayed.1 =
      Set.range
        (nodes (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.rear.1 := by
        simpa [nodes] using
          (baseNode_range (K0 := K0) (K1 := K1) (K2 := K2)
            H.toClosing n).symm
    _ = Set.range
        (geometricUnitTangent
          (basePre (K0 := K0) (K1 := K1) (K2 := K2) H
            n).geometric.output.jets.rear) := by
      exact
        (basePre (K0 := K0) (K1 := K1) (K2 := K2) H
          n).geometric.output.stage.range_edge
    _ = Set.range
        (geometricUnitTangent
          (basePre (K0 := K0) (K1 := K1) (K2 := K2) H n).geometric.base) :=
      (actualPullback_base_rear_geometric_range
        (basePre (K0 := K0) (K1 := K1) (K2 := K2) H n).geometric).symm

/-- The multiplier-scaled source mass is paid by the public successor-cell
error; no separate mapped-cost callback is needed at the base step. -/
theorem base_mappedCost_le (n : ℕ) :
    (∫ t in (0 : ℝ)..
      (basePre (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)).path.T,
      (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).source.m t) ≤
        H.error n 1 := by
  change
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).source ≤
      H.error n 1
  refine
    (basePreparedAnalytic_sourceMass_le_allowance
      (K0 := K0) (K1 := K1) (K2 := K2) H n).trans ?_
  rw [← H.toClosing_data]
  simpa only [
    ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing.Output.error,
    Nat.add_assoc] using
    (ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.multiplierRecostSourceAllowance_le_error
      H.toClosing n 1)

/-- Canonical raw metric geometry on the provenance-preserving prepared base. -/
noncomputable def baseRawMetric (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedRawMetricGeometry.RawMetricGeometry.Bounded
      (basePre (K0 := K0) (K1 := K1) (K2 := K2) H n).geometric := by
  simpa [basePre] using
    (ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness.baseNodePreRawMetric
      (K0 := K0) (K1 := K1) (K2 := K2) H.toClosing n)

/-- The physical terminal rear retained by base row `n`, before the finite-tail
index is hidden behind the prepared-node packaging. -/
noncomputable abbrev basePhysicalTerminal (n : ℕ) :=
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.geometry
    (ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
      (K0 := K0) (K1 := K1) (K2 := K2))
    (ConfiguredRecursiveEdgePhysicalBaseFinalTailState.rowOutput
      H.toClosing n).N

/-- The retained physical terminal kinematics have exactly the configured
source curvature cap. -/
noncomputable def baseInitialKinematics (n : ℕ) :
    PhysicalRearLimitKinematics
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
      (basePhysicalTerminal (K0 := K0) (K1 := K1) (K2 := K2) H n).presented
      (basePhysicalTerminal (K0 := K0) (K1 := K1) (K2 := K2) H n).frontData := by
  simpa [ConfiguredRecursiveEdgeSourceP0CappedRowProduction.khRow] using
    (basePhysicalTerminal (K0 := K0) (K1 := K1) (K2 := K2) H n).frontKinematics

/-- Canonical initial phase of the first recost successor.  The preceding
terminal front is shifted back by its physical terminal phase before applying
the selected-rear phase normalization. -/
noncomputable def baseInitialPhase (n : ℕ) : ℝ :=
  FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization.physicalRearPhase
    (baseInitialKinematics (K0 := K0) (K1 := K1) (K2 := K2) H n)
    (-ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.terminalFrontPhase
      J.scalar
      (ConfiguredRecursiveEdgePhysicalBaseFinalTailState.rowOutput
        H.toClosing n).N)

/-- The presented base retained by the prepared node is the same physical
terminal rear used to define the canonical initial phase. -/
theorem basePre_geometricBase_eq_basePhysicalTerminal (n : ℕ) :
    (basePre (K0 := K0) (K1 := K1) (K2 := K2) H n).geometric.base =
      (basePhysicalTerminal (K0 := K0) (K1 := K1) (K2 := K2) H n).presented := by
  change
    ((ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness.baseNodePresentedInput
      (K0 := K0) (K1 := K1) (K2 := K2)
        H.toClosing n).geometricInput).base = _
  rw [ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness.baseNodePresentedInput_geometricInput]
  simp [ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre.baseNodeGeometricInput,
    ConfiguredRecursiveEdgeRecostMultiplierBaseLayer.baseNode,
    ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.geometricInput,
    basePhysicalTerminal]

/-- The selected time-zero rear of the first prepared successor is forced by
the physical row data; no phase callback is needed. -/
theorem baseNextDisplayed_eq_shift (n : ℕ) :
    nextDisplayed (K0 := K0) (K1 := K1) (K2 := K2) H n =
      MarkedShift.shiftData
        (baseInitialPhase (K0 := K0) (K1 := K1) (K2 := K2) H n)
        (basePre (K0 := K0) (K1 := K1) (K2 := K2) H n).geometric.base := by
  let q := (ConfiguredRecursiveEdgePhysicalBaseFinalTailState.rowOutput
    H.toClosing n).N
  let qnext := (ConfiguredRecursiveEdgePhysicalBaseFinalTailState.rowOutput
    H.toClosing (n + 1)).N
  let G := basePhysicalTerminal (K0 := K0) (K1 := K1) (K2 := K2) H n
  let tau := ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.terminalFrontPhase
    J.scalar q
  have hqnext : qnext = q + 1 := by
    simp [qnext, q, Nat.add_assoc]
  have hfrontShift :
      G.frontData = MarkedShift.shiftData tau
        (ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar (q + 1)) := by
    calc
      G.frontData =
          FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
            ((ConfiguredRecursiveEdgePhysicalGeometricBase.base J
              (K0 := K0) (K1 := K1) (K2 := K2)).source q) := by
        simpa [G, basePhysicalTerminal, q] using G.frontData_eq
      _ = MarkedShift.shiftData
          (ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.terminalFrontPhase
            J.scalar q)
          ((ConfiguredRecursiveEdgePhysicalGeometricBase.base J
            (K0 := K0) (K1 := K1) (K2 := K2)).initial (q + 1)) := by
        simpa [ConfiguredRecursiveEdgePhysicalGeometricBase.base,
          ConfiguredRecursiveEdgePhysicalGeometricBase.base_initial,
          ConfiguredRecursiveEdgePhysicalCompositionBase.compositionBaseCorrelated_source,
          ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated_source,
          ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource] using
          (ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.source_unitTangentData_eq_shift_initial
              J.scalar
              (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
              (MA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
              (NA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
              (K0 := K0) (K1 := K1) (K2 := K2) q)
      _ = MarkedShift.shiftData tau
          (ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar (q + 1)) := by
        simp [tau]
  have hfrontTerminal :
      G.frontData =
        ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.sourceTerminalData
          J.scalar q := by
    calc
      G.frontData = MarkedShift.shiftData tau
          (ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar (q + 1)) :=
        hfrontShift
      _ = ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.sourceTerminalData
          J.scalar q := by
        simpa [tau] using
          (ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.sourceTerminalData_eq_shift_initial
            J.scalar q).symm
  have hfrontTube :
      IsTubeMember
        (ConfiguredCanonicalPairSource.commonC
          (ConfiguredBaseProfiledEdgeSourceFamily.data J.scalar)) 0
        (ConfiguredCanonicalPairSource.commonDlt
          (ConfiguredBaseProfiledEdgeSourceFamily.data J.scalar))
        G.frontData := by
    rw [hfrontTerminal]
    exact
      ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.sourceTerminalData_tube
        J.scalar q
  have hcF : 0 < ConfiguredCanonicalPairSource.commonC
      (ConfiguredBaseProfiledEdgeSourceFamily.data J.scalar) :=
    (ConfiguredBaseProfiledEdgeSourceFamily.data J.scalar).separation_zero_pos
  have hsource :
      (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source =
        ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source
          J.scalar
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
          (MA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
          (NA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) qnext := by
    change
      (ConfiguredRecursiveEdgePhysicalCompositionBase.compositionBaseCorrelated
        J (K0 := K0) (K1 := K1) (K2 := K2)).source qnext = _
    rfl
  have hsourceFront :
      FiniteSmoothRearFamilyMarkingAwareSuccessorFront.front
          (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source 0 =
        ev (ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar qnext) := by
    rw [hsource]
    funext x
    simpa [FiniteSmoothRearFamilyMarkingAwareSuccessorFront.front] using
      (ConfiguredRecursiveEdgePhysicalInitialData.rearOwn_zero_eq_initial_ev
        J.scalar
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
        (MA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
        (NA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) qnext x)
  have hsourcePeriod :
      FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period
          (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source 0 =
        perim (ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar qnext) := by
    rw [hsource]
    simpa [FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period] using
      (ConfiguredRecursiveEdgePhysicalInitialData.rearPeriod_zero_eq_initial_perim
        J.scalar
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
        (MA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
        (NA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) qnext)
  have hF :
      FiniteSmoothRearFamilyMarkingAwareSuccessorFront.front
          (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source 0 =
        ev (MarkedShift.shiftData (-tau) G.frontData) := by
    rw [hsourceFront, hqnext, hfrontShift, MarkedShift.shiftData_add]
    simp
  have hP :
      FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period
          (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source 0 =
        perim G.frontData := by
    calc
      _ = perim (ConfiguredRecursiveEdgePhysicalInitialData.initial
          J.scalar qnext) := hsourcePeriod
      _ = perim (ConfiguredRecursiveEdgePhysicalInitialData.initial
          J.scalar (q + 1)) := by rw [hqnext]
      _ = perim
          (ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.sourceTerminalData
            J.scalar q) := by
        rw [ConfiguredRecursiveEdgePhysicalInitialData.initial_perim_eq,
          ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.sourceTerminalData_perim]
      _ = perim G.frontData := (congrArg perim hfrontTerminal).symm
  have hphase :=
    ConfiguredRecursiveEdgeRecostMultiplierPhaseNormalization.source_initial_eq_shift_physicalRear
        (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n)
        (baseInitialKinematics (K0 := K0) (K1 := K1) (K2 := K2) H n)
        hcF hfrontTube G.physical.cq_pos G.zero_floor_tube
        (-tau) hF hP
  rw [basePre_geometricBase_eq_basePhysicalTerminal
    (K0 := K0) (K1 := K1) (K2 := K2) H n]
  simpa [nextDisplayed, baseInitialPhase, G, tau, q] using hphase

/-- The terminal phase is forced by the current terminal gauge and the next
row's initial phase. -/
noncomputable def terminalPhase (n : ℕ) : ℝ :=
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeGeometry.sigma
      (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).selected
      (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).gauge.q
      (basePre (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)).geometric.output.chosen.Delta.T /
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period
      (nodes (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)).stage.source
      (basePre (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)).geometric.output.chosen.Delta.T -
    baseInitialPhase (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)

/-- All fields of the finite-history intrinsic step are assembled canonically
from the base analytic and raw-metric constructions. -/
noncomputable def inputData :
    InputData J H (ConfiguredRecursiveEdgeRecostFiniteIntrinsicBaseLayer.budget H)
      (layer (K0 := K0) (K1 := K1) (K2 := K2) H) where
  pre := basePre (K0 := K0) (K1 := K1) (K2 := K2) H
  analytic := baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H
  eps_le := basePreparedAnalytic_eps_le H
  periodUpper_le := baseAnalytic_periodUpper_le H
  periodUpper_le_P1 := baseAnalytic_periodUpper_le_P1 H
  rawMetric := baseRawMetric (K0 := K0) (K1 := K1) (K2 := K2) H
  edgeBudget_le_error := fun n ↦ by
    simpa [baseRawMetric,
      ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing.Output.error,
      Nat.add_assoc] using
      (ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness.baseNodePreRawMetric_edgeBudget_le_error
          (K0 := K0) (K1 := K1) (K2 := K2) H.toClosing n)
  nextDisplayed := nextDisplayed (K0 := K0) (K1 := K1) (K2 := K2) H
  terminalFrontReference := fun n ↦
    nextDisplayed (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)
  terminalFrontPhase :=
    terminalPhase (K0 := K0) (K1 := K1) (K2 := K2) H
  terminalFront_eq_phase := fun n ↦ by
    simpa [baseAnalytic, basePre, nextDisplayed, terminalPhase] using
      (source_unitTangentData_eq_shift_nextInitial
        (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n)
        (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1))
        (baseInitialPhase (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1))
        (baseNextDisplayed_eq_shift
          (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)))

/-- The first prepared source obeys the configured curvature ceiling by the
same intrinsic model-distance argument used at every later depth. -/
theorem base_mappedRearCurvature_le (n : ℕ) (t s : ℝ) :
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).source t s| ≤
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh := by
  let I := inputData (K0 := K0) (K1 := K1) (K2 := K2) H
  let F : Input.RecursiveFacts
      (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n) :=
    Input.RecursiveFacts.ofTerminal
      (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n)
      (ConfiguredRecursiveEdgeRecostFiniteBasePreparedAnalytic.basePreparedAnalytic_terminalCurvature_nonnegative
          (K0 := K0) (K1 := K1) (K2 := K2) H n)
      (ConfiguredRecursiveEdgeRecostFiniteBasePreparedAnalytic.basePreparedAnalytic_terminalRange
          (K0 := K0) (K1 := K1) (K2 := K2) H n)
  let B : BoundaryFacts I n (H.error n 1) :=
    { recursiveFacts := F
      displayed_eq := rfl
      cost_le := base_mappedCost_le H n }
  let P := B.presentedInput
  let A :=
    (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).source
  let phase :=
    -baseInitialPhase (K0 := K0) (K1 := K1) (K2 := K2) H n
  let model := MarkedShift.shiftData (-phase)
    (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n)
  have hcoherent :
      dist (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n)
          (MarkedShift.shiftData phase (A.selectedRearData 0)) ≤
        H.toClosing.radius n := by
    have hstep :=
      ConfiguredRecursiveEdgeRecostFinitePreparedReachableSystem.PreparedStepData.coherentDistance_step
        (Z := preparedBase (K0 := K0) (K1 := K1) (K2 := K2) H) H I
        (baseInitialPhase (K0 := K0) (K1 := K1) (K2 := K2) H)
        (baseNextDisplayed_eq_shift
          (K0 := K0) (K1 := K1) (K2 := K2) H) n
    refine (show
      dist (ConfiguredRecursiveEdgeRecostMultiplierRowBudget.base H.toClosing n)
          (MarkedShift.shiftData phase (A.selectedRearData 0)) ≤
        ∑ j ∈ Finset.range 1, H.error n j by
          simpa only [phase, preparedBase_coherentPhase, zero_sub] using hstep).trans ?_
    simpa [ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing.Output.error]
      using ConfiguredRecursiveEdgeRecostMultiplierRowBudget.error_partialSum_le_radius
        H.toClosing n 1
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
      (FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.selectedRearData_tube
        A 0)
  have hmass : (∫ tau in (0 : ℝ)..1, A.m tau) ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.configuredCurvatureSourceMassBudget := by
    have hm := (basePreparedAnalytic_sourceMass_le_allowance
      (K0 := K0) (K1 := K1) (K2 := K2) H n).trans
        (H.mass_curvature_final (n + 1))
    have hT :
        (ConfiguredRecursiveEdgeRecostFiniteBasePreparedAnalytic.sourceCore
          (K0 := K0) (K1 := K1) (K2 := K2) H n).path.T = 1 :=
      (ConfiguredRecursiveEdgeRecostFiniteBasePreparedAnalytic.sourceCore
        (K0 := K0) (K1 := K1) (K2 := K2) H n).time_one
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
    A P.output.chosen F.spatial
      (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).slice
      P.path_time_one hmodel hp (positive_speed_margin H.toClosing n)
      hmodelAcc hdist (initial_ratio_le_kbar H.toClosing n) hsmall t s

/-- The unconditional first actual successor of the theorem-produced prepared
base. -/
noncomputable def preparedStep :
    PreparedStepData H
      (preparedBase (K0 := K0) (K1 := K1) (K2 := K2) H) where
  input := inputData (K0 := K0) (K1 := K1) (K2 := K2) H
  pre_eq := fun _ ↦ rfl
  recursiveFacts := fun n =>
    Input.RecursiveFacts.ofTerminal
      (baseAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n)
      (ConfiguredRecursiveEdgeRecostFiniteBasePreparedAnalytic.basePreparedAnalytic_terminalCurvature_nonnegative
          (K0 := K0) (K1 := K1) (K2 := K2) H n)
      (ConfiguredRecursiveEdgeRecostFiniteBasePreparedAnalytic.basePreparedAnalytic_terminalRange
          (K0 := K0) (K1 := K1) (K2 := K2) H n)
  nextDisplayed_eq_selected := fun _ ↦ rfl
  mappedCost_le := base_mappedCost_le H
  mappedRearCurvature_le := base_mappedRearCurvature_le H
  initialPhase := baseInitialPhase (K0 := K0) (K1 := K1) (K2 := K2) H
  nextDisplayed_eq_phase :=
    baseNextDisplayed_eq_shift (K0 := K0) (K1 := K1) (K2 := K2) H
  rawDiagonalRangeEdge := base_rawDiagonalRangeEdge H
  terminalReference_eq := fun _ ↦ rfl

/-- The theorem-produced prepared base has an unconditional first successor. -/
theorem exists_preparedStep :
    Nonempty (PreparedStepData H
      (preparedBase (K0 := K0) (K1 := K1) (K2 := K2) H)) :=
  ⟨preparedStep (K0 := K0) (K1 := K1) (K2 := K2) H⟩

end ConfiguredRecursiveEdgeRecostFiniteBasePreparedStep
