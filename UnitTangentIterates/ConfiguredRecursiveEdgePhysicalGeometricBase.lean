import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalCompositionBase
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalInitialData
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalTerminalPhaseLink
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalBaseCurvature
import UnitTangentIterates.ConfiguredRecursiveEdgeExactAutomaticRowFacts
import UnitTangentIterates.ConfiguredRecursiveEdgeReachableQmax
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion

/-! # Transition-free physical geometric base column -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePhysicalGeometricBase

open ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgePhysicalInitialData
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
  ConfiguredRecursiveEdgeSourceP0Growth
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedSlicedInvariant
  RichStageDataPhaseRigidTransport

variable {MA NA : ℝ}

private theorem range_move (a w : ℂ) (q : ℝ) (p : Data) :
    range (move a w q p).1 = (fun z ↦ a + w * z) '' range p.1 := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨p.1 (u + q), ⟨u + q, rfl⟩, by
      simp [move, MarkedRigid.rigidData, MarkedShift.shiftData,
        MarkedShift.shiftMap]⟩
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨u - q, ?_⟩
    simp [move, MarkedRigid.rigidData, MarkedShift.shiftData,
      MarkedShift.shiftMap]

/-- The range representative retained by the configured `ColumnStep`. -/
noncomputable def baseCurrent
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) : Data :=
  (compositionBaseCorrelated J (K0 := K0) (K1 := K1)
    (K2 := K2)).column.step.next n

/-- The physical-step rear and the configured nonaffinely marked terminal
rear have the same unmarked range. -/
theorem unshiftedRear_range_baseCurrent
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    range (unshiftedRear J.scalar n).1 =
      range (baseCurrent J (K0 := K0) (K1 := K1) (K2 := K2) n).1 := by
  let A := previousPresentation J.scalar n
  let W := ConfiguredGaugeFirstPhysicalSequence.output
    J.scalar.pair.input J.scalar.model_data n
  have hphysical := ConfiguredGaugeFirstPhysicalSequence.terminalBase_eq_physicalRear
    J.scalar.pair.input J.scalar.model_data n
  have hmark :=
    ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily.range_of_normalizedMarking
      W.marking
  change range (unshiftedRear J.scalar n).1 =
    range (ConfiguredGaugeFirstPhysicalSequence.movedRear
      J.scalar.pair.input J.scalar.model_data n).1
  calc
    range (unshiftedRear J.scalar n).1 =
        range (move A.translation A.rotation
          (W.marking.marking.psi A.phase) W.terminalBase).1 := by
      simpa [unshiftedRear, previousPresentation, A, W] using
        congrArg (fun p : Data ↦ range p.1) hphysical.symm
    _ = (fun z ↦ A.translation + A.rotation * z) ''
        range W.terminalBase.1 := range_move _ _ _ _
    _ = (fun z ↦ A.translation + A.rotation * z) ''
        range W.rear.1 := by rw [hmark]
    _ = range (move A.translation A.rotation A.phase W.rear).1 :=
      (range_move _ _ _ _).symm

theorem initial_range_baseCurrent
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    range (initial J.scalar n).1 =
      range (baseCurrent J (K0 := K0) (K1 := K1) (K2 := K2) n).1 :=
  (initial_range J.scalar n).trans
    (unshiftedRear_range_baseCurrent J (K0 := K0) (K1 := K1)
      (K2 := K2) n)

/-- The transition-free geometric base assembled from the configured physical
source, its actual path, and the sound shifted physical initial rear. -/
noncomputable def base
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} :
    GeometricCorrelatedColumn (Q J.scalar)
      (baseCurrent J (K0 := K0) (K1 := K1) (K2 := K2))
      (compositionError J) 0
      (edgeSourceP0 (D J.scalar)) (edgeP1 (D J.scalar) MA)
      (fun _ ↦ pathKhat J.scalar) (edgeG1 (D J.scalar) MA NA)
      (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar) MA NA)
      (rowC J.scalar)
      (ConfiguredCanonicalPairSource.commonC (D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar))
      khRow (Qmax J.scalar) where
  pathStart n := Q J.scalar (n + 1)
  pathEnd n := baseCurrent J (K0 := K0) (K1 := K1) (K2 := K2) (n + 1)
  path n := ((compositionBaseCorrelated J (K0 := K0) (K1 := K1)
    (K2 := K2)).column.step.richStage (n + 1)).stage.increment
  source n := (compositionBaseCorrelated J (K0 := K0) (K1 := K1)
    (K2 := K2)).source n
  initial n := initial J.scalar n
  initial_eq n u := by
    simpa [compositionBaseCorrelated_source, baseCorrelated_source,
      ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource] using
      (ConfiguredRecursiveEdgePhysicalInitialData.initial_eq
        J.scalar (rowC J.scalar) (MA0 := MA) (NA0 := NA)
          (K0 := K0) (K1 := K1) (K2 := K2) n u)
  initial_range n := initial_range_baseCurrent J
    (K0 := K0) (K1 := K1) (K2 := K2) n
  pathEndRange n := (initial_range_baseCurrent J
    (K0 := K0) (K1 := K1) (K2 := K2) (n + 1)).symm

/-- The geometric base retains the complete shifted physical initial datum. -/
@[simp] theorem base_initial
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    (base J (K0 := K0) (K1 := K1) (K2 := K2)).initial n =
      ConfiguredRecursiveEdgePhysicalInitialData.initial J.scalar n := rfl

/-- All analytic, terminal-range, cost, and composition budgets on the
transition-free physical base. -/
noncomputable def invariant
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} :
    GeometricCompositionInvariant
      (base J (K0 := K0) (K1 := K1) (K2 := K2)) := by
  let X := fun n => ConfiguredRecursiveEdgePhysicalFlowCeilings.compositionRecursiveAnalyticSuccessor
    J (rowC J.scalar) (MA0 := MA) (NA0 := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) n
  refine
    { slice := fun n => by
        simpa [base] using
          (ConfiguredRecursiveEdgePhysicalCompositionBase.baseSlice J
            (K0 := K0) (K1 := K1) (K2 := K2) n)
      periodUpper_le := fun n => by
        have H := ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily.edgePeriodUpperAt_le_edgeP1
          (MA := MA) J.scalar n (initialRearPhase J.scalar n)
        simpa [base, ConfiguredRecursiveEdgePhysicalCompositionBase.baseSlice] using H
      rearCurvature_le := fun n t s => by
        simpa [base, khRow, compositionBaseCorrelated_source, baseCorrelated_source,
          ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource] using
          (ConfiguredRecursiveEdgePhysicalBaseCurvature.base_source_curvature_le_sourceKh
            J.scalar (rowC J.scalar) (MA0 := MA) (NA0 := NA)
              (K0 := K0) (K1 := K1) (K2 := K2) n t s)
      frontPeriodScaleOne := fun n t => by
        change 1 ≤ Real.sqrt (1 - sourceKh ^ 2) *
          (ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily.edgeSourceAt
            J.scalar n (initialRearPhase J.scalar n)).P t
        rw [ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily.edgeSourceAt_period_eq]
        simpa [ConfiguredBaseProfiledEdgeExactAnalyticSuccessorFamily.edgeSource_period_eq]
          using (ConfiguredRecursiveEdgeExactAutomaticRowFacts.edge_front_period_scale_one
            J.scalar n t)
      spatial := fun n => by
        simpa [base, X, khRow, Qmax,
          compositionBaseCorrelated_source, baseCorrelated_source,
          compositionBaseCorrelated_path, baseCorrelated_path] using (X n).spatial
      sidecars := fun n => by
        simpa [base, X, khRow, Qmax,
          compositionBaseCorrelated_source, baseCorrelated_source,
          compositionBaseCorrelated_path, baseCorrelated_path] using (X n).sidecars
      terminalCurvature_nonnegative := fun n s => by
        simpa [base, X, khRow, Qmax,
          compositionBaseCorrelated_source, baseCorrelated_source,
          compositionBaseCorrelated_path, baseCorrelated_path] using
          (X n).terminalCurvature_nonnegative s
      terminalRange := fun n => by
        simpa [base, X, khRow, Qmax,
          compositionBaseCorrelated_source, baseCorrelated_source,
          compositionBaseCorrelated_path, baseCorrelated_path] using
          (X n).terminalRange
      terminalFront_phase := fun n =>
        ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.terminalFrontPhase
          J.scalar n
      terminalFront_eq_phase := fun n => by
        simpa [base, compositionBaseCorrelated_source, baseCorrelated_source,
          ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource] using
          (ConfiguredRecursiveEdgePhysicalTerminalPhaseLink.source_unitTangentData_eq_shift_initial
            J.scalar (rowC J.scalar) (MA0 := MA) (NA0 := NA)
              (K0 := K0) (K1 := K1) (K2 := K2) n)
      nextFront_zero := fun n => by
        funext x
        simpa [base, compositionBaseCorrelated_source, baseCorrelated_source,
          ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource,
          FiniteSmoothRearFamilyMarkingAwareSuccessorFront.front] using
          (ConfiguredRecursiveEdgePhysicalInitialData.rearOwn_zero_eq_initial_ev
            J.scalar (rowC J.scalar) (MA0 := MA) (NA0 := NA)
              (K0 := K0) (K1 := K1) (K2 := K2) (n + 1) x)
      nextPeriod_zero := fun n => by
        simpa [base, compositionBaseCorrelated_source, baseCorrelated_source,
          ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource,
          FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period] using
          (ConfiguredRecursiveEdgePhysicalInitialData.rearPeriod_zero_eq_initial_perim
            J.scalar (rowC J.scalar) (MA0 := MA) (NA0 := NA)
              (K0 := K0) (K1 := K1) (K2 := K2) (n + 1))
      initialTube := fun n => by
        let H := VariableMarkedTube.ofTubeMember
          (ConfiguredRecursiveEdgePhysicalInitialData.initial_tube J.scalar n)
        refine { H with speed_ub := ?_ }
        intro u
        calc
          ‖(initial J.scalar n).2.1 u‖ ≤ perim (initial J.scalar n) :=
            H.speed_ub u
          _ = 2 * (data J.scalar).Hs n :=
            ConfiguredRecursiveEdgePhysicalInitialData.initial_perim_eq
              J.scalar n
          _ ≤ rowC J.scalar n := by
            unfold rowC ConfiguredPhysicalDiagonalRowBudget.outputUpper
            exact le_add_of_nonneg_right
              (ConfiguredRecursiveEdgeReachableQmax.outputRadius_nonnegative
                J.scalar n)
      initialOrdinaryTube := fun n => by
        refine ⟨ConfiguredCanonicalPairSource.commonC (data J.scalar),
          ConfiguredCanonicalPairSource.commonDlt (data J.scalar), ?_,
          ConfiguredRecursiveEdgePhysicalInitialData.initial_tube J.scalar n⟩
        exact (data J.scalar).separation_zero_pos
      rearPeriod_zero_eq_initial_perim := fun n => by
        simpa [base, compositionBaseCorrelated_source, baseCorrelated_source,
          ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource] using
          (ConfiguredRecursiveEdgePhysicalInitialData.rearPeriod_zero_eq_initial_perim
            J.scalar (rowC J.scalar) (MA0 := MA) (NA0 := NA)
              (K0 := K0) (K1 := K1) (K2 := K2) n)
      initialRange := fun n => (base J (K0 := K0) (K1 := K1)
        (K2 := K2)).initial_range n
      pathEndRange := fun n => (base J (K0 := K0) (K1 := K1)
        (K2 := K2)).pathEndRange n
      source_cost_le := fun n => by
        simpa [base] using
          (compositionBase_source_cost_le J (K0 := K0) (K1 := K1)
            (K2 := K2) n)
      composition_d1 := fun n t => by
        simpa [base, X, khRow, Qmax,
          compositionBaseCorrelated_source, baseCorrelated_source,
          compositionBaseCorrelated_path, baseCorrelated_path] using
          (X n).composition_d1 t
      composition_d2 := fun n t => by
        simpa [base, X, khRow, Qmax,
          compositionBaseCorrelated_source, baseCorrelated_source,
          compositionBaseCorrelated_path, baseCorrelated_path] using
          (X n).composition_d2 t }

end ConfiguredRecursiveEdgePhysicalGeometricBase
