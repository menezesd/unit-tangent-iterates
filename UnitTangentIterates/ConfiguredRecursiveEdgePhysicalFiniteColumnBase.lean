import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalGeometricBase
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn

/-! # Configured depth-zero finite presented column -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePhysicalFiniteColumnBase

open ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgePhysicalGeometricBase
  ConfiguredRecursiveEdgePhysicalInitialData
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
  ConfiguredRecursiveEdgeSourceP0Growth
  FiniteSmoothRearFamilyMarkingAwareCompositionInitialNormalization
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedSlicedInvariant
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareFiniteCorrelatedPresentedColumn
  FiniteSmoothRearFamilyMarkingAwareGeometricExactPresentedRowConstructor
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareSource
  MarkedShift
  RichStageDataPhaseRigidTransport

variable {MA NA : ℝ}

/-- The configured depth-zero column after discarding the obsolete transition
and component certificates. -/
noncomputable def column
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} :
    FiniteColumn (Q J.scalar)
      (Q J.scalar)
      (compositionError J) 0
      (edgeSourceP0 (D J.scalar)) (edgeP1 (D J.scalar) MA)
      (fun _ ↦ pathKhat J.scalar) (edgeG1 (D J.scalar) MA NA)
      (edgeCgWithKhat (D J.scalar) (pathKhat J.scalar) MA NA)
      (rowC J.scalar)
      (ConfiguredCanonicalPairSource.commonC (D J.scalar))
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar))
      khRow (Qmax J.scalar) :=
  let S := compositionBaseCorrelated J
    (K0 := K0) (K1 := K1) (K2 := K2)
  let HS : SlicedCorrelatedColumn S :=
    { slice := fun n ↦ by
        simpa [S] using
          (ConfiguredRecursiveEdgePhysicalCompositionBase.baseSlice J
            (K0 := K0) (K1 := K1) (K2 := K2) n)
      periodUpper_le := by
        intro n
        simpa [S, ConfiguredRecursiveEdgePhysicalCompositionBase.baseSlice,
          D, ConfiguredBaseProfiledEdgeSourceFamily.data] using
          (ConfiguredBaseProfiledEdgeExactAnalyticSuccessorFamily.edgePeriodUpper_le_edgeP1
            J.scalar n) }
  { step := S.column.step
    source := S.source
    slice := HS.slice
    periodUpper_le := HS.periodUpper_le }

/-- The selected source rear at time zero is exactly the configured shifted
physical initial datum as complete marked `Data`. -/
theorem selectedRearData_zero_eq_initial
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    ((column J (K0 := K0) (K1 := K1) (K2 := K2)).source n).selectedRearData 0 =
      initial J.scalar n := by
  let A := (column J (K0 := K0) (K1 := K1) (K2 := K2)).source n
  apply selectedRearData_zero_eq_physicalRear A (initialKinematics J.scalar n)
  · simpa [A, column, FiniteColumn.ofCorrelated,
      compositionBaseCorrelated_source, baseCorrelated_source,
      ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource] using
      (source_front_zero_eq_shift J.scalar (rowC J.scalar)
        (MA0 := MA) (NA0 := NA) (K0 := K0) (K1 := K1) (K2 := K2) n)
  · have H := source_period_zero_eq_frontData J.scalar (rowC J.scalar)
      (MA0 := MA) (NA0 := NA) (K0 := K0) (K1 := K1) (K2 := K2) n
    simpa [A, column, FiniteColumn.ofCorrelated,
      compositionBaseCorrelated_source, baseCorrelated_source,
      ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource,
      SelectedInverseShiftEquivariance.perim_shiftData
        (front_tube J.scalar n)] using H
  · exact initial_tube J.scalar n

/-- A positive chord tube makes the normalized terminal front embedded on one
marked period.  The configured terminal phase link transports that tube from
the next physical initial datum. -/
theorem normalizedFront_injective
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    InjOn (normalizedFront
      ((column J (K0 := K0) (K1 := K1) (K2 := K2)).source n))
      (Ico 0 1) := by
  let H := invariant J (K0 := K0) (K1 := K1) (K2 := K2)
  let b := H.terminalFront_phase n
  let p := shiftData b (initial J.scalar (n + 1))
  have hp : IsTubeMember
      (ConfiguredCanonicalPairSource.commonC (D J.scalar)) 0
      (ConfiguredCanonicalPairSource.commonDlt (D J.scalar)) p :=
    isTubeMember_shiftData (initial_tube J.scalar (n + 1)) b
  have hd : 0 < ConfiguredCanonicalPairSource.commonDlt (D J.scalar) := by
    have hkpos :=
      ConstructedConfiguredInductiveTubeBudget.configured_kstar_pos
        (D J.scalar).model
    rw [ConfiguredCanonicalPairSource.commonDlt,
      ConstructedConfiguredInductiveTubeBudget.chordBase_eq_min
        (D J.scalar).model hkpos]
    exact half_pos (lt_min (D J.scalar).separation_zero_pos
      (div_pos Real.pi_pos (mul_pos (by norm_num) hkpos)))
  have heq : unitTangentData
      ((column J (K0 := K0) (K1 := K1) (K2 := K2)).source n) = p := by
    simpa [H, b, p, column, FiniteColumn.ofCorrelated,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      compositionBaseCorrelated_source, baseCorrelated_source] using
      H.terminalFront_eq_phase n
  intro x hx y hy hxy
  have hcurve : p.1 x = p.1 y := by
    rw [← heq]
    simpa only [unitTangentData_curve] using hxy
  have hxcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
  have hycc : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1, hy.2.le⟩
  have hchord := hp.chord x hxcc y hycc
  rw [hcurve, sub_self, norm_zero] at hchord
  have hcyc0 : cyc x y = 0 := by
    have hcyc := ChordArc.cyc_nonneg hxcc hycc
    nlinarith
  exact cyc_eq_zero_iff hx hy hcyc0.le

/-- All exact row-local analytic readiness fields for the configured
depth-zero finite column.  The marked initial datum is deliberately not
identified with `step.next`: those two representatives have the same range
but generally differ by their marking. -/
noncomputable def readyAt
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    Ready ((column J (K0 := K0) (K1 := K1) (K2 := K2)).state n) := by
  let H := invariant J (K0 := K0) (K1 := K1) (K2 := K2)
  refine
    { initial := initial J.scalar n
      spatial := ?_
      terminalCurvature_nonnegative := ?_
      terminalRange := ?_
      initial_eq := selectedRearData_zero_eq_initial J n
      density_d1 := ?_
      density_d2 := ?_
      front_injective := normalizedFront_injective J n }
  · simpa [column, FiniteColumn.ofCorrelated, FiniteColumn.state,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      compositionBaseCorrelated_source, compositionBaseCorrelated_path,
      baseCorrelated_source, baseCorrelated_path] using H.spatial n
  · simpa [column, FiniteColumn.ofCorrelated, FiniteColumn.state,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      compositionBaseCorrelated_source, compositionBaseCorrelated_path,
      baseCorrelated_source, baseCorrelated_path] using
      H.terminalCurvature_nonnegative n
  · simpa [column, FiniteColumn.ofCorrelated, FiniteColumn.state,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      compositionBaseCorrelated_source, compositionBaseCorrelated_path,
      baseCorrelated_source, baseCorrelated_path] using H.terminalRange n
  · intro t
    simpa [column, FiniteColumn.ofCorrelated, FiniteColumn.state,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      compositionBaseCorrelated_source, compositionBaseCorrelated_path,
      baseCorrelated_source, baseCorrelated_path] using H.composition_d1 n t
  · intro t
    simpa [column, FiniteColumn.ofCorrelated, FiniteColumn.state,
      ConfiguredRecursiveEdgePhysicalGeometricBase.base,
      compositionBaseCorrelated_source, compositionBaseCorrelated_path,
      baseCorrelated_source, baseCorrelated_path] using H.composition_d2 n t

/-- The truthful coherence retained at depth zero: the intrinsic physical
initial rear and the configured next representative have the same range. -/
theorem initial_range_next
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    range (readyAt J (K0 := K0) (K1 := K1) (K2 := K2) n).initial.1 =
      range ((column J (K0 := K0) (K1 := K1) (K2 := K2)).step.next n).1 := by
  simpa [readyAt, column, baseCurrent] using
    (initial_range_baseCurrent J (K0 := K0) (K1 := K1) (K2 := K2) n)

end ConfiguredRecursiveEdgePhysicalFiniteColumnBase
