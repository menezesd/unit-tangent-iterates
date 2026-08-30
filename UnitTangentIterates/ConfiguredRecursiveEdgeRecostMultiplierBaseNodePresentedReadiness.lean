import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNativeCoreBase
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFlowCeilings
import UnitTangentIterates.ConfiguredRecursiveEdgeGeometricPresentedCanonicalRowProvider
import UnitTangentIterates.ConfiguredRecursiveEdgeGeometricPresentedRowCap
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds

/-! # Presented and selection provenance for canonical base nodes -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness

open ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
  ConfiguredRecursiveEdgeRecostMultiplierBaseNodePre
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeFullRecostMetricDiagonal
  ConfiguredRecursiveEdgeGeometricPresentedRowCap
  ConfiguredRecursiveEdgePhysicalCompositionBase
  ConfiguredRecursiveEdgePhysicalBaseFinalTailState
  ConfiguredRecursiveEdgePhysicalGeometricBase
  ConfiguredRecursiveEdgeRecostMultiplierNativeCore
  ConfiguredRecursiveEdgeSourceP0CappedRowProduction
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)
  {K0 K1 K2 : ℝ}

/-- Full theorem-produced presented boundary on the canonical base node. -/
noncomputable def baseNodePresentedInput (n : ℕ) :
    PresentedInput
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage := by
  let G := baseNodeGeometricInput
    (K0 := K0) (K1 := K1) (K2 := K2) R n
  exact
    { base := G.base
      bound := G.bound
      terminal := G.terminal
      output := G.output
      path_time_one := by
        simpa [baseNode, baseStage] using
          (raw_path_time_one (J := J) (K0 := K0) (K1 := K1) (K2 := K2)
            ((rowOutput R n).N)) }

/-- Retaining the output witness makes the presented geometric input exactly
the canonical physical geometric input, rather than a fresh choice. -/
@[simp] theorem baseNodePresentedInput_geometricInput (n : ℕ) :
    (baseNodePresentedInput (K0 := K0) (K1 := K1) (K2 := K2) R n).geometricInput =
      baseNodeGeometricInput (K0 := K0) (K1 := K1) (K2 := K2) R n := rfl

/-- The canonical physical row whose terminal geometry and selected output are
transported into `baseNodePresentedInput`. -/
noncomputable def baseNodePresentedRowSelection (n : ℕ) :
    GeometricPresentedRowSelection
      (n := (rowOutput R n).N)
      (ConfiguredRecursiveEdgePhysicalGeometricBase.base J
        (K0 := K0) (K1 := K1) (K2 := K2)) :=
  ConfiguredRecursiveEdgeGeometricPresentedCanonicalRowProvider.row J
    (ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
      (K0 := K0) (K1 := K1) (K2 := K2)) ((rowOutput R n).N)

/-- The physical base row has the exact configured marking cap.  In particular,
the physical selected-inverse curvature fields use the analytic terminal caps,
not the smaller model-profile fields `kstar` and `kd`. -/
theorem baseNodePresentedRowCap (n : ℕ) :
    GeometricPresentedRowCap
      (baseNodePresentedRowSelection
        (K0 := K0) (K1 := K1) (K2 := K2) R n)
      J.scalar.Mend
      (successorEndpointConversion (D J.scalar) sourceKh J.scalar.Mend
        ((rowOutput R n).N))
      (compositionDiagonal J ((rowOutput R n).N + 1)) := by
  let q := (rowOutput R n).N
  let D0 := D J.scalar
  let H := ConfiguredRecursiveEdgePhysicalGeometricBase.invariant J
    (K0 := K0) (K1 := K1) (K2 := K2)
  have hterminal :
      (baseNodePresentedRowSelection
        (K0 := K0) (K1 := K1) (K2 := K2) R n).terminalInput =
        terminalInput H q := by
    rfl
  have hcomposition_lt :
      compositionDiagonal J (q + 1) < J.scalar.Mend := by
    have hkhpos : 0 < sourceKh := by
      rw [sourceKh_eq]
      norm_num
    have hargpos : 0 < 1 - sourceKh ^ 2 := by
      nlinarith [sourceKh_nonnegative, sourceKh_lt_one]
    have hrootpos : 0 < Real.sqrt (1 - sourceKh ^ 2) :=
      Real.sqrt_pos.2 hargpos
    have hrootlt : Real.sqrt (1 - sourceKh ^ 2) < 1 := by
      have hsq := Real.sq_sqrt hargpos.le
      have hroot0 := Real.sqrt_nonneg (1 - sourceKh ^ 2)
      have hkhsqpos : 0 < sourceKh ^ 2 := pow_pos hkhpos 2
      nlinarith
    have hscaled := J.composition_scaled_mass_one
      (q + 1) (q + 1) (Nat.le_refl (q + 1))
    change edgeCompositionCoeff D0 (q + 1) /
        Real.sqrt (1 - sourceKh ^ 2) *
          edgeCompositionPhysicalDefect D0 (q + 1) ≤ 1 at hscaled
    have hfactor : 1 < edgeCompositionCoeff D0 (q + 1) /
        Real.sqrt (1 - sourceKh ^ 2) := by
      apply (lt_div_iff₀ hrootpos).2
      nlinarith [edgeCompositionCoeff_one_le D0 (q + 1)]
    have hdefect0 := edgeCompositionPhysicalDefect_nonnegative D0 (q + 1)
    have hdefect1 : edgeCompositionPhysicalDefect D0 (q + 1) < 1 := by
      nlinarith
    change edgeCompositionPhysicalDefect D0 (q + 1) < J.scalar.Mend
    exact hdefect1.trans_le J.one_le_Mend
  have hdiagonal_shift :
      edgeCompositionPhysicalDefect D0 (q + 1) =
        ExponentialDiagonalLargeSeparation.shiftSequence
          (edgeCompositionPhysicalDefect J.scalar.E.data)
          J.scalar.large.N (q + 1) := by
    rw [show D0 = shift J.scalar.E.data J.scalar.large.N from rfl,
      edgeCompositionPhysicalDefect_shift]
    rfl
  have hbounds : ConfiguredCapBounds
      (baseNodePresentedRowSelection
        (K0 := K0) (K1 := K1) (K2 := K2) R n)
      J.scalar.E.data (edgeCompositionPhysicalDefect J.scalar.E.data)
      J.scalar.large.N J.scalar.Mend sourceKh := by
    refine
      { kh_eq := ?_
        error_eq := ?_
        defect_lt_M := ?_
        Lmax_le := ?_
        length_le := ?_
        kb_le := ?_
        kL_le := ?_ }
    · simp [ConfiguredRecursiveEdgeSourceP0CappedRowProduction.khRow]
    · change edgeCompositionPhysicalDefect D0 (q + 1) =
        ExponentialDiagonalLargeSeparation.shiftSequence
          (edgeCompositionPhysicalDefect J.scalar.E.data)
          J.scalar.large.N (q + 1)
      exact hdiagonal_shift
    · rw [← hdiagonal_shift]
      exact hcomposition_lt
    · rw [hterminal]
      change (geometry H q).Lmax ≤ speedCap (shift J.scalar.E.data
        J.scalar.large.N) (q + 1)
      rw [geometry_Lmax]
      simp [ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax,
        ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap, speedCap,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D]
    · rw [hterminal]
      change (geometry H q).physical.L ≤ lengthCap (shift J.scalar.E.data
        J.scalar.large.N) (q + 1)
      rw [(geometry H q).physical_L_eq]
      simpa [FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.terminalPeriod,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.Qmax,
        ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap, speedCap, lengthCap,
        ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D] using
          ((ConfiguredRecursiveEdgePhysicalGeometricBase.base J
            (K0 := K0) (K1 := K1) (K2 := K2)).source q).rear_period_le
              ((ConfiguredRecursiveEdgePhysicalGeometricBase.base J
                (K0 := K0) (K1 := K1) (K2 := K2)).path q).T
    · rw [hterminal]
      change (geometry H q).physical.kb ≤
        analyticKhat (shift J.scalar.E.data J.scalar.large.N)
      rw [(geometry H q).physical_kb_eq]
      simpa [ConfiguredRecursiveEdgeSourceP0CappedRowProduction.khRow,
        D0, ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D] using
          (rearKappa1_sourceKh_le_analyticKhat D0)
    · rw [hterminal]
      change (geometry H q).physical.kL ≤
        analyticKd (shift J.scalar.E.data J.scalar.large.N)
      rw [(geometry H q).physical_kL_eq]
      simpa [ConfiguredRecursiveEdgePhysicalGeometricBase.base,
        compositionBaseCorrelated_source, baseCorrelated_source,
        ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource,
        ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source_kx,
        D0, ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D] using
          (stripCurvConst_sourceKh_le_analyticKd D0)
  simpa [q, ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
    compositionDiagonal, ExponentialDiagonalLargeSeparation.shiftSequence,
    edgeCompositionPhysicalDefect_shift] using
      (ConfiguredCapBounds.rowCap hbounds)

/-- The intrinsic marking term in the presented input is exactly the one
controlled by the retained composition-based row cap. -/
theorem baseNodePresentedEndpointCap_le (n : ℕ) :
    (baseNodePresentedInput
      (K0 := K0) (K1 := K1) (K2 := K2) R n).geometricInput.endpointCap ≤
      edgeEndpointConversion (D J.scalar) sourceKh J.scalar.Mend
          ((rowOutput R n).N) *
        compositionDiagonal J ((rowOutput R n).N + 1) := by
  change
    FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.intrinsicEndpointCap
        (baseNodePresentedRowSelection
          (K0 := K0) (K1 := K1) (K2 := K2) R n).output ≤ _
  calc
    FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.intrinsicEndpointCap
        (baseNodePresentedRowSelection
          (K0 := K0) (K1 := K1) (K2 := K2) R n).output ≤
      successorEndpointConversion (D J.scalar) sourceKh J.scalar.Mend
          ((rowOutput R n).N) *
        compositionDiagonal J ((rowOutput R n).N + 1) :=
      GeometricPresentedRowCap.markingC2Bound_le
        (zero_le_one.trans J.one_le_Mend)
        (baseNodePresentedRowCap
          (K0 := K0) (K1 := K1) (K2 := K2) R n)
    _ ≤ edgeEndpointConversion (D J.scalar) sourceKh J.scalar.Mend
          ((rowOutput R n).N) *
        compositionDiagonal J ((rowOutput R n).N + 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact successorEndpointConversion_le_edgeEndpointConversion
          (D J.scalar) sourceKh J.scalar.Mend ((rowOutput R n).N)
      · simpa [compositionDiagonal] using
          (edgeCompositionPhysicalDefect_nonnegative
            (D J.scalar) ((rowOutput R n).N + 1))

/-- The native base core is definitionally reconstructed from retained
presented provenance. -/
noncomputable def baseNodePre (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedPreCarrier.Core
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage :=
  (baseNodePresentedInput (K0 := K0) (K1 := K1) (K2 := K2) R n).core

/-- Canonical raw metric geometry transported through the provenance-preserving
presented base core. -/
noncomputable def baseNodePreRawMetric (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedRawMetricGeometry.RawMetricGeometry.Bounded
      (baseNodePre (K0 := K0) (K1 := K1) (K2 := K2) R n).geometric := by
  change ConfiguredRecursiveEdgeRecostedRawMetricGeometry.RawMetricGeometry.Bounded
    ((baseNodePresentedInput (K0 := K0) (K1 := K1) (K2 := K2) R n).geometricInput)
  rw [baseNodePresentedInput_geometricInput]
  exact baseNodeRawMetric (K0 := K0) (K1 := K1) (K2 := K2) R n

/-- The transported base raw metric retains the configured variable-speed
factor at the physical public row. -/
@[simp] theorem baseNodePreRawMetric_pathFactor (n : ℕ) :
    (baseNodePreRawMetric
      (K0 := K0) (K1 := K1) (K2 := K2) R n).toRawMetricGeometry.pathFactor =
      edgeConversion (D J.scalar) (analyticKhat (D J.scalar))
        choice.MA0 choice.NA0 ((rowOutput R n).N) := by
  rfl

/-- The transported base raw metric retains the composition defect as its
exact raw chosen-path cost ceiling. -/
@[simp] theorem baseNodePreRawMetric_rawBound (n : ℕ) :
    (baseNodePreRawMetric
      (K0 := K0) (K1 := K1) (K2 := K2) R n).rawBound =
      compositionDiagonal J ((rowOutput R n).N + 1) := by
  rfl

/-- The depth-zero raw base edge is paid by the closing error at `(n,0)`.
The path factor, raw composition defect, and endpoint coefficient are all
normalized from the retained public-row provenance before applying the full
displayed-metric diagonal bound. -/
theorem baseNodePreRawMetric_edgeBudget_le_error (n : ℕ) :
    (baseNodePreRawMetric
      (K0 := K0) (K1 := K1) (K2 := K2) R n).edgeBudget ≤ R.error n 0 := by
  let q := (rowOutput R n).N
  let s := R.preShift + R.large.N + n
  let M := baseNodePreRawMetric
    (K0 := K0) (K1 := K1) (K2 := K2) R n
  have hOdata : O.data = shift (D J.scalar) O.N := by
    rfl
  have hq : q = O.N + s := by
    simp [q, s, RecostClosingOutput.totalShift, Nat.add_assoc]
  have hq1 : q + 1 = O.N + (s + 1) := by
    simpa [Nat.add_assoc] using congrArg (fun x : ℕ => x + 1) hq
  have hdefect :
      compositionDiagonal J (q + 1) =
        edgeCompositionPhysicalDefect O.data (s + 1) := by
    change edgeCompositionPhysicalDefect (D J.scalar) (q + 1) = _
    calc
      edgeCompositionPhysicalDefect (D J.scalar) (q + 1) =
          edgeCompositionPhysicalDefect (D J.scalar) (O.N + (s + 1)) := by
            rw [hq1]
      _ = edgeCompositionPhysicalDefect (shift (D J.scalar) O.N) (s + 1) :=
        (edgeCompositionPhysicalDefect_shift (D J.scalar) O.N (s + 1)).symm
      _ = edgeCompositionPhysicalDefect O.data (s + 1) := by
        rw [hOdata]
  have hpathShift :
      edgeConversion (D J.scalar) (analyticKhat (D J.scalar))
          choice.MA0 choice.NA0 q =
        edgeConversion O.data (analyticKhat O.data)
          choice.MA0 choice.NA0 s := by
    rw [hOdata, hq]
    rfl
  have hendpointShift :
      edgeEndpointConversion (D J.scalar) sourceKh J.scalar.Mend q =
        edgeEndpointConversion O.data sourceKh J.scalar.Mend s := by
    rw [hOdata, hq]
    rfl
  have hfactor :
      M.toRawMetricGeometry.pathFactor ≤
        edgeConversion O.data (analyticKhat O.data)
          choice.MA0 choice.NA0 s := by
    have hpath :
        M.toRawMetricGeometry.pathFactor =
          edgeConversion (D J.scalar) (analyticKhat (D J.scalar))
            choice.MA0 choice.NA0 q := by
      simpa [M, q] using
        (baseNodePreRawMetric_pathFactor
          (K0 := K0) (K1 := K1) (K2 := K2) R n)
    exact (hpath.trans hpathShift).le
  have hraw :
      M.rawBound ≤ edgeCompositionPhysicalDefect O.data (s + 1) := by
    have hraw' : M.rawBound = compositionDiagonal J (q + 1) := by
      simpa [M, q] using
        (baseNodePreRawMetric_rawBound
          (K0 := K0) (K1 := K1) (K2 := K2) R n)
    exact (hraw'.trans hdefect).le
  have hendpointLocal :
      (baseNodePresentedInput
          (K0 := K0) (K1 := K1) (K2 := K2) R n).geometricInput.endpointCap ≤
        edgeEndpointConversion (D J.scalar) sourceKh J.scalar.Mend q *
          compositionDiagonal J (q + 1) := by
    simpa [q] using
      (baseNodePresentedEndpointCap_le
        (K0 := K0) (K1 := K1) (K2 := K2) R n)
  have hendpoint :
      (baseNodePresentedInput
          (K0 := K0) (K1 := K1) (K2 := K2) R n).geometricInput.endpointCap ≤
        edgeEndpointConversion O.data sourceKh J.scalar.Mend s *
          edgeCompositionPhysicalDefect O.data (s + 1) := by
    calc
      (baseNodePresentedInput
          (K0 := K0) (K1 := K1) (K2 := K2) R n).geometricInput.endpointCap ≤
          edgeEndpointConversion (D J.scalar) sourceKh J.scalar.Mend q *
            compositionDiagonal J (q + 1) := hendpointLocal
      _ = edgeEndpointConversion O.data sourceKh J.scalar.Mend s *
          edgeCompositionPhysicalDefect O.data (s + 1) := by
        rw [hendpointShift, hdefect]
  have hbudget :
      M.edgeBudget ≤
        fullRecostMetricDiagonal O.data choice.MA0 choice.NA0
          distortionTotal physicalTransitionCeilings.C0
          physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
          J.scalar.Mend s := by
    simpa only [
      ConfiguredRecursiveEdgeRecostedRawMetricGeometry.RawMetricGeometry.Bounded.edgeBudget] using
      (baseRawEdgeBudget_le_fullRecostMetricDiagonal
        O.data choice.MA0 choice.NA0 distortionTotal
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2 J.scalar.Mend
        M.toRawMetricGeometry.pathFactor M.rawBound
        (baseNodePresentedInput
          (K0 := K0) (K1 := K1) (K2 := K2) R n).geometricInput.endpointCap
        s hfactor hraw M.rawBound_nonnegative hendpoint)
  change M.edgeBudget ≤ R.error n 0
  rw [R.error_eq_multiplierDiagonal]
  simpa [s, Nat.add_assoc] using hbudget

/-- Fresh exact successor-selection derivative bounds tied to the physical
base source itself. -/
noncomputable def baseNodeSelection (n : ℕ) :
    SelectionBounds
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source := by
  let q := (rowOutput R n).N
  let X := ConfiguredRecursiveEdgePhysicalFlowCeilings.compositionRecursiveAnalyticSuccessor
    J (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
      (MA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
      (NA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) q
  have hsource :
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source =
        ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source
          J.scalar (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
          (MA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
          (NA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
          (K0 := K0) (K1 := K1) (K2 := K2) q := by
    change
      (ConfiguredRecursiveEdgePhysicalCompositionBase.compositionBaseCorrelated
        J (K0 := K0) (K1 := K1) (K2 := K2)).source q = _
    rfl
  rw [hsource]
  simpa [X] using X.sidecars.selection

end ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness
