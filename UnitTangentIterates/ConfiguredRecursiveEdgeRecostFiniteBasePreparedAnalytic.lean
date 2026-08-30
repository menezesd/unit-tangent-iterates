import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteIntrinsicBaseLayer
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNonaffinePreCarrierInput
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierSourceMass
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass
import UnitTangentIterates.ConfiguredBaseProfiledEdgeRecursiveAnalyticSuccessorFamily

/-! # Callback-free analytic input at depth zero

The depth-zero source is the physical composition source.  Its mass is paid
for by the physical base estimate, not by the positive-depth multiplier
allowance.  Only after the exact unscaled successor has been constructed and
completed through the finite history do we install the configured multiplier
density.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostFiniteBasePreparedAnalytic

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgePhysicalBaseFinalTailState
  ConfiguredRecursiveEdgeRecostFiniteIntrinsicBaseLayer
  ConfiguredRecursiveEdgeRecostMultiplierBaseLayer
  ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing
  ConfiguredRecursiveEdgeRecostMultiplierNonaffinePreCarrierInput
  ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
  ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
  ConfiguredRecursiveEdgeRecostedPreCarrier
  ConfiguredRecursiveEdgeRecostedScaledPreCarrier
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  FiniteNonaffineMajorNormalizedState
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} {R : RecostClosingOutput J O}
  (H : Output R) {K0 K1 K2 : ℝ}

abbrev sourceNode (n : ℕ) :=
  nodes (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)

abbrev sourceCore (n : ℕ) :
    Core (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage :=
  baseNodePre H.toClosing (n + 1)

private theorem unaryStage_mass_le_one
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    sourceMass
        (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.unaryStage
          (K0 := K0) (K1 := K1) (K2 := K2) J n).source ≤ 1 := by
  have hm :=
    ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass.sourceMass_le_compositionPhysicalDefect
      J (K0 := K0) (K1 := K1) (K2 := K2) n
  exact hm.trans (J.composition_mass_one (n + 1))

private theorem unaryStage_mass_le_defect
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    sourceMass
        (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.unaryStage
          (K0 := K0) (K1 := K1) (K2 := K2) J n).source ≤
      edgeCompositionPhysicalDefect
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar) (n + 1) :=
  ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass.sourceMass_le_compositionPhysicalDefect
    J (K0 := K0) (K1 := K1) (K2 := K2) n

private theorem baseNode_mass_le_one
    (R : RecostClosingOutput J O) {K0 K1 K2 : ℝ} (n : ℕ) :
    sourceMass (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source ≤ 1 :=
  unaryStage_mass_le_one J
    (K0 := K0) (K1 := K1) (K2 := K2) (rowOutput R n).N

private theorem baseNode_mass_le_defect
    (R : RecostClosingOutput J O) {K0 K1 K2 : ℝ} (n : ℕ) :
    sourceMass (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source ≤
      edgeCompositionPhysicalDefect R.data (n + 1) := by
  have h := unaryStage_mass_le_defect J
    (K0 := K0) (K1 := K1) (K2 := K2) (rowOutput R n).N
  simpa [baseNode, rowGaugeOutput_N, RecostClosingOutput.data,
    ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
    ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
    edgeCompositionPhysicalDefect, edgeCompositionPhysicalCoeff,
    ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect,
    ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalCoeff,
    Nat.add_assoc] using h

/-- The physical base source already has mass at most one. -/
theorem baseSourceMass_le_one (n : ℕ) :
    sourceMass (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source ≤ 1 := by
  exact baseNode_mass_le_one H.toClosing
    (K0 := K0) (K1 := K1) (K2 := K2) (n + 1)

private theorem unaryStage_curvature_le_sourceKh
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
    {K0 K1 K2 : ℝ} (n : ℕ) (t s : ℝ) :
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (ConfiguredRecursiveEdgeRecostedRawDiagonalBase.unaryStage
        (K0 := K0) (K1 := K1) (K2 := K2) J n).source t s| ≤ sourceKh := by
  simpa [ConfiguredRecursiveEdgeRecostedRawDiagonalBase.unaryStage,
    ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
    ConfiguredRecursiveEdgePhysicalGeometricBase.base,
    ConfiguredRecursiveEdgePhysicalCompositionBase.compositionBaseCorrelated_source,
    ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated_source,
    ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource] using
    (ConfiguredRecursiveEdgePhysicalBaseCurvature.base_source_curvature_le_sourceKh
      J.scalar (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
      (MA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0)
      (NA0 := ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n t s)

private theorem baseNode_curvature_le_sourceKh
    (R : RecostClosingOutput J O) {K0 K1 K2 : ℝ} (n : ℕ) (t s : ℝ) :
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (baseNode (K0 := K0) (K1 := K1) (K2 := K2) R n).stage.source t s| ≤ sourceKh :=
  unaryStage_curvature_le_sourceKh J
    (K0 := K0) (K1 := K1) (K2 := K2) (rowOutput R n).N t s

/-- Configured scalar bounds for the physical base source at the successor
diagonal. -/
noncomputable def scalar (n : ℕ) :
    Scalar
      (A := (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source)
      (kap := sourceKh)
      (P0Next := edgeSourceP0 H.data (n + 1))
      (khatNext := analyticKhat H.data)
      (QmaxNext := edgeSpeedCap H.data (n + 1)) where
  curvature_le := fun t s ↦
    baseNode_curvature_le_sourceKh H.toClosing
      (K0 := K0) (K1 := K1) (K2 := K2) (n + 1) t s
  period_le := fun t ↦ by
    let C := baseNode_configured (K0 := K0) (K1 := K1) (K2 := K2)
      H.toClosing (n + 1)
    calc
      FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period
          (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source t =
          FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
            (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source t := rfl
      _ ≤ (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stageQmax
            (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stageIndex :=
        (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source.rear_period_le t
      _ = (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).Qmax :=
        C.stageQmax_at_index_eq
      _ = edgeSpeedCap H.data (n + 1) := by
        rw [C.Qmax_eq]
        simp [ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap,
          ConfiguredCombinedPhysicalDiagonalLargeSeparation.speedCap,
          ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D,
          ConfiguredRecursiveEdgeRecostMultiplierHistoryClosing.Output.data,
          ConfiguredRecursiveEdgeRecostMultiplierClosing.RecostClosingOutput.data,
          ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
          Nat.add_assoc]
  rearKappa1_le := rearKappa1_sourceKh_le_analyticKhat H.data
  numerical_A := ConfiguredRecursiveEdgeSourceP0.numerical_A H.data (n + 1)
  numerical_K := by
    simpa [FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.sourceConst,
      FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.derivativeConst,
      FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds.curvatureConst] using
      (ConfiguredRecursiveEdgeSourceP0.numerical_K H.data (n + 1))

/-- The base chosen-flow jet error is paid by the physical base gauge term of
the unified finite-history epsilon. -/
theorem baseJetLinear_le_epsDiag (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.floorJetLinearConst
        (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source
        1 J.scalar.Mend *
      sourceMass (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source ≤
        H.epsDiag (n + 1) := by
  let A :=
    (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source
  have hperiod :
      FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod A 0 ≤
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.ellCap H.data (n + 2) := by
    simpa [A, ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap,
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.speedCap,
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.ellCap,
      Nat.add_assoc] using
      (scalar (K0 := K0) (K1 := K1) (K2 := K2) H n).period_le 0
  have hcoeff :
      FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.floorJetLinearConst
          A 1 J.scalar.Mend ≤
        ConfiguredRecursiveSourceP0RowJetTail.rowJetCoeff
          H.data J.scalar.Mend (n + 2) := by
    simpa only [FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.floorJetLinearConst] using
      (ConfiguredRecursiveSourceP0RowJetTail.jetLinearConst_le_rowJetCoeff
        H.data J.scalar.Mend (n + 2)
        (A.rear_period_pos 0).le hperiod (by norm_num))
  have hmass :
      sourceMass A ≤ edgeCompositionPhysicalDefect H.data (n + 2) := by
    simpa only [A, H.toClosing_data] using
      (baseNode_mass_le_defect H.toClosing
        (K0 := K0) (K1 := K1) (K2 := K2) (n + 1))
  calc
    FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.floorJetLinearConst
          A 1 J.scalar.Mend * sourceMass A ≤
        ConfiguredRecursiveSourceP0RowJetTail.rowJetCoeff
            H.data J.scalar.Mend (n + 2) *
          edgeCompositionPhysicalDefect H.data (n + 2) :=
      mul_le_mul hcoeff hmass
        (FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear.sourceMass_nonnegative A)
        (ConfiguredRecursiveSourceP0RowJetTail.rowJetCoeff_nonnegative
          H.data J.scalar.Mend (n + 2))
    _ = baseGaugeMajor H.data J.scalar.Mend (n + 1) := rfl
    _ ≤ combinedGaugeMajor H.data J.scalar.Mend
        (configuredSourceMassTarget
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2)
        (n + 1) := by
      exact le_add_of_nonneg_right
        (gaugeMajor_nonnegative H.data J.scalar.Mend _
          (configuredSourceMassTarget_nonnegative
            ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
            ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
            ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
            ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2)
          (n + 1))
    _ ≤ H.epsDiag (n + 1) := H.baseGaugeMajor_le_epsDiag (n + 1)

private noncomputable def finalScalar (n : ℕ) :
    Scalar
      (A := (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source)
      (kap := sourceKh)
      (P0Next := edgeSourceP0 (finalGaugeOutput H.toClosing).data (n + 1))
      (khatNext := analyticKhat (finalGaugeOutput H.toClosing).data)
      (QmaxNext := edgeSpeedCap (finalGaugeOutput H.toClosing).data (n + 1)) := by
  simpa only [finalGaugeOutput_data, H.toClosing_data] using
    (scalar (K0 := K0) (K1 := K1) (K2 := K2) H n)

private theorem exists_unscaled_package (n : ℕ) :
    Nonempty (AllowanceWitness
        (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n)
        (edgeSourceP0 H.data (n + 1)) sourceKh (analyticKhat H.data)
        (edgeSpeedCap H.data (n + 1)) (H.epsDiag (n + 1))) := by
  have h := exists_input_of_mass_recursive_spec
    (O := finalGaugeOutput H.toClosing) (q := n + 1)
    (eps := H.epsDiag (n + 1))
    (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n)
    (baseNodeSelection H.toClosing (n + 1))
    (finalScalar (K0 := K0) (K1 := K1) (K2 := K2) H n)
    (normalized (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)).periodFloor
    (baseSourceMass_le_one H n)
    (baseJetLinear_le_epsDiag H n)
    (H.epsDiag_quarter (n + 1))
  have hdata : (finalGaugeOutput H.toClosing).data = H.data := by
    rw [finalGaugeOutput_data, H.toClosing_data]
  rw [hdata] at h
  exact h

private noncomputable def unscaledPackage (n : ℕ) :=
  Classical.choice
    (exists_unscaled_package (K0 := K0) (K1 := K1) (K2 := K2) H n)

/-- Exact unscaled direct-recost input at the first recursive step. -/
theorem exists_unscaled (n : ℕ) :
    Nonempty (ConfiguredRecursiveEdgeRecostedPreCarrier.Input
      (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n)
      (edgeSourceP0 H.data (n + 1)) sourceKh (analyticKhat H.data)
      (edgeSpeedCap H.data (n + 1))) :=
  ⟨(unscaledPackage (K0 := K0) (K1 := K1) (K2 := K2) H n).input⟩

/-- Canonical choice of the theorem-produced unscaled base input. -/
noncomputable def unscaled (n : ℕ) :=
  (unscaledPackage (K0 := K0) (K1 := K1) (K2 := K2) H n).input

@[simp] theorem unscaled_eps (n : ℕ) :
    (unscaled (K0 := K0) (K1 := K1) (K2 := K2) H n).eps =
      H.epsDiag (n + 1) :=
  (unscaledPackage (K0 := K0) (K1 := K1) (K2 := K2) H n).eps_eq

/-- Its finite-history completion supplies precisely the cost estimate used
by the multiplier scalar. -/
noncomputable def completion (n : ℕ) :=
  (normalized (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)).completion
    (budget H (n + 1))
    (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n)
    (unscaled (K0 := K0) (K1 := K1) (K2 := K2) H n)
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal_le_eighth
    (by
      rw [budget_major_of_le H (n + 1) 1
        (Nat.succ_le_succ (Nat.zero_le n)), unscaled_eps])
    (edgeSpeedCap H.data (n + 1))
    (one_le_edgeSpeedCap H.data (n + 1))
    (two_le_recostPeriodScale H.data (n + 1))
    (fun t _ ↦
      (scalar (K0 := K0) (K1 := K1) (K2 := K2) H n).period_le t)

private theorem defect_succ_eq (n : ℕ) :
    ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.defect H (n + 1) =
      ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect H.data (n + 2) := by
  rw [← H.toClosing_data]
  symm
  change
    ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
        (ConstructedConfiguredInductiveTubeBudget.WeightedData.shift
          (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J))
          H.totalShift) (n + 1 + 1) =
      ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
        (ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly.globalData (J := J))
        (H.totalShift + (n + 1) + 1)
  unfold ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
  unfold ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect
  rw [ConstructedRowDefectLargeSeparation.rowDefect_shift]
  simp [ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalDefect,
    ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalCoeff,
    ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
    Nat.add_assoc]

/-- The finite-history completion provides the exact carrier-cost premise used
by the configured multiplier scalar. -/
theorem baseCarrier_cost_le (n : ℕ) :
    (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.carrier
      (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).geometric.output.chosen
      (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).geometric.output.chosen.c2
      (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).eta_continuous
      (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).eta1_continuous
      (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).eta2_continuous).cost ≤
      4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 *
        (2 * ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.recostPeriodScale
            H.data (n + 1) *
          ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
            H.data (n + 1 + 1)) := by
  change (Completion.carrier
      (completion (K0 := K0) (K1 := K1) (K2 := K2) H n)).path.cost ≤ _
  calc
    _ ≤ 4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2 *
        ((edgeSpeedCap H.data (n + 1)) ^ 2 *
          (2 * ConfiguredRecursiveEdgeRecostFiniteIntrinsicStepAssembly.defect H (n + 1))) :=
      ConfiguredRecursiveEdgeRecostedCarrierRow.CarrierRow.cost_le
        (Completion.carrier
          (completion (K0 := K0) (K1 := K1) (K2 := K2) H n))
    _ = _ := by
      rw [defect_succ_eq H n]
      simp only [ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.recostPeriodScale]
      ring

/-- Callback-free multiplier input for the depth-zero prepared row. -/
noncomputable def scaled (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedScaledPreCarrier.Input
      (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n)
      (edgeSourceP0 H.data (n + 1)) sourceKh (analyticKhat H.data)
      (edgeSpeedCap H.data (n + 1)) :=
  let I := unscaled (K0 := K0) (K1 := K1) (K2 := K2) H n
  ConfiguredRecursiveEdgeRecostMultiplierPreCarrier.input H.toClosing (n + 1)
    I.selected I.pre I.gauge I.shifted I.scalar I.P0_pos I.jets
    I.eps_le_quarter
    (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).eta_continuous
    (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).eta1_continuous
    (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).eta2_continuous
    I.bounds I.rawSlice
    (baseCarrier_cost_le (K0 := K0) (K1 := K1) (K2 := K2) H n)

/-- The analytic family consumed by the first prepared successor step. -/
noncomputable def basePreparedAnalytic (n : ℕ) :=
  scaled (K0 := K0) (K1 := K1) (K2 := K2) H n

/-- The actual multiplier-scaled base successor has exactly the local source
mass allowance reserved by the final closing diagonal. -/
theorem basePreparedAnalytic_sourceMass_le_allowance (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction.sourceMass
        (basePreparedAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).source ≤
      ConfiguredRecursiveEdgeRecostMultiplierScaledDiagonal.multiplierRecostSourceAllowance H.data
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2
          (n + 1) := by
  change sourceMass (scaled (K0 := K0) (K1 := K1) (K2 := K2) H n).source ≤ _
  simpa only [H.toClosing_data] using
    (ConfiguredRecursiveEdgeRecostMultiplierSourceMass.scaledInput_sourceMass_le_allowance
      H.toClosing (n + 1)
        (scaled (K0 := K0) (K1 := K1) (K2 := K2) H n)
        (baseCarrier_cost_le (K0 := K0) (K1 := K1) (K2 := K2) H n)
        (by rfl))

theorem basePreparedAnalytic_eps_le (n : ℕ) :
    (basePreparedAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).eps ≤
      (budget H (n + 1)).major 1 := by
  change (unscaled (K0 := K0) (K1 := K1) (K2 := K2) H n).eps ≤ _
  rw [unscaled_eps, budget_major_of_le H (n + 1) 1
    (Nat.succ_le_succ (Nat.zero_le n))]

/-- The chosen depth-zero slice retains the configured successor speed cap
as its exact period ceiling. -/
theorem basePreparedAnalytic_periodUpper_eq (n : ℕ) :
    (basePreparedAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).slice.periodUpper =
      edgeSpeedCap H.data (n + 1) := by
  change
    (unscaledPackage (K0 := K0) (K1 := K1) (K2 := K2) H n).input.slice.periodUpper = _
  exact
    (unscaledPackage (K0 := K0) (K1 := K1) (K2 := K2) H n).periodUpper_eq

/-- Multiplier scaling preserves the terminal curvature of the raw physical
base successor. -/
theorem basePreparedAnalytic_terminalCurvature_nonnegative (n : ℕ) (s : ℝ) :
    0 ≤ (basePreparedAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).source.K
      (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).path.T s := by
  change 0 ≤ (scaled (K0 := K0) (K1 := K1) (K2 := K2) H n).source.K
    (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).path.T s
  rw [ConfiguredRecursiveEdgeRecostMultiplierPreCarrier.source_K_eq_unscaled]
  simpa [scaled, ConfiguredRecursiveEdgeRecostMultiplierPreCarrier.unscaled] using
    (unscaledPackage (K0 := K0) (K1 := K1) (K2 := K2) H n).terminalCurvature_nonnegative s

/-- Multiplier scaling preserves the terminal range of the raw physical base
successor. -/
theorem basePreparedAnalytic_terminalRange (n : ℕ) :
    range
        ((basePreparedAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).source.F
          (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).path.T) =
      range
        (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).geometric.output.jets.rear.1 := by
  change range
      ((scaled (K0 := K0) (K1 := K1) (K2 := K2) H n).source.F
        (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n).path.T) = _
  rw [ConfiguredRecursiveEdgeRecostMultiplierPreCarrier.source_F_eq_unscaled]
  simpa [scaled, ConfiguredRecursiveEdgeRecostMultiplierPreCarrier.unscaled] using
    (unscaledPackage (K0 := K0) (K1 := K1) (K2 := K2) H n).terminalRange

end ConfiguredRecursiveEdgeRecostFiniteBasePreparedAnalytic
