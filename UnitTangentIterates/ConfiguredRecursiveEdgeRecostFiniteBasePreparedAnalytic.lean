import UnitTangentIterates.ConfiguredRecursiveEdgeRecostFiniteIntrinsicBaseLayer
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierBaseNodePresentedReadiness
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNonaffinePreCarrierInput
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierPreCarrier
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass

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

abbrev sourceCore (n : ℕ) : Core (sourceNode H n).stage :=
  baseNodePre H.toClosing (n + 1)

/-- The physical base source already has mass at most one. -/
theorem baseSourceMass_le_one (n : ℕ) :
    sourceMass (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source ≤ 1 := by
  let q := H.totalShift + (n + 1)
  have hm :=
    ConfiguredRecursiveEdgePhysicalFiniteColumnSourceMass.sourceMass_le_compositionPhysicalDefect
      J (K0 := K0) (K1 := K1) (K2 := K2) q
  exact hm.trans (J.composition_mass_one (q + 1))

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
    (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source.curvature_le t s
  period_le := fun t ↦ by
    simpa [sourceNode, nodes] using
      (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source.rear_period_le t
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
  let A := legacyState (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)
  have heps := A.sourceFacts.eps_le_major
  rw [ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.shiftOutput_major] at heps
  simp only [Nat.add_zero] at heps
  have hbase : A.sourceFacts.eps ≤
      combinedGaugeMajor H.data J.scalar.Mend
        (configuredSourceMassTarget
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C0
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C1
          ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.physicalTransitionCeilings.C2)
        (n + 1) := by
    simpa [A, legacyState,
      ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput_data,
      H.toClosing_data,
      ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output.major] using heps
  have hdiag := hbase.trans (H.baseGaugeMajor_le_epsDiag (n + 1))
  simpa [A, legacyState, sourceNode, nodes,
    FiniteSmoothRearFamilyMarkingAwareChosenNonaffineJetBounds.floorJetLinearConst,
    ConfiguredRecursiveEdgePhysicalBaseNormalizedSourceFacts.stageEps] using hdiag

/-- Exact unscaled direct-recost input at the first recursive step. -/
theorem exists_unscaled (n : ℕ) :
    Nonempty (Input (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n)
      (edgeSourceP0 H.data (n + 1)) sourceKh (analyticKhat H.data)
      (edgeSpeedCap H.data (n + 1))) := by
  apply exists_input_of_mass
    (O := finalGaugeOutput H.toClosing) (q := n + 1)
    (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n)
    (baseNodeSelection H.toClosing (n + 1)) (scalar H n)
  · exact (normalized (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)).periodFloor
  · exact baseSourceMass_le_one H n
  · exact baseJetLinear_le_epsDiag H n
  · exact H.epsDiag_quarter (n + 1)

/-- Canonical choice of the theorem-produced unscaled base input. -/
noncomputable def unscaled (n : ℕ) :=
  Classical.choice (exists_unscaled (K0 := K0) (K1 := K1) (K2 := K2) H n)

/-- Its finite-history completion supplies precisely the cost estimate used
by the multiplier scalar. -/
noncomputable def completion (n : ℕ) :=
  (normalized (K0 := K0) (K1 := K1) (K2 := K2) H (n + 1)).completion
    (budget H (n + 1))
    (sourceCore (K0 := K0) (K1 := K1) (K2 := K2) H n)
    (unscaled (K0 := K0) (K1 := K1) (K2 := K2) H n)
    ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal_le_eighth
    (by
      simpa [unscaled, budget_major_of_le] using
        H.epsDiag_quarter (n + 1))
    (edgeSpeedCap H.data (n + 1))
    (one_le_edgeSpeedCap H.data (n + 1))
    (two_le_recostPeriodScale H.data (n + 1))
    (fun t _ ↦ by
      simpa [sourceNode, nodes] using
        (sourceNode (K0 := K0) (K1 := K1) (K2 := K2) H n).stage.source.rear_period_le t)

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
    (by
      simpa [completion, recostPeriodScale] using
        (ConfiguredRecursiveEdgeRecostedCarrierRow.CarrierRow.cost_le
          (Completion.carrier (completion (K0 := K0) (K1 := K1) (K2 := K2) H n))))

/-- The analytic family consumed by the first prepared successor step. -/
noncomputable def basePreparedAnalytic (n : ℕ) :=
  scaled (K0 := K0) (K1 := K1) (K2 := K2) H n

theorem basePreparedAnalytic_eps_le (n : ℕ) :
    (basePreparedAnalytic (K0 := K0) (K1 := K1) (K2 := K2) H n).eps ≤
      (budget H (n + 1)).major 1 := by
  rw [budget_major_of_le H (n + 1) 1 (Nat.succ_le_succ (Nat.zero_le n))]
  exact baseJetLinear_le_epsDiag H n

end ConfiguredRecursiveEdgeRecostFiniteBasePreparedAnalytic
