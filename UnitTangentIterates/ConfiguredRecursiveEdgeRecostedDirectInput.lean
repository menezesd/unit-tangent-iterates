import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRowState
import UnitTangentIterates.ConfiguredRecursiveEdgeDirectRecostBounds
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds

/-!
# Configured direct input for the recosted row state

This specializes the structural direct input to the paper's source profiles.
The canonical-density analytic bounds and the doubled source `numerical_K`
inequality are theorem-produced; no `DirectBounds` callback remains.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedDirectInput

open ConfiguredRecursiveEdgeRecostedRowState
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds

theorem edgeSourceP0_le_one
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D n ≤ 1 := by
  have hkh :=
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat_nonnegative D
  have hR : 0 ≤ GaugeRearFamilyFromFront.rearDriftConst
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap D n)
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh :=
    GaugeRearFamilyFromFront.rearDriftConst_nonneg
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap_nonnegative D n)
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
  have hInv : 1 ≤
      1 / ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D n := by
    have H := ConfiguredRecursiveEdgeSourceP0.numerical_A D n
    nlinarith [mul_nonneg hkh hR]
  have hp := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos D n
  have H := (le_div_iff₀ hp).mp hInv
  simpa using H

variable {j : ℕ}
  {E C0 C1 C2 d eps : ℝ}
  (D : ConstructedConfiguredSequenceWeighted.Data)
  {S : Stage
    (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D)
    (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
    (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
    (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap D) j}
  (R : PhysicalRow S E C0 C1 C2 d)
  (selected : ExactSelected S.source)
  (pre : PreTransport selected)
  (gauge : RearOwnFrameGaugeFlowReanchoring.Gauge (xi pre))
  (shifted : ShiftedTransport pre gauge)
  (scalar : Scalar (A := S.source)
    (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
    (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D (j + 1))
    (khatNext := ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
    (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap D (j + 1)))

def rawSlice
    (hperiod : ∀ t, 1 ≤ rearPeriod S.source t) :
    AnalyticSuccessorSliceFacts
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
        R.geometric.output.chosen selected pre gauge shifted
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
        scalar (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos D (j + 1))) := by
  let W := R.geometric.output.chosen
  let hkh0 :=
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
  let hkh1 := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
  let hP0 := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos D (j + 1)
  let B :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawBounds
      W selected pre gauge shifted hkh0 hkh1 scalar hP0
  let K :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource.compatibility
      W selected pre gauge hkh0 hkh1 shifted B
  have K' :
      FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.Compatibility
        W
        (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
          W selected pre gauge shifted hkh0 hkh1 scalar hP0) := by
    simpa [FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource,
      B] using K
  exact
    FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.sliceFacts
      W _ K' hP0
      (fun t ↦ by
        rw [K'.period_eq]
        exact (edgeSourceP0_le_one D (j + 1)).trans (hperiod t))
      (fun t ↦ by
        rw [K'.period_eq]
        exact scalar.period_le t)

/-- The complete direct input.  Its bounds use the configured doubled source
reserve at the successor diagonal `j+1`. -/
def input
    (J : FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.NormalizedJetBounds
      R.geometric.output.chosen eps)
    (heps : eps ≤ 1 / 4)
    (hperiod : ∀ t, 1 ≤ rearPeriod S.source t)
    (hT : R.geometric.output.chosen.Delta.T = 1) :
    Direct.Input R where
  selected := selected
  pre := pre
  gauge := gauge
  shifted := shifted
  kh_nonnegative :=
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
  kh_lt_one :=
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
  scalar := scalar
  P0_pos := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos D (j + 1)
  bounds := ConfiguredRecursiveEdgeDirectRecostBounds.directBounds D (j + 1)
    R.geometric.output.chosen selected pre gauge shifted scalar
    R.chosenRegularity.eta_continuous
    R.chosenRegularity.eta1_continuous R.chosenRegularity.eta2_continuous
    J heps hperiod hT
  rawSlice := rawSlice D R selected pre gauge shifted scalar hperiod

/-- All qualitative successor choices are internal.  The remaining inputs are
the two scalar time-derivative ceilings, the automatic scalar package, and the
chosen normalized-jet estimates. -/
theorem exists_input
    {Md MP : ℝ}
    (scalar : Scalar (A := S.source)
      (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D (j + 1))
      (khatNext := ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap D (j + 1)))
    (hKnTbd : ∀ t u,
      |RearOwnHigherRegularity.partialTime
          (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
            (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature S.source)
            (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source))
          t u| ≤ Md)
    (hPtbd : ∀ t,
      |SteeringVariablePeriodSelectedInverseJointC1.periodTime
          (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source) t| ≤ MP)
    (J : FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.NormalizedJetBounds
      R.geometric.output.chosen eps)
    (heps : eps ≤ 1 / 4)
    (hperiod : ∀ t, 1 ≤ rearPeriod S.source t)
    (hT : R.geometric.output.chosen.Delta.T = 1) :
    Nonempty (Direct.Input R) := by
  let hkh0 :=
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
  let hkh1 := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
  let hP0 := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos D (j + 1)
  have hPl : ∀ t,
      ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D (j + 1) ≤
        FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source t := by
    intro t
    exact (edgeSourceP0_le_one D (j + 1)).trans (hperiod t)
  obtain ⟨selected⟩ :=
    FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1.exists_exactSelected
      hP0 hkh0 hkh1 hPl scalar.period_le
      (fun t s ↦ (le_abs_self _).trans (scalar.curvature_le t s))
      hKnTbd hPtbd
  let pre :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact
      selected hkh0 hkh1
  obtain ⟨gauge⟩ :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence.exists_gauge
      selected pre R.geometric.output.chosen hkh0 hkh1
  let shifted :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
      pre gauge hkh0 hkh1
  exact ⟨input D R selected pre gauge shifted scalar J heps hperiod hT⟩

theorem exists_input_ofSeparated
    {Md MP P1 : ℝ}
    (scalar : Scalar (A := S.source)
      (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D (j + 1))
      (khatNext := ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap D (j + 1)))
    (hKnTbd : ∀ t u,
      |RearOwnHigherRegularity.partialTime
          (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
            (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature S.source)
            (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source))
          t u| ≤ Md)
    (hPtbd : ∀ t,
      |SteeringVariablePeriodSelectedInverseJointC1.periodTime
          (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source) t| ≤ MP)
    (separated :
      FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
        S.source P1)
    (hsourceT : S.Gamma.T = 1)
    (hsmall :
      FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.chosenJetError
        S.source ≤ 1 / 4)
    (hperiod : ∀ t, 1 ≤ rearPeriod S.source t) :
    Nonempty (Direct.Input R) := by
  let J :=
    FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.normalizedJetBounds_of_flow
      R.geometric.output.chosen separated hsourceT
  have hT : R.geometric.output.chosen.Delta.T = 1 :=
    R.geometric.output.chosen.time_eq.trans hsourceT
  exact exists_input D R scalar hKnTbd hPtbd J hsmall hperiod hT

/-- The installed direct source has exactly the truthful recost-source mass.
This is the quantitative field used by the relabeled geometric invariant. -/
theorem sourceMass_le_recostSourceAllowance
    (I : Direct.Input R)
    (hd : d ≤ ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
      D (j + 1)) :
    (∫ t in (0 : ℝ)..R.directPath.T, I.source.m t) ≤
      ConfiguredRecursiveEdgeRecostedAnalyticCarrier.recostSourceAllowance
        D E C0 C1 C2 j := by
  have hc : R.directPath.cost ≤
      ConfiguredRecursiveEdgeRecostedAnalyticCarrier.recostAllowance
        D E C0 C1 C2 j := by
    exact R.directPath_cost_le.trans
      (mul_le_mul_of_nonneg_left hd
        (mul_nonneg (by norm_num)
          (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget_nonnegative
            E C0 C1 C2)))
  have H :=
    ConfiguredRecursiveEdgeRecostedAnalyticCarrier.scaledCost_le_recostSourceAllowance
      D E C0 C1 C2 j R.directPath.cost_nonneg hc
  simpa [Direct.Input.source,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.directSource,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.density,
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.carrier,
    PhysicalRow.directPath, NormalPath.cost, intervalIntegral.integral_div] using H

end ConfiguredRecursiveEdgeRecostedDirectInput
