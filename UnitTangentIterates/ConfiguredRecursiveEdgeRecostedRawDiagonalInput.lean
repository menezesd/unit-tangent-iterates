import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
import UnitTangentIterates.ConfiguredRecursiveEdgeDirectRecostBounds
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedDirectInput

/-! Configured exact input at an explicit diagonal index. -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedRawDiagonalInput

open ConfiguredRecursiveEdgeRecostedCarrierRow
  ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds

variable {j q : ℕ} {E C0 C1 C2 d eps : ℝ}
  (D : ConstructedConfiguredSequenceWeighted.Data)
  {S : FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.Stage
    (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D)
    (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
    (fun _ ↦ ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
    (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap D) j}
  (R : CarrierRow S E C0 C1 C2 d)
  (selected : ExactSelected S.source
    (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh))
  (pre : PreTransport selected)
  (gauge : RearOwnFrameGaugeFlowReanchoring.Gauge (xi pre))
  (shifted : ShiftedTransport pre gauge)
  (scalar : Scalar (A := S.source)
    (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
    (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D q)
    (khatNext := ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
    (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap D q))

def rawSlice
    (hperiod : ∀ t, 1 ≤ rearPeriod S.source t) :
    AnalyticSuccessorSliceFacts
      (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
        R.geometric.output.chosen selected pre gauge shifted
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one scalar
        (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos D q)) := by
  let W := R.geometric.output.chosen
  let hkh0 := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
  let hkh1 := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
  let hP0 := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos D q
  let B := FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawBounds
    W selected pre gauge shifted hkh0 hkh1 scalar hP0
  let K := FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource.compatibility
    W selected pre gauge hkh0 hkh1 shifted B
  have K' :
      FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.Compatibility W
        (FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource
          W selected pre gauge shifted hkh0 hkh1 scalar hP0) := by
    simpa [FiniteSmoothRearFamilyMarkingAwareExactSuccessorDirectRecostSource.rawSource,
      B] using K
  exact FiniteSmoothRearFamilyMarkingAwareChosenExactAnalyticSuccessor.sliceFacts
    W _ K' hP0
    (fun t ↦ by
      rw [K'.period_eq]
      exact (ConfiguredRecursiveEdgeRecostedDirectInput.edgeSourceP0_le_one D q).trans
        (hperiod t))
    (fun t ↦ by rw [K'.period_eq]; exact scalar.period_le t)

set_option maxHeartbeats 800000 in
def input
    (J : FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.NormalizedJetBounds
      R.geometric.output.chosen eps)
    (heps : eps ≤ 1 / 4)
    (hperiod : ∀ t, 1 ≤ rearPeriod S.source t) :
    Input R (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D q)
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap D q) where
  selected := selected
  pre := pre
  gauge := gauge
  shifted := shifted
  kh_nonnegative := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
  kh_lt_one := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
  scalar := scalar
  P0_pos := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos D q
  eps := eps
  jets := J
  eps_le_quarter := heps
  bounds := by
    simpa only using
      (ConfiguredRecursiveEdgeDirectRecostBounds.directBounds
        (eps := eps)
        (W := R.geometric.output.chosen) (S := selected) (R := pre)
        (G := gauge) (T := shifted) (C := scalar)
        (heta0 := R.eta_continuous) (heta1 := R.eta1_continuous)
        (heta2 := R.eta2_continuous) D q (J := J) (heps := heps)
        (hperiod := hperiod) (hT := R.time_one))
  rawSlice := rawSlice D R selected pre gauge shifted scalar hperiod

theorem exists_input_ofSeparated
    {Md MP P1 : ℝ}
    (scalar : Scalar (A := S.source)
      (kap := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
      (P0Next := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D q)
      (khatNext := ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
      (QmaxNext := ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap D q))
    (hKnTbd : ∀ t u,
      |RearOwnHigherRegularity.partialTime
          (SteeringVariablePeriodSelectedInverseJointC1.normalizedCurvature
            (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature S.source)
            (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source)) t u| ≤ Md)
    (hPtbd : ∀ t,
      |SteeringVariablePeriodSelectedInverseJointC1.periodTime
          (FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source) t| ≤ MP)
    (separated :
      FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts S.source P1)
    (hsourceT : S.Gamma.T = 1)
    (hsmall :
      FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.chosenJetError
        S.source ≤ 1 / 4)
    (hperiod : ∀ t, 1 ≤ rearPeriod S.source t) :
    Nonempty (Input R (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D q)
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap D q)) := by
  let hkh0 := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
  let hkh1 := ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
  let hP0 := ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos D q
  have hPl : ∀ t, ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 D q ≤
      FiniteSmoothRearFamilyMarkingAwareSuccessorFront.period S.source t :=
    fun t ↦ (ConfiguredRecursiveEdgeRecostedDirectInput.edgeSourceP0_le_one D q).trans
      (hperiod t)
  obtain ⟨selected⟩ :=
    FiniteSmoothRearFamilyMarkingAwareExactSelectedOfC1.exists_exactSelected
      hP0 hkh0 hkh1 hPl scalar.period_le
      (fun t s ↦ (le_abs_self _).trans (scalar.curvature_le t s)) hKnTbd hPtbd
  let pre := FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport.exact
    selected hkh0 hkh1
  obtain ⟨gauge⟩ :=
    FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence.exists_gauge
      selected pre R.geometric.output.chosen hkh0 hkh1
  let shifted := FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport.exact
    pre gauge hkh0 hkh1
  let J :=
    FiniteSmoothRearFamilyMarkingAwareChosenVariableJetBounds.normalizedJetBounds_of_flow
      R.geometric.output.chosen separated hsourceT
  exact ⟨input D R selected pre gauge shifted scalar J hsmall hperiod⟩

end ConfiguredRecursiveEdgeRecostedRawDiagonalInput
