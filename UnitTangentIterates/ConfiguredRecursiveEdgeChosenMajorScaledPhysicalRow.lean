import UnitTangentIterates.ConfiguredRecursiveEdgeChosenMajorSplitHistory
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRowState
import UnitTangentIterates.PeriodicSupNormFunctionalIntegrable

/-! # Configured physical rows from uniformly scaled chosen ancestry -/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace ConfiguredRecursiveEdgeChosenMajorScaledPhysicalRow

open ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeChosenMajorSplitHistory
  ConfiguredRecursiveEdgeRecostedAnalyticCarrier
  ConfiguredRecursiveEdgeRecostedRowState
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  ControlledJunctionPathFunctionalBounds
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTerminalScaling
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA Etotal Dtarget K0 K1 K2 : ℝ}
  {RJ : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA}
  (O : ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.Output
    RJ Etotal Dtarget)
  {j n depth : ℕ}
  {S : Stage
    (edgeSourceP0 (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar))
    (fun _ ↦ sourceKh)
    (fun _ ↦ analyticKhat
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar))
    (edgeSpeedCap
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar)) j}
  {G : GeometricInput S}

private def terminalFacts
    (M : MetricGeometry G) : FunctionalIntegrable G.rawPath.eta :=
  PeriodicSupNormFunctionalIntegrable.functionalIntegrable_of_jointC2
    M.c2 M.eta_continuous M.eta1_continuous M.eta2_continuous

private theorem rearPeriod_continuous :
    Continuous (rearPeriod S.source) :=
  Differentiable.continuous fun t ↦
    (S.applied.frame.period_deriv t).differentiableAt

private theorem rearPhysicalW_integrable
    (M : MetricGeometry G) :
    IntervalIntegrable
      (fun t ↦ rearPeriod S.source t *
        ∫ u in (0 : ℝ)..1, |G.rawPath.eta t u|) volume 0 1 := by
  simpa [mul_comm] using
    (terminalFacts M).w.mul_continuousOn
      (rearPeriod_continuous (S := S)).continuousOn

private theorem rearSpatialS1_integrable
    (M : MetricGeometry G) :
    IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 1 (G.rawPath.eta t)) /
        rearPeriod S.source t) volume 0 1 := by
  have hInv : Continuous (fun t ↦ (rearPeriod S.source t)⁻¹) :=
    (rearPeriod_continuous (S := S)).inv₀ fun t ↦
      (S.source.rear_period_pos t).ne'
  simpa [div_eq_mul_inv] using
    (terminalFacts M).s1.mul_continuousOn hInv.continuousOn

private theorem rearSpatialS2_integrable
    (M : MetricGeometry G) :
    IntervalIntegrable
      (fun t ↦ supNorm (iteratedDeriv 2 (G.rawPath.eta t)) /
        rearPeriod S.source t ^ 2) volume 0 1 := by
  have hInv : Continuous (fun t ↦ (rearPeriod S.source t ^ 2)⁻¹) :=
    ((rearPeriod_continuous (S := S)).pow 2).inv₀ fun t ↦
      (sq_pos_of_pos (S.source.rear_period_pos t)).ne'
  simpa [div_eq_mul_inv] using
    (terminalFacts M).s2.mul_continuousOn hInv.continuousOn

/-- The configured split history.  The common scale is the row's retained
rear-period ceiling, and its only cost is the exact square of that ceiling in
the initial physical defect. -/
def splitHistory
    (M : MetricGeometry G)
    (H : Ancestry (K0 := K0) (K1 := K1) (K2 := K2)
      O G.rawPath n depth)
    (hE : Etotal ≤ 1 / 8)
    (hterminal : H.V depth =
      physicalComponents (rearPeriod S.source) G.rawPath.eta)
    (hperiod : ∀ t, 1 ≤ rearPeriod S.source t) :
    ConfiguredRecursiveEdgeActualPhysicalSplitHistory.SplitHistory G.rawPath
      (fun r ↦ scaleAll
        (edgeSpeedCap
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) j ^ 2)
        (H.V r))
      O.major depth Etotal configuredC0 configuredC1 configuredC2
      (edgeSpeedCap
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) j ^ 2 *
        edgePhysicalDefect
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar)
          (n + 1)) := by
  let L := edgeSpeedCap
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) j
  have hL : 1 ≤ L :=
    (hperiod 0).trans (S.source.rear_period_le 0)
  exact Ancestry.toScaledSplitHistory O H hE (rearPeriod S.source) L
    hterminal hL
    (fun t _ ↦ hperiod t)
    (fun t _ ↦ S.source.rear_period_le t)
    (terminalFacts M).w (rearPhysicalW_integrable M)
    (terminalFacts M).s1 (rearSpatialS1_integrable M)
    (terminalFacts M).s2 (rearSpatialS2_integrable M)

/-- Package the scaled chosen ancestry as the physical row consumed by the
recosted recursive state.  Its `metric` projection is definitionally
`PhysicalMetricInput.ofSplitHistory` applied to the same history. -/
def physicalRow
    (M : MetricGeometry G)
    (H : Ancestry (K0 := K0) (K1 := K1) (K2 := K2)
      O G.rawPath n depth)
    (hE : Etotal ≤ 1 / 8)
    (hterminal : H.V depth =
      physicalComponents (rearPeriod S.source) G.rawPath.eta)
    (hperiod : ∀ t, 1 ≤ rearPeriod S.source t) :
    PhysicalRow S Etotal configuredC0 configuredC1 configuredC2
      (edgeSpeedCap
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) j ^ 2 *
        edgePhysicalDefect
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar)
          (n + 1)) where
  geometric := G
  metricGeometry := M
  V := fun r ↦ scaleAll
    (edgeSpeedCap
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) j ^ 2)
    (H.V r)
  major := O.major
  depth := depth
  splitHistory := splitHistory O M H hE hterminal hperiod

/-- The resulting metric package, exposed without any additional geometric
or analytic callback. -/
def physicalMetric
    (M : MetricGeometry G)
    (H : Ancestry (K0 := K0) (K1 := K1) (K2 := K2)
      O G.rawPath n depth)
    (hE : Etotal ≤ 1 / 8)
    (hterminal : H.V depth =
      physicalComponents (rearPeriod S.source) G.rawPath.eta)
    (hperiod : ∀ t, 1 ≤ rearPeriod S.source t) :
    PhysicalMetricInput G Etotal configuredC0 configuredC1 configuredC2
      (edgeSpeedCap
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar) j ^ 2 *
        edgePhysicalDefect
          (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D RJ.scalar)
          (n + 1)) :=
  (physicalRow O M H hE hterminal hperiod).metric

end ConfiguredRecursiveEdgeChosenMajorScaledPhysicalRow
