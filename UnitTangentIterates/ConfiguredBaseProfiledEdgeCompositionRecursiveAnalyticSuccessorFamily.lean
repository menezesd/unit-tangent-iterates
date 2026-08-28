import UnitTangentIterates.ConfiguredBaseProfiledEdgeRecursiveAnalyticSuccessorFamily
import UnitTangentIterates.ConfiguredBaseProfiledInitialGaugeBoundsScale
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0RowJetTail
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionDensityBudgets
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor

/-! # Composition-stable edge-output-native recursive sources -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredBaseProfiledEdgeCompositionRecursiveAnalyticSuccessorFamily

open ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredBaseProfiledEdgeRecursiveAnalyticSuccessorFamily
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareCompositionDensityBudgets
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA : ℝ}

/-- The composition multiplier installed in the edge source discharges both
composed-normal density inequalities directly on the unnormalized canonical
edge source. -/
theorem edgeSource_composition_budgets
    (J : RowJetScalarOutput MA NA) (n : ℕ) :
    let A := edgeSourceFamily J.scalar n
    let Gamma := (edgeOutput J.scalar (n + 1)).increment
    let M := ∫ s in (0 : ℝ)..Gamma.T, A.m s
    (∀ t, 2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2)) *
        GaugeFlowDerivCost.costP1 (rearPeriod A 0)
          (GaugeMarkedDataOfRearFamily.rearKappa1 sourceKh) M ≤ A.m t) ∧
      (∀ t,
        (A.Dd t + 2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2))) *
            GaugeFlowDerivCost.costP1 (rearPeriod A 0)
              (GaugeMarkedDataOfRearFamily.rearKappa1 sourceKh) M ^ 2 +
          2 * (Gamma.m t / Real.sqrt (1 - sourceKh ^ 2)) *
            GaugeFlowDerivCost.costG1 (rearPeriod A 0)
              (GaugeMarkedDataOfRearFamily.rearKappa1 sourceKh)
              (GaugeMarkedDataOfRearFamily.rearKappa2 sourceKh) M ≤ A.m t) := by
  dsimp only
  let A := edgeSourceFamily J.scalar n
  let Gamma := (edgeOutput J.scalar (n + 1)).increment
  let raw := fun t ↦ (edgeBounds J.scalar n).m t
  let coeff := edgeCompositionCoeff (data J.scalar) (n + 1)
  let d := FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicSourceConst
    sourceKh
    (FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst sourceKh)
  have hspeed : edgeSpeedCap (data J.scalar) n ≤
      edgeSpeedCap (data J.scalar) (n + 1) := by
    unfold edgeSpeedCap speedCap
    have hs := (data J.scalar).separation_step (n + 1)
    have hd := (data J.scalar).deltaStep_pos
    nlinarith
  have hmass : (∫ s in (0 : ℝ)..Gamma.T, A.m s) ≤ 1 := by
    have h := (edgeSource_cost_le_compositionPhysicalDefect J.scalar n).trans
      (J.composition_mass_one (n + 1))
    simpa [A, Gamma, edgeSourceFamily] using h
  apply of_scaled_density (A := A) (C := coeff) (d := d)
    (Q := edgeSpeedCap (data J.scalar) (n + 1)) raw
  · exact (edgeBounds J.scalar n).density_nonnegative
  · exact (edgeBounds J.scalar n).density_domination
  · intro t
    dsimp [A, raw, coeff]
    simp [edgeSourceFamily,
      ConfiguredBaseProfiledGenuineGaugeResidual.baseSource,
      ConfiguredBaseProfiledGenuineGaugeResidual.residual,
      ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
      ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
      edgeScaledBounds, ConfiguredBaseProfiledGenuineGaugeResidual.Bounds.scale]
  · intro t
    have hraw := (edgeBounds J.scalar n).Dd_le t
    have hdconst : (edgeBounds J.scalar n).d ≤ d := by
      change ConfiguredBaseProfiledResidualConstructor.auditedJacobiSourceConst
        (sourceCertificate J.scalar) ≤ d
      exact edgeAuditedJacobiSourceConst_le_intrinsic (O := J.scalar)
    simpa [A, raw, d, edgeSourceFamily,
      ConfiguredBaseProfiledGenuineGaugeResidual.baseSource,
      ConfiguredBaseProfiledGenuineGaugeResidual.residual,
      ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
      ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
      edgeScaledBounds, ConfiguredBaseProfiledGenuineGaugeResidual.Bounds.scale] using
        hraw.trans (mul_le_mul_of_nonneg_right hdconst
          ((edgeBounds J.scalar n).density_nonnegative t))
  · exact ConfiguredRecursiveSourceP0Growth.intrinsicSourceConst_nonnegative
  · exact (A.rear_period_pos 0).le
  · exact (A.rear_period_le 0).trans hspeed
  · exact sourceKh_nonnegative
  · exact sourceKh_lt_one
  · exact analyticKhat_nonnegative (data J.scalar)
  · exact rearKappa1_sourceKh_le_analyticKhat (data J.scalar)
  · exact hmass
  · simpa [edgeFlowP1AtOne] using
      edgeCompositionCoeff_first (data J.scalar) (n + 1)
  · simpa [d, edgeFlowP1AtOne, edgeFlowG1AtOne] using
      edgeCompositionCoeff_second (data J.scalar) (n + 1)

/-- The actual edge source with recursive slice/spatial sidecars and both
composition budgets retained together. -/
noncomputable def compositionRecursiveAnalyticSuccessor
    (J : RowJetScalarOutput MA NA) (n : ℕ) :
    CompositionRecursiveAnalyticSuccessor
      (edgeOutput J.scalar (n + 1)).increment (sourceFamily J.scalar n)
      (edgeSourceP0 (data J.scalar) n) sourceKh
      (analyticKhat (data J.scalar)) (edgeSpeedCap (data J.scalar) n) := by
  let X := recursiveAnalyticSuccessor J.scalar n
  have H := edgeSource_composition_budgets J n
  refine { toRecursiveAnalyticSuccessor := X
           composition_d1 := ?_
           composition_d2 := ?_ }
  · simpa [X] using H.1
  · simpa [X] using H.2

end ConfiguredBaseProfiledEdgeCompositionRecursiveAnalyticSuccessorFamily
