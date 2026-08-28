import UnitTangentIterates.ConfiguredBaseProfiledGenuineGaugeResidual
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0ScalarStart
import UnitTangentIterates.ConfiguredRecursiveSourceP0
import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0

/-!
# The all-depth exact configured base-source family

This is the uniform assembly boundary for the exact profiled base sources.
The configured scalar start supplies every geometric and numerical choice.
Until the exact dynamics adapter is packaged, existence of its minimized
`Transport` is the sole input.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredBaseProfiledEdgeSourceFamily

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseProfiledResidualConstructor
  ConfiguredBaseExactSelectedGaugeFlow
  ConfiguredBaseExactSelectedGaugeTransport
  ConfiguredBaseProfiledGenuineGaugeResidual
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveSourceP0
  ConfiguredRecursiveEdgeSourceP0ScalarStart
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSmoothSource

variable {MA NA : ℝ}

/-- The configured data after removal of the finite scalar prefix. -/
abbrev data (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) :
    ConstructedConfiguredSequenceWeighted.Data :=
  shift O.E.data O.large.N

/-- The exact quantitative edge retained at depth `n`. -/
abbrev edgeOutput (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) :=
  ConfiguredGaugeFirstPhysicalSequence.output O.pair.input O.model_data n

/-- Widen the actual half-curvature certificate to the recursive ceiling
`sourceKh = 5/6`.  This changes only the recorded ceiling. -/
def sourceCertificate
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) :
    ConfiguredActualSubunitCurvature.Certificate (data O) where
  k0 := sourceKh
  k0_lt_one := sourceKh_lt_one
  front_nonnegative := O.actualCertificate.front_nonnegative
  front_le := by
    intro n s
    exact (O.actualCertificate.front_le n s).trans (by
      rw [O.actualCertificate_k0]
      exact half_le_sourceKh)
  rear_nonnegative := O.actualCertificate.rear_nonnegative
  rear_le := by
    intro n s
    exact (O.actualCertificate.rear_le n s).trans (by
      rw [O.actualCertificate_k0]
      exact half_le_sourceKh)

@[simp] theorem sourceCertificate_k0
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) :
    (sourceCertificate O).k0 = sourceKh := rfl

private theorem auditedJacobiSourceConst_le_intrinsic :
    RearJacobiSourceCost.jacobiSourceConst sourceKh 1 ≤
      intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh) := by
  unfold intrinsicSourceConst intrinsicDerivativeConst
    RearJacobiSourceCost.jacobiSourceConst
  have hs : 0 < Real.sqrt (1 - sourceKh ^ 2) := by
    rw [sourceKh_eq]
    positivity
  rw [one_div_div]
  refine div_le_div_of_nonneg_right ?_ (pow_nonneg (Real.sqrt_nonneg _) 3)
  norm_num
  have hroot : 0 < Real.sqrt 11 := Real.sqrt_pos.2 (by norm_num)
  have hterm : 0 ≤ 6 / Real.sqrt 11 := div_nonneg (by norm_num) hroot.le
  linarith

theorem period_le_speedCap
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ∀ t, ConfiguredBaseInterpolationShiftedFront.period (edgeOutput O n) t ≤
      speedCap (data O) n := by
  intro t
  have hH := (data O).model.separation_pos n
  simp only [ConfiguredBaseInterpolationShiftedFront.period, speedCap]
  linarith

theorem speedCap_nonnegative
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    0 ≤ speedCap (data O) n := by
  unfold speedCap
  have hH := (data O).model.separation_pos n
  exact mul_nonneg (by norm_num) (add_nonneg zero_le_one hH.le)

theorem configuredNumericalK
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    auditedJacobiSourceConst (sourceCertificate O) + 2 +
        analyticKhat (data O) ^ 2 + 2 *
          GaugeRearFamilyFromFront.rearDriftConst
            (speedCap (data O) n) sourceKh *
            SelInvFrontStripC2.stripCurvConst sourceKh ≤
      1 / sourceP0 (data O) n ^ 2 + analyticKhat (data O) ^ 2 := by
  have hconfigured := ConfiguredRecursiveSourceP0.numerical_K
    (data O) n (speedCap_nonnegative O n) le_rfl
  have hd := auditedJacobiSourceConst_le_intrinsic
  calc
    auditedJacobiSourceConst (sourceCertificate O) + 2 +
          analyticKhat (data O) ^ 2 + 2 *
            GaugeRearFamilyFromFront.rearDriftConst
              (speedCap (data O) n) sourceKh *
              SelInvFrontStripC2.stripCurvConst sourceKh
        ≤ (intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh) + 2) +
          analyticKhat (data O) ^ 2 + 2 *
            GaugeRearFamilyFromFront.rearDriftConst
              (speedCap (data O) n) sourceKh * successorKx sourceKh := by
            simpa [auditedJacobiSourceConst, successorKx,
              SelInvFrontStripC2.stripCurvConst] using
                add_le_add_right hd (2 + analyticKhat (data O) ^ 2 +
                  2 * GaugeRearFamilyFromFront.rearDriftConst
                    (speedCap (data O) n) sourceKh * successorKx sourceKh)
    _ ≤ 1 / sourceP0 (data O) n ^ 2 + analyticKhat (data O) ^ 2 :=
      hconfigured

theorem edgePeriod_le_edgeSpeedCap
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ∀ t, ConfiguredBaseInterpolationShiftedFront.period
      (edgeOutput O (n + 1)) t ≤ edgeSpeedCap (data O) n := by
  intro t
  have hH := (data O).model.separation_pos (n + 1)
  simp only [ConfiguredBaseInterpolationShiftedFront.period,
    edgeSpeedCap, speedCap]
  linarith

private theorem configuredEdgeNumericalK
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    auditedJacobiSourceConst (sourceCertificate O) + 2 +
        analyticKhat (data O) ^ 2 + 2 *
          GaugeRearFamilyFromFront.rearDriftConst
            (edgeSpeedCap (data O) n) sourceKh *
            SelInvFrontStripC2.stripCurvConst sourceKh ≤
      1 / edgeSourceP0 (data O) n ^ 2 + analyticKhat (data O) ^ 2 := by
  have hconfigured := ConfiguredRecursiveEdgeSourceP0.numerical_K (data O) n
  have hd := auditedJacobiSourceConst_le_intrinsic
  calc
    auditedJacobiSourceConst (sourceCertificate O) + 2 +
          analyticKhat (data O) ^ 2 + 2 *
            GaugeRearFamilyFromFront.rearDriftConst
              (edgeSpeedCap (data O) n) sourceKh *
              SelInvFrontStripC2.stripCurvConst sourceKh
        ≤ (intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh) + 2) +
          analyticKhat (data O) ^ 2 + 2 *
            GaugeRearFamilyFromFront.rearDriftConst
              (edgeSpeedCap (data O) n) sourceKh * successorKx sourceKh := by
            simpa [auditedJacobiSourceConst, successorKx,
              SelInvFrontStripC2.stripCurvConst] using
                add_le_add_right hd (2 + analyticKhat (data O) ^ 2 +
                  2 * GaugeRearFamilyFromFront.rearDriftConst
                    (edgeSpeedCap (data O) n) sourceKh * successorKx sourceKh)
    _ ≤ 1 / edgeSourceP0 (data O) n ^ 2 + analyticKhat (data O) ^ 2 :=
      hconfigured

/-- The selected rear data used by the exact configured edge source. -/
noncomputable def edgeSelected
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ExactSelected (n := n + 1) (sourceCertificate O) :=
  Classical.choice (exists_exactSelected (O.smooth.shift O.large.N)
    (sourceCertificate O) (n + 1))

/-- The genuine gauge-flow reanchoring used by the exact configured edge. -/
noncomputable def edgeReanchored
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    GenuineReanchored (edgeOutput O (n + 1)) (sourceCertificate O)
      (edgeSelected O n) :=
  Classical.choice (exists_genuineReanchored
    (edgeOutput O (n + 1)) (edgeSelected O n))

/-- The shifted first-order transport retained by the exact configured edge. -/
noncomputable def edgeTransport
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ShiftedTransport (edgeReanchored O n).preTransport
      (edgeReanchored O n).gauge :=
  ConfiguredBaseExactSelectedGaugeTransport.exact
    (edgeReanchored O n).preTransport (edgeReanchored O n).gauge

/-- The quantitative audit retained by the exact configured edge. -/
noncomputable def edgeBounds
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ConfiguredBaseProfiledGenuineGaugeResidual.Bounds
      (edgeOutput O (n + 1)) (edgeSourceP0 (data O) n) sourceKh
      (analyticKhat (data O)) (edgeSpeedCap (data O) n)
      (edgeSelected O n) (edgeReanchored O n).preTransport
      (edgeReanchored O n).gauge (edgeTransport O n) :=
  ConfiguredBaseProfiledGenuineGaugeResidual.auditedBounds
    (edgeOutput O (n + 1)) (edgeSourceP0 (data O) n)
    (analyticKhat (data O)) (edgeSpeedCap (data O) n)
    (sourceCertificate O) (edgeSelected O n)
    (edgeReanchored O n).preTransport (edgeReanchored O n).gauge
    (edgeTransport O n) (edgePeriod_le_edgeSpeedCap O n)
    (rearKappa1_sourceKh_le_analyticKhat (data O))
    (ConfiguredRecursiveEdgeSourceP0.numerical_A (data O) n)
    (configuredEdgeNumericalK O n)

/-- All exact profiled base sources, uniformly in the configured depth. -/
noncomputable def sourceFamily
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) :
    ∀ n, MarkingAwareSource (edgeOutput O n).increment
      (sourceP0 (data O) n) sourceKh (analyticKhat (data O))
      (speedCap (data O) n) := by
  intro n
  let S : ExactSelected (n := n) (sourceCertificate O) :=
    Classical.choice (exists_exactSelected (O.smooth.shift O.large.N)
      (sourceCertificate O) n)
  let R : GenuineReanchored (edgeOutput O n) (sourceCertificate O) S :=
    Classical.choice (exists_genuineReanchored (edgeOutput O n) S)
  let T : ShiftedTransport R.preTransport R.gauge :=
    ConfiguredBaseExactSelectedGaugeTransport.exact R.preTransport R.gauge
  let B : ConfiguredBaseProfiledGenuineGaugeResidual.Bounds
      (edgeOutput O n) (sourceP0 (data O) n) sourceKh
      (analyticKhat (data O)) (speedCap (data O) n)
      S R.preTransport R.gauge T :=
    ConfiguredBaseProfiledGenuineGaugeResidual.auditedBounds
      (edgeOutput O n) (sourceP0 (data O) n)
      (analyticKhat (data O)) (speedCap (data O) n)
      (sourceCertificate O) S R.preTransport R.gauge T (period_le_speedCap O n)
      (rearKappa1_sourceKh_le_analyticKhat (data O))
      (ConfiguredRecursiveSourceP0.numerical_A (data O) n
        (speedCap_nonnegative O n) le_rfl)
      (configuredNumericalK O n)
  simpa [sourceCertificate_k0] using
    ConfiguredBaseProfiledGenuineGaugeResidual.baseSource
      (edgeOutput O n) (sourceP0 (data O) n)
      (analyticKhat (data O)) (speedCap (data O) n)
      (sourceCertificate O) S R.preTransport R.gauge T B

/-- The successor-edge source uses the noncircular mass-one composition
multiplier.  Only its cost density is enlarged. -/
def edgeScaledBounds
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ConfiguredBaseProfiledGenuineGaugeResidual.Bounds
      (edgeOutput O (n + 1)) (edgeSourceP0 (data O) n) sourceKh
      (analyticKhat (data O)) (edgeSpeedCap (data O) n)
      (edgeSelected O n) (edgeReanchored O n).preTransport
      (edgeReanchored O n).gauge (edgeTransport O n) :=
  (edgeBounds O n).scale
    (ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionCoeff (data O) (n + 1))
    (ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionCoeff_one_le (data O) (n + 1))
    sourceKh_nonnegative sourceKh_lt_one (by
      change 0 ≤ RearJacobiSourceCost.jacobiSourceConst sourceKh 1
      unfold RearJacobiSourceCost.jacobiSourceConst
      positivity)

theorem edgeAuditedJacobiSourceConst_le_intrinsic :
    auditedJacobiSourceConst (sourceCertificate
      (O := O)) ≤ intrinsicSourceConst sourceKh (intrinsicDerivativeConst sourceKh) :=
  auditedJacobiSourceConst_le_intrinsic

@[simp] theorem edgeScaledBounds_m
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) (t : ℝ) :
    (edgeScaledBounds O n).m t =
      ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionCoeff (data O) (n + 1) *
        (edgeBounds O n).m t := rfl

@[simp] theorem edgeScaledBounds_Dd
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) (t : ℝ) :
    (edgeScaledBounds O n).Dd t = (edgeBounds O n).Dd t := rfl

@[simp] theorem edgeScaledBounds_d
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    (edgeScaledBounds O n).d = (edgeBounds O n).d := rfl

/-- The exact source family with indices aligned to the retained successor
edges used by the recursive base-source adapter.  Its speed floor is lowered
only as far as needed to retain both the current-stage spatial certificate and
the numerical reserve at the successor period cap. -/
noncomputable def edgeSourceFamily
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) :
    ∀ n, MarkingAwareSource (edgeOutput O (n + 1)).increment
      (edgeSourceP0 (data O) n) sourceKh (analyticKhat (data O))
      (edgeSpeedCap (data O) n) := by
  intro n
  simpa [sourceCertificate_k0] using
    ConfiguredBaseProfiledGenuineGaugeResidual.baseSource
      (edgeOutput O (n + 1)) (edgeSourceP0 (data O) n)
      (analyticKhat (data O)) (edgeSpeedCap (data O) n)
      (sourceCertificate O) (edgeSelected O n)
      (edgeReanchored O n).preTransport (edgeReanchored O n).gauge
      (edgeTransport O n) (edgeScaledBounds O n)

/-- The scaled edge-source density is charged to the successor-indexed
composition/physical defect. -/
theorem edgeSource_cost_le_compositionPhysicalDefect
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    (∫ t in (0 : ℝ)..(edgeOutput O (n + 1)).increment.T,
      (edgeSourceFamily O n).m t) ≤
        ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionPhysicalDefect
          (data O) (n + 1) := by
  let W := edgeOutput O (n + 1)
  let H := sourceCertificate O
  let C := ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionCoeff
    (data O) (n + 1)
  have hsep : 1 ≤ (data O).Hs 0 := O.large.separation_one
  have hgamma : (1 / 2 : ℝ) ≤ auditedGamma H := by
    dsimp [H, auditedGamma, sourceCertificate]
    rw [sourceKh_eq]
    apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  have hraw := auditedDensity_integral_le_three_of_gamma_half
    W H hsep hgamma
  have hm : (edgeSourceFamily O n).m = fun t ↦ C * auditedDensity W H t := by
    simp [edgeSourceFamily, ConfiguredBaseProfiledGenuineGaugeResidual.baseSource,
      ConfiguredBaseProfiledGenuineGaugeResidual.residual,
      ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
      ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
      edgeScaledBounds, ConfiguredBaseProfiledGenuineGaugeResidual.Bounds.scale,
      edgeBounds, ConfiguredBaseProfiledGenuineGaugeResidual.auditedBounds,
      C, W, H]
  rw [hm]
  change (∫ t in (0 : ℝ)..W.increment.T, C * auditedDensity W H t) ≤ _
  rw [W.increment_time_one, intervalIntegral.integral_const_mul]
  have hC0 : 0 ≤ C := zero_le_one.trans
    (ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionCoeff_one_le
      (data O) (n + 1))
  have hscaled := mul_le_mul_of_nonneg_left hraw hC0
  change C * (∫ t in (0 : ℝ)..1, auditedDensity W H t) ≤
    C * (3 * ConfiguredApproximateDefectPathRowwise.rowDefect (data O) (n + 1)) at hscaled
  unfold ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionPhysicalDefect
    ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionPhysicalCoeff
  have hrow0 := ConfiguredRowDefectProvider.rowDefect_nonneg (data O) (n + 1)
  calc
    C * (∫ t in (0 : ℝ)..1, auditedDensity W H t) ≤
        C * (3 * ConfiguredApproximateDefectPathRowwise.rowDefect (data O) (n + 1)) :=
      hscaled
    _ = (3 * C) * ConfiguredApproximateDefectPathRowwise.rowDefect (data O) (n + 1) := by ring
    _ ≤ (ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalCoeff
          (data O) (n + 1) + 3 * C) *
        ConfiguredApproximateDefectPathRowwise.rowDefect (data O) (n + 1) := by
      exact mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left
          ((ConfiguredPolynomialDiagonalStableRowDefectProvider.physicalCoeffEnvelope
            (data O)).value_nonneg (n + 1))) hrow0

end ConfiguredBaseProfiledEdgeSourceFamily
