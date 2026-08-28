import UnitTangentIterates.ConfiguredBaseProfiledGenuineGaugeResidual
import UnitTangentIterates.ConfiguredRecursiveSourceP0ScalarStart
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

namespace ConfiguredBaseProfiledSourceFamily

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseProfiledResidualConstructor
  ConfiguredBaseExactSelectedGaugeFlow
  ConfiguredBaseExactSelectedGaugeTransport
  ConfiguredBaseProfiledGenuineGaugeResidual
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredGaugeFirstPhysicalSequence
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveSourceP0
  ConfiguredRecursiveSourceP0ScalarStart
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSmoothSource

variable {MA NA : ℝ}

/-- The configured data after removal of the finite scalar prefix. -/
abbrev data (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) :
    ConstructedConfiguredSequenceWeighted.Data :=
  shift O.E.data O.large.N

/-- The exact quantitative edge retained at depth `n`. -/
abbrev edgeOutput (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA)
    (n : ℕ) :=
  ConfiguredGaugeFirstPhysicalSequence.output O.pair.input O.model_data n

/-- Widen the actual half-curvature certificate to the recursive ceiling
`sourceKh = 5/6`.  This changes only the recorded ceiling. -/
def sourceCertificate
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) :
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
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) :
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
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ∀ t, ConfiguredBaseInterpolationShiftedFront.period (edgeOutput O n) t ≤
      speedCap (data O) n := by
  intro t
  have hH := (data O).model.separation_pos n
  simp only [ConfiguredBaseInterpolationShiftedFront.period, speedCap]
  linarith

theorem speedCap_nonnegative
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    0 ≤ speedCap (data O) n := by
  unfold speedCap
  have hH := (data O).model.separation_pos n
  exact mul_nonneg (by norm_num) (add_nonneg zero_le_one hH.le)

private theorem configuredNumericalK
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
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
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ∀ t, ConfiguredBaseInterpolationShiftedFront.period
      (edgeOutput O (n + 1)) t ≤ edgeSpeedCap (data O) n := by
  intro t
  have hH := (data O).model.separation_pos (n + 1)
  simp only [ConfiguredBaseInterpolationShiftedFront.period,
    edgeSpeedCap, speedCap]
  linarith

private theorem configuredEdgeNumericalK
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
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
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ExactSelected (n := n + 1) (sourceCertificate O) :=
  Classical.choice (exists_exactSelected (O.smooth.shift O.large.N)
    (sourceCertificate O) (n + 1))

/-- The genuine gauge-flow reanchoring used by the exact configured edge. -/
noncomputable def edgeReanchored
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    GenuineReanchored (edgeOutput O (n + 1)) (sourceCertificate O)
      (edgeSelected O n) :=
  Classical.choice (exists_genuineReanchored
    (edgeOutput O (n + 1)) (edgeSelected O n))

/-- The shifted first-order transport retained by the exact configured edge. -/
noncomputable def edgeTransport
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ShiftedTransport (edgeReanchored O n).preTransport
      (edgeReanchored O n).gauge :=
  ConfiguredBaseExactSelectedGaugeTransport.exact
    (edgeReanchored O n).preTransport (edgeReanchored O n).gauge

/-- The quantitative audit retained by the exact configured edge. -/
noncomputable def edgeBounds
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
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
noncomputable def selected
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ExactSelected (n := n) (sourceCertificate O) :=
  Classical.choice (exists_exactSelected (O.smooth.shift O.large.N)
    (sourceCertificate O) n)

noncomputable def reanchored
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    GenuineReanchored (edgeOutput O n) (sourceCertificate O) (selected O n) :=
  Classical.choice (exists_genuineReanchored (edgeOutput O n) (selected O n))

noncomputable def transport
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ShiftedTransport (reanchored O n).preTransport (reanchored O n).gauge :=
  ConfiguredBaseExactSelectedGaugeTransport.exact
    (reanchored O n).preTransport (reanchored O n).gauge

noncomputable def bounds
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ConfiguredBaseProfiledGenuineGaugeResidual.Bounds
      (edgeOutput O n) (sourceP0 (data O) n) sourceKh
      (analyticKhat (data O)) (speedCap (data O) n)
      (selected O n) (reanchored O n).preTransport
      (reanchored O n).gauge (transport O n) :=
  ConfiguredBaseProfiledGenuineGaugeResidual.auditedBounds
    (edgeOutput O n) (sourceP0 (data O) n)
    (analyticKhat (data O)) (speedCap (data O) n)
    (sourceCertificate O) (selected O n) (reanchored O n).preTransport
    (reanchored O n).gauge (transport O n) (period_le_speedCap O n)
    (rearKappa1_sourceKh_le_analyticKhat (data O))
    (ConfiguredRecursiveSourceP0.numerical_A (data O) n
      (speedCap_nonnegative O n) le_rfl)
    (configuredNumericalK O n)

/-- All exact profiled base sources, uniformly in the configured depth. -/
noncomputable def sourceFamily
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) :
    ∀ n, MarkingAwareSource (edgeOutput O n).increment
      (sourceP0 (data O) n) sourceKh (analyticKhat (data O))
      (speedCap (data O) n) := by
  intro n
  simpa [sourceCertificate_k0] using
    ConfiguredBaseProfiledGenuineGaugeResidual.baseSource
      (edgeOutput O n) (sourceP0 (data O) n)
      (analyticKhat (data O)) (speedCap (data O) n)
      (sourceCertificate O) (selected O n) (reanchored O n).preTransport
      (reanchored O n).gauge (transport O n) (bounds O n)

/-- The exact source family with indices aligned to the retained successor
edges used by the recursive base-source adapter.  Its speed floor is lowered
only as far as needed to retain both the current-stage spatial certificate and
the numerical reserve at the successor period cap. -/
noncomputable def edgeSourceFamily
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) :
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
      (edgeTransport O n) (edgeBounds O n)

end ConfiguredBaseProfiledSourceFamily
