import UnitTangentIterates.ConfiguredBaseProfiledEdgeSourceFamily
import UnitTangentIterates.ConfiguredBaseExactSelectedInitialGaugeFlow
import UnitTangentIterates.ConfiguredBaseExactSelectedInitialGaugeTransport
import UnitTangentIterates.ConfiguredBaseProfiledInitialGaugeResidual

/-! # Prescribed-gauge configured sources with the physical row index -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredBaseProfiledInitialGaugeAlignedSourceFamily

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseExactSelectedGaugeFlow
  ConfiguredBaseExactSelectedInitialGaugeFlow
  ConfiguredBaseExactSelectedInitialGaugeTransport
  ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredBaseProfiledInitialGaugeResidual
  ConfiguredBaseProfiledResidualConstructor
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveSourceP0
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA : ℝ}

noncomputable def selected
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ExactSelected (n := n) (sourceCertificate O) :=
  Classical.choice (exists_exactSelected (O.smooth.shift O.large.N)
    (sourceCertificate O) n)

noncomputable def reanchoredAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) : GenuineReanchoredAt (edgeOutput O n)
      (sourceCertificate O) (selected O n) q0 :=
  Classical.choice (exists_genuineReanchoredAt
    (edgeOutput O n) (selected O n) q0)

noncomputable def transportAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) :
    ShiftedTransport (reanchoredAt O n q0).preTransport
      (reanchoredAt O n q0).gauge :=
  ConfiguredBaseExactSelectedInitialGaugeTransport.exact
    (reanchoredAt O n q0).preTransport (reanchoredAt O n q0).gauge

noncomputable def boundsAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) :
    ConfiguredBaseProfiledInitialGaugeResidual.Bounds
      (edgeOutput O n) (sourceP0 (data O) n) sourceKh
      (analyticKhat (data O)) (speedCap (data O) n)
      (selected O n) (reanchoredAt O n q0).preTransport
      (reanchoredAt O n q0).gauge (transportAt O n q0) :=
  ConfiguredBaseProfiledInitialGaugeResidual.auditedBounds
    (edgeOutput O n) (sourceP0 (data O) n)
    (analyticKhat (data O)) (speedCap (data O) n)
    (sourceCertificate O) (selected O n)
    (reanchoredAt O n q0).preTransport (reanchoredAt O n q0).gauge
    (transportAt O n q0) (period_le_speedCap O n)
    (rearKappa1_sourceKh_le_analyticKhat (data O))
    (ConfiguredRecursiveSourceP0.numerical_A (data O) n
      (speedCap_nonnegative O n) le_rfl)
    (configuredNumericalK O n)

/-- The exact source at physical row `n`, with its rear gauge prescribed at
time zero. -/
noncomputable def sourceAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) :
    MarkingAwareSource (edgeOutput O n).increment
      (sourceP0 (data O) n) sourceKh (analyticKhat (data O))
      (speedCap (data O) n) := by
  simpa [sourceCertificate_k0] using
    ConfiguredBaseProfiledInitialGaugeResidual.baseSource
      (edgeOutput O n) (sourceP0 (data O) n)
      (analyticKhat (data O)) (speedCap (data O) n)
      (sourceCertificate O) (selected O n)
      (reanchoredAt O n q0).preTransport (reanchoredAt O n q0).gauge
      (transportAt O n q0) (boundsAt O n q0)

theorem gauge_initial
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) : (reanchoredAt O n q0).gauge.q 0 = q0 :=
  (reanchoredAt O n q0).initial

theorem sourceAt_rearOwn
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 t x : ℝ) :
    RearOwnArclength.rearOwn (sourceAt O n q0).F (sourceAt O n q0).Theta
        (sourceAt O n q0).delta (sourceAt O n q0).sf t x =
      TimeDependentSpatialReanchoring.shift
        (ExactSelected.rearR (edgeOutput O n) (selected O n))
        (reanchoredAt O n q0).gauge.q t x := by
  simpa [sourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseProfiledInitialGaugeResidual.residual] using
    (ConfiguredBaseProfiledSelectedRearGaugeReanchoring.rearOwn_eq_shift
      (edgeOutput O n) (selected O n) (reanchoredAt O n q0).gauge.q
      (reanchoredAt O n q0).gauge.contDiff t x)

end ConfiguredBaseProfiledInitialGaugeAlignedSourceFamily
