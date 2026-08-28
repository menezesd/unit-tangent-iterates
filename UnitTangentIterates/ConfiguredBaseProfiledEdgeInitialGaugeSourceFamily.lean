import UnitTangentIterates.ConfiguredBaseProfiledEdgeSourceFamily
import UnitTangentIterates.ConfiguredBaseProfiledInitialGaugeBoundsScale
import UnitTangentIterates.ConfiguredBaseExactSelectedInitialGaugeFlow
import UnitTangentIterates.ConfiguredBaseExactSelectedInitialGaugeTransport
import UnitTangentIterates.ConfiguredBaseProfiledInitialGaugeResidual

/-! # Exact configured edge source through a prescribed rear marking -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseExactSelectedGaugeFlow
  ConfiguredBaseExactSelectedInitialGaugeFlow
  ConfiguredBaseExactSelectedInitialGaugeTransport
  ConfiguredBaseProfiledResidualConstructor
  ConfiguredBaseProfiledGenuineGaugeResidual
  ConfiguredBaseProfiledInitialGaugeResidual
  ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeSourceP0
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA : ℝ}

noncomputable def edgeReanchoredAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) : GenuineReanchoredAt (edgeOutput O (n + 1))
      (sourceCertificate O) (edgeSelected O n) q0 :=
  Classical.choice (exists_genuineReanchoredAt
    (edgeOutput O (n + 1)) (edgeSelected O n) q0)

noncomputable def edgeTransportAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) :
    ShiftedTransport (edgeReanchoredAt O n q0).preTransport
      (edgeReanchoredAt O n q0).gauge :=
  ConfiguredBaseExactSelectedInitialGaugeTransport.exact
    (edgeReanchoredAt O n q0).preTransport
    (edgeReanchoredAt O n q0).gauge

noncomputable def edgeBoundsAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) :
    ConfiguredBaseProfiledInitialGaugeResidual.Bounds
      (edgeOutput O (n + 1)) (edgeSourceP0 (data O) n) sourceKh
      (analyticKhat (data O)) (edgeSpeedCap (data O) n)
      (edgeSelected O n) (edgeReanchoredAt O n q0).preTransport
      (edgeReanchoredAt O n q0).gauge (edgeTransportAt O n q0) :=
  ConfiguredBaseProfiledInitialGaugeResidual.auditedBounds
    (edgeOutput O (n + 1)) (edgeSourceP0 (data O) n)
    (analyticKhat (data O)) (edgeSpeedCap (data O) n)
    (sourceCertificate O) (edgeSelected O n)
    (edgeReanchoredAt O n q0).preTransport
    (edgeReanchoredAt O n q0).gauge (edgeTransportAt O n q0)
    (edgePeriod_le_edgeSpeedCap O n)
    (rearKappa1_sourceKh_le_analyticKhat (data O))
    (edgeBounds O n).numerical_A (edgeBounds O n).numerical_K

/-- Initial-value gauge bounds with the same mass-one composition density as
the canonical edge source. -/
def edgeScaledBoundsAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) :
    ConfiguredBaseProfiledInitialGaugeResidual.Bounds
      (edgeOutput O (n + 1)) (edgeSourceP0 (data O) n) sourceKh
      (analyticKhat (data O)) (edgeSpeedCap (data O) n)
      (edgeSelected O n) (edgeReanchoredAt O n q0).preTransport
      (edgeReanchoredAt O n q0).gauge (edgeTransportAt O n q0) :=
  (edgeBoundsAt O n q0).scale
    (ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionCoeff (data O) (n + 1))
    (ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionCoeff_one_le (data O) (n + 1))
    sourceKh_nonnegative sourceKh_lt_one (by
      change 0 ≤ RearJacobiSourceCost.jacobiSourceConst sourceKh 1
      unfold RearJacobiSourceCost.jacobiSourceConst
      positivity)

@[simp] theorem edgeScaledBoundsAt_m
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 t : ℝ) :
    (edgeScaledBoundsAt O n q0).m t =
      ConfiguredRecursiveEdgeSourceP0Growth.edgeCompositionCoeff (data O) (n + 1) *
        (edgeBoundsAt O n q0).m t := rfl

@[simp] theorem edgeScaledBoundsAt_Dd
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 t : ℝ) :
    (edgeScaledBoundsAt O n q0).Dd t = (edgeBoundsAt O n q0).Dd t := rfl

@[simp] theorem edgeScaledBoundsAt_d
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) :
    (edgeScaledBoundsAt O n q0).d = (edgeBoundsAt O n q0).d := rfl

/-- The exact edge source whose anchored rear coordinate starts at `q0`. -/
noncomputable def edgeSourceAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) :
    MarkingAwareSource (edgeOutput O (n + 1)).increment
      (edgeSourceP0 (data O) n) sourceKh (analyticKhat (data O))
      (edgeSpeedCap (data O) n) := by
  simpa [sourceCertificate_k0] using
    ConfiguredBaseProfiledInitialGaugeResidual.baseSource
      (edgeOutput O (n + 1)) (edgeSourceP0 (data O) n)
      (analyticKhat (data O)) (edgeSpeedCap (data O) n)
      (sourceCertificate O) (edgeSelected O n)
      (edgeReanchoredAt O n q0).preTransport
      (edgeReanchoredAt O n q0).gauge (edgeTransportAt O n q0)
      (edgeScaledBoundsAt O n q0)

theorem edgeGauge_initial
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) : (edgeReanchoredAt O n q0).gauge.q 0 = q0 :=
  (edgeReanchoredAt O n q0).initial

theorem edgeSourceAt_rearOwn
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 t x : ℝ) :
    RearOwnArclength.rearOwn (edgeSourceAt O n q0).F
        (edgeSourceAt O n q0).Theta (edgeSourceAt O n q0).delta
        (edgeSourceAt O n q0).sf t x =
      TimeDependentSpatialReanchoring.shift
        (ExactSelected.rearR (edgeOutput O (n + 1)) (edgeSelected O n))
        (edgeReanchoredAt O n q0).gauge.q t x := by
  simpa [edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseProfiledInitialGaugeResidual.residual] using
    (ConfiguredBaseProfiledSelectedRearGaugeReanchoring.rearOwn_eq_shift
      (edgeOutput O (n + 1)) (edgeSelected O n)
      (edgeReanchoredAt O n q0).gauge.q
      (edgeReanchoredAt O n q0).gauge.contDiff t x)

end ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily
