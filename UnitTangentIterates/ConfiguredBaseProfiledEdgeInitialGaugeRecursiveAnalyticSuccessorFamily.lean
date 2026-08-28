import UnitTangentIterates.ConfiguredBaseProfiledEdgeExactAnalyticSuccessorFamily
import UnitTangentIterates.ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSourceStopping
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor

/-!
# Recursive certificates for an arbitrary initial rear gauge

The physically presented base column must prescribe the initial value of the
rear-gauge ODE.  This file proves the complete exact recursive package directly
for that initial-value source; no equality with the independently normalized
canonical gauge is assumed.
-/

noncomputable section

set_option maxHeartbeats 1600000

open Function Set MarkedSpace PathMetric PathMetric.NormalPath RearTrack

namespace ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseExactSelectedGaugeFlow
  ConfiguredBaseProfiledEdgeExactAnalyticSuccessorFamily
  ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily
  ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredBaseProfiledInitialGaugeResidual
  ConfiguredBaseProfiledSelectedRearGaugeReanchoring
  ConfiguredBaseProfiledSelectedRearReanchoring
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeSourceP0
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSourceStopping
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareRegularitySum
  RearFamilyFrame RearOwnArclength

variable {MA NA : ℝ}

private theorem spatialC2_slice {f : ℝ → ℝ → ℝ}
    (S : RearOwnFrameDrift.SpatialC2 f) (t : ℝ) :
    ContDiff ℝ (2 : ℕ) (f t) := by
  change ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (f t)
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x ↦ (S.deriv1 t x).differentiableAt, by simp, ?_⟩
  have hd1 : deriv (f t) = S.xi1 t := by
    funext x
    exact (S.deriv1 t x).deriv
  rw [hd1]
  change ContDiff ℝ ((0 : WithTop ℕ∞) + 1) (S.xi1 t)
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x ↦ (S.deriv2 t x).differentiableAt, by simp, ?_⟩
  have hd2 : deriv (S.xi1 t) = S.xi2 t := by
    funext x
    exact (S.deriv2 t x).deriv
  rw [hd2]
  exact contDiff_zero.mpr
    (S.continuous2.comp (continuous_const.prodMk continuous_id))

private def edgeEtaFsAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) : ℝ → ℝ → ℝ := fun t s ↦
  ProfiledInterpolationFields.enS
    (sourceK0 (data O) (n + 1)) (sourceK1 (data O) (n + 1))
    (data O).model.thetaBase ((data O).Hs (n + 1)) t
    (s + sigma (edgeOutput O (n + 1)) (edgeSelected O n)
      (edgeReanchoredAt O n q0).gauge.q t +
      rawPhi (edgeOutput O (n + 1)) t 0)

private theorem edgeEtaF_derivAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 t s : ℝ) : HasDerivAt ((edgeSourceAt O n q0).etaF t)
      (edgeEtaFsAt O n q0 t s) s := by
  let W := edgeOutput O (n + 1)
  let S := edgeSelected O n
  let R := edgeReanchoredAt O n q0
  have hs : HasDerivAt (fun x : ℝ ↦ x + sigma W S R.gauge.q t + frontPhase W t) 1 s := by
    simpa using ((hasDerivAt_id s).add_const (sigma W S R.gauge.q t)).add_const
      (frontPhase W t)
  have h := (W.sourceCertificate.en_space t
    (s + sigma W S R.gauge.q t + frontPhase W t)).comp s hs
  simpa [edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual,
    ConfiguredBaseProfiledInitialGaugeResidual.geom,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.etaF,
    ConfiguredBaseProfiledSelectedRearReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearReanchoring.etaF,
    ConfiguredBaseProfiledSelectedRearReanchoring.rawEtaF,
    edgeEtaFsAt, W, S, R, TimeDependentSpatialReanchoring.shift] using h

private theorem edgeEtaFs_continuousAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 t : ℝ) : Continuous (edgeEtaFsAt O n q0 t) := by
  let W := edgeOutput O (n + 1)
  change Continuous (fun s ↦ ProfiledInterpolationFields.enS
    (sourceK0 (data O) (n + 1)) (sourceK1 (data O) (n + 1))
    (data O).model.thetaBase ((data O).Hs (n + 1)) t
    (s + sigma W (edgeSelected O n) (edgeReanchoredAt O n q0).gauge.q t +
      rawPhi W t 0))
  have hd : ∀ s, HasDerivAt
      (ProfiledInterpolationFields.enS
        (sourceK0 (data O) (n + 1)) (sourceK1 (data O) (n + 1))
        (data O).model.thetaBase ((data O).Hs (n + 1)) t)
      (ProfiledInterpolationFields.enSS
        (sourceK0 (data O) (n + 1)) (sourceK1 (data O) (n + 1))
        (sourceK0' (data O) (n + 1)) (sourceK1' (data O) (n + 1))
        (data O).model.thetaBase ((data O).Hs (n + 1)) t s) s :=
    (edgeOutput O (n + 1)).sourceCertificate.en_space2 t
  exact continuous_iff_continuousAt.2 fun s ↦ by
    have hh := hd (s + sigma W (edgeSelected O n)
      (edgeReanchoredAt O n q0).gauge.q t + rawPhi W t 0)
    have hc := ((hasDerivAt_id s).add_const
      (sigma W (edgeSelected O n) (edgeReanchoredAt O n q0).gauge.q t)).add_const
        (rawPhi W t 0)
    simpa only [Function.comp_apply, id_eq] using (hh.comp s hc).continuousAt

private theorem edgeEtaF_periodicAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 t : ℝ) : Function.Periodic ((edgeSourceAt O n q0).etaF t)
      ((edgeSourceAt O n q0).P t) := by
  let A := edgeSourceAt O n q0
  have hcont : Continuous (A.phi t) :=
    continuous_iff_continuousAt.2 fun u ↦ (A.phi_deriv t u).continuousAt
  have hsurj : Surjective (A.phi t) :=
    surjective_of_continuous_quasiPeriodic (A.period_pos t) hcont (A.phi_shift t)
  intro s
  obtain ⟨u, rfl⟩ := hsurj s
  rw [← A.phi_shift t u, ← A.eta_link t (u + 1), ← A.eta_link t u]
  exact (edgeOutput O (n + 1)).increment_c2.eta_periodic t u

private theorem normal_stopped_of_source
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (t : ℝ) (ht : t ∉ Set.Ioo (0 : ℝ) Gamma.T) :
    frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t = fun _ ↦ 0 := by
  have hper : ∀ r, Function.Periodic
      (frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) r)
      (rearArclength (A.delta r) (A.P r)) := fun r ↦
    RearOwnDriftFundamental.periodic_frameNormal_rearOwn
      A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le A.cos_ne_zero
      A.front_frenet A.angle_frenet A.steering A.sf_deriv A.sf_rightInverse
      A.steering_periodic A.front_periodic A.angle_periodic A.front_contDiff
      A.angle_contDiff A.steering_contDiff A.sf_contDiff A.period_contDiff
      A.rear_time_deriv r
  funext x
  have hb := RearOwnTangentialCost.abs_frameNormal_le_slice
    A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
    A.rear_period_pos hper A.jacobi A.etaF_bound t x
  rw [Gamma.m_stop t ht] at hb
  exact abs_eq_zero.mp (le_antisymm (by simpa using hb) (abs_nonneg _))

private theorem rearNormal_c2_of_source
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t : ℝ) :
    ContDiff ℝ (2 : ℕ)
      (frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t) := by
  cases A.frame_regularity with
  | spatial R => exact spatialC2_slice R.normal t
  | joint hY hpsi =>
      exact (RearOwnTangential.contDiff_frameNormal hY hpsi).comp
        (contDiff_const.prodMk contDiff_id)

theorem edgeSourceAt_period_eq
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) :
    (edgeSourceAt O n q0).P =
      ConfiguredBaseInterpolationShiftedFront.period (edgeOutput O (n + 1)) := by
  funext t
  simp [edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual]

private theorem edgePhi1_eq_flowDerivAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 t u : ℝ) :
    (edgeSourceAt O n q0).phi1 t u = FlowDerivative.flowDeriv
      (ProfiledInterpolationFields.hx
        (sourceK0 (data O) (n + 1)) (sourceK1 (data O) (n + 1))
        (data O).model.thetaBase ((data O).Hs (n + 1)))
      (ProfiledInterpolationFields.PhiB (edgeOutput O (n + 1)).sourcePhi)
      (2 * (data O).Hs (n + 1)) t u := by
  let W := edgeOutput O (n + 1)
  have hflow := FlowDerivative.hasDerivAt_flow_initial
    W.sourceBounds.hlip W.sourceCertificate.field_cont
    W.sourceCertificate.field_flow
    (mul_pos (by norm_num) ((data O).model.separation_pos (n + 1)))
    W.sourceCertificate.phi_initial W.sourceCertificate.field_space u t
  have heq := (W.sourcePhi_space (PathMetricCircle.B t) u).unique
    (by simpa [ProfiledInterpolationFields.PhiB] using hflow)
  simpa [edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual,
    ConfiguredBaseProfiledInitialGaugeResidual.geom,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearReanchoring.phi1,
    ConfiguredBaseInterpolationMarkingSource.phi1, W] using heq

/-- Exact slice data for the source whose gauge starts at `q0`. -/
noncomputable def edgeSliceFactsAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) : AnalyticSuccessorSliceFacts (edgeSourceAt O n q0) := by
  let W := edgeOutput O (n + 1)
  let A := edgeSourceAt O n q0
  let markingLower := 2 * (data O).Hs (n + 1) *
    Real.exp (-((W.sourceBounds.K : NNReal) : ℝ))
  let markingUpper := InterpolationPathDist.costFac
    (data O).kstar ((data O).Hs (n + 1))
      (ConfiguredApproximateDefectPathRowwise.edgeEps (data O) (n + 1))
  refine
    { periodUpper := 2 * (data O).Hs (n + 1)
      periodLower_pos := edgeSourceP0_pos (data O) n
      period_lower := ?_
      period_upper := ?_
      etaFs := edgeEtaFsAt O n q0
      etaF_deriv := edgeEtaF_derivAt O n q0
      etaFs_continuous := edgeEtaFs_continuousAt O n q0
      etaF_periodic := edgeEtaF_periodicAt O n q0
      rearNormal_c2 := rearNormal_c2_of_source A
      normal_stopped := normal_stopped_of_source A
      markingLower := markingLower
      markingUpper := markingUpper
      marking_increment := ?_
      markingLower_pos := ?_
      marking_lower := ?_
      markingUpper_nonnegative := ?_
      marking_upper := ?_
      marked_bdd0 := ?_
      marked_bdd1 := ?_ }
  · intro t
    have hkh : 0 ≤ analyticKhat (data O) := analyticKhat_nonnegative (data O)
    have hR : 0 ≤ GaugeRearFamilyFromFront.rearDriftConst
        (edgeSpeedCap (data O) n) sourceKh :=
      GaugeRearFamilyFromFront.rearDriftConst_nonneg
        (edgeSpeedCap_nonnegative (data O) n)
        sourceKh_nonnegative sourceKh_lt_one
    have hInv : 1 ≤ 1 / edgeSourceP0 (data O) n := by
      have hn := (edgeBoundsAt O n q0).numerical_A
      nlinarith [mul_nonneg hkh hR]
    have hPone : edgeSourceP0 (data O) n ≤ 1 := by
      have hp := edgeSourceP0_pos (data O) n
      have := (le_div_iff₀ hp).mp hInv
      simpa using this
    have hH : 1 ≤ (data O).Hs (n + 1) :=
      O.large.separation_one.trans ((data O).separation_lower (n + 1))
    rw [edgeSourceAt_period_eq O n q0]
    simp only [ConfiguredBaseInterpolationShiftedFront.period]
    nlinarith
  · intro t
    rw [edgeSourceAt_period_eq O n q0]
    rfl
  · intro t
    have hs := A.phi_shift t 0
    have hs' : A.phi t 1 = A.phi t 0 + A.P t := by simpa using hs
    linarith
  · dsimp [markingLower]
    exact mul_pos (mul_pos (by norm_num) ((data O).model.separation_pos (n + 1)))
      (Real.exp_pos _)
  · intro t ht u
    rw [edgePhi1_eq_flowDerivAt O n q0 t u]
    have hL : 0 < 2 * (data O).Hs (n + 1) :=
      mul_pos (by norm_num) ((data O).model.separation_pos (n + 1))
    have hbd : ∀ s x, |ProfiledInterpolationFields.hx
        (sourceK0 (data O) (n + 1)) (sourceK1 (data O) (n + 1))
        (data O).model.thetaBase ((data O).Hs (n + 1)) s x| ≤
        ((W.sourceBounds.K : NNReal) : ℝ) :=
      FlowDerivative.abs_hx_le W.sourceBounds.hlip
        W.sourceCertificate.field_space
    have hb := (FlowDerivative.flowDeriv_bounds
      (K := W.sourceBounds.K)
      (Phi := ProfiledInterpolationFields.PhiB W.sourcePhi) hL hbd t u).1
    have hT : W.increment.T = 1 := W.increment_time_one
    have habs : |t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hK0 : 0 ≤ ((W.sourceBounds.K : NNReal) : ℝ) := NNReal.coe_nonneg _
    have he : Real.exp (-((W.sourceBounds.K : NNReal) : ℝ)) ≤
        Real.exp (-(((W.sourceBounds.K : NNReal) : ℝ) * |t|)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    dsimp [markingLower]
    exact (mul_le_mul_of_nonneg_left he hL.le).trans hb
  · dsimp [markingUpper]
    exact (InterpolationVariableSpeedConstants.costFac_pos
      ((data O).model.separation_pos (n + 1))).le
  · intro t _ht u
    rw [edgePhi1_eq_flowDerivAt O n q0 t u]
    exact W.sourceBounds.hP1 t u
  · intro t
    exact ⟨W.increment.m t, by
      rintro _ ⟨u, rfl⟩
      exact W.increment.abs_eta_le t u⟩
  · intro t
    have hd1 : deriv (W.increment.eta t) = W.increment_c2.eta1 t := by
      funext u
      exact (W.increment_c2.eta_deriv t u).deriv
    change BddAbove (Set.range fun u ↦ |iteratedDeriv 1 (W.increment.eta t) u|)
    simpa only [iteratedDeriv_one, hd1] using W.increment_c2.eta1_bdd t

theorem edgePeriodUpperAt_le_edgeP1
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) :
    (edgeSliceFactsAt O n q0).periodUpper ≤
      ConfiguredRecursiveEdgeSourceP0Growth.edgeP1 (data O) MA n := by
  simpa [edgeSliceFactsAt] using
    (ConfiguredBaseProfiledEdgeExactAnalyticSuccessorFamily.edgePeriodUpper_le_edgeP1
      (MA := MA) O n)

/-- The source-native spatial certificate for the arbitrary gauge origin. -/
def edgeSpatialAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) : SpatialFrameRegularity (edgeOutput O (n + 1)).increment
      (edgeSourceAt O n q0).Ydot (edgeSourceAt O n q0).Theta
      (edgeSourceAt O n q0).delta (edgeSourceAt O n q0).sf
      (edgeSourceAt O n q0).P (edgeSourceAt O n q0).m sourceKh
      (edgeSpeedCap (data O) n) := by
  let W := edgeOutput O (n + 1)
  let S := edgeSelected O n
  let P := (edgeReanchoredAt O n q0).preTransport
  let G := (edgeReanchoredAt O n q0).gauge
  let T := edgeTransportAt O n q0
  let R := ConfiguredBaseProfiledInitialGaugeResidual.spatialFrames W S P G T
  let H : SpatialFrameRegularity W.increment
      (ConfiguredBaseExactSelectedInitialGaugeTransport.Ydot P G)
      (ConfiguredBaseProfiledInitialGaugeResidual.geom W S P G).Theta
      (ConfiguredBaseProfiledSelectedRearGaugeReanchoring.delta W S G.q)
      (ConfiguredBaseProfiledSelectedRearGaugeReanchoring.sf W S G.q)
      (ConfiguredBaseInterpolationShiftedFront.period W)
      (edgeScaledBoundsAt O n q0).m sourceKh
      (edgeSpeedCap (data O) n) :=
    { tangential := R.1
      normal := R.2
      tangential1_bound := (edgeScaledBoundsAt O n q0).tangential1_bound
      tangential2_bound := (edgeScaledBoundsAt O n q0).tangential2_bound
      tangential_period_bound := (edgeScaledBoundsAt O n q0).tangential_period_bound }
  simpa [edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual,
    ConfiguredBaseProfiledInitialGaugeResidual.geom, W, S, P, G, T] using H

noncomputable def edgeSelectionBoundsAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) := Classical.choice (by
  apply exists_selectionBounds (edgeSourceAt O n q0) (edgeSpatialAt O n q0)
  · exact (edgeSliceFactsAt O n q0).normal_stopped
  · exact edgeSourceP0_pos (data O) n
  · exact (edgeSliceFactsAt O n q0).period_lower)

noncomputable def edgeRecursiveSidecarsAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) : RecursiveExactSidecars (edgeSourceAt O n q0) :=
  RecursiveExactSidecars.ofSource _ (edgeSelectionBoundsAt O n q0)

theorem edgeTerminalCurvature_nonnegativeAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 s : ℝ) :
    0 ≤ (edgeSourceAt O n q0).K (edgeOutput O (n + 1)).increment.T s := by
  let W := edgeOutput O (n + 1)
  let S := edgeSelected O n
  let P := (edgeReanchoredAt O n q0).preTransport
  let G := (edgeReanchoredAt O n q0).gauge
  have H : 0 ≤ (ConfiguredBaseProfiledInitialGaugeResidual.geom W S P G).K
      W.increment.T s := by
    change 0 ≤ ConfiguredBaseProfiledSelectedRearGaugeReanchoring.K W S G.q
      W.increment.T s
    unfold ConfiguredBaseProfiledSelectedRearGaugeReanchoring.K
      TimeDependentSpatialReanchoring.shift
    change 0 ≤ ConfiguredBaseProfiledSelectedRearReanchoring.K W W.increment.T _
    unfold ConfiguredBaseProfiledSelectedRearReanchoring.K
      ConfiguredBaseProfiledSelectedRearReanchoring.rawK
      ProfiledInterpolationFields.kappa CurvatureInterpolation.kappaInterp
    have hB := ProfiledInterpolationFields.B_mem_Icc W.increment.T
    apply add_nonneg
    · apply mul_nonneg (sub_nonneg.mpr hB.2)
      simpa only [sourceK0, ← (data O).model.curvature_eq (n + 1)] using
        (sourceCertificate O).front_nonnegative (n + 1) _
    · apply mul_nonneg hB.1
      simpa only [sourceK1] using
        (sourceCertificate O).rear_nonnegative (n + 1) _
  simpa [edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual,
    ConfiguredBaseProfiledInitialGaugeResidual.geom, W, S, P, G] using H

theorem range_shiftData (p : Data) (b : ℝ) :
    range (MarkedShift.shiftData b p).1 = range p.1 := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u + b, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u - b, by simp [MarkedShift.shiftData, MarkedShift.shiftMap]⟩

theorem range_of_normalizedMarking
    {base rear : Data} {lambda Lambda : ℝ}
    (M : NormalizedTerminalMarkingComposition.NormalizedC2Marking
      base rear lambda Lambda) : range rear.1 = range base.1 := by
  have hc : Continuous M.marking.psi :=
    continuous_iff_continuousAt.2 fun u ↦ (M.psi_deriv u).continuousAt
  have hs : Surjective M.marking.psi :=
    surjective_of_continuous_quasiPeriodic (by norm_num) hc M.marking.translate
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨M.marking.psi u, (M.marking.position u).symm⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨u, hu⟩ := hs v
    exact ⟨u, by rw [M.marking.position, hu]⟩

theorem edgeTerminalRangeAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) :
    range ((edgeSourceAt O n q0).F (edgeOutput O (n + 1)).increment.T) =
      range (edgeOutput O (n + 1)).rear.1 := by
  let W := edgeOutput O (n + 1)
  let S := edgeSelected O n
  let P := (edgeReanchoredAt O n q0).preTransport
  let G := (edgeReanchoredAt O n q0).gauge
  have hcarrierRaw :
      range ((ConfiguredBaseProfiledInitialGaugeResidual.geom W S P G).F
        W.increment.T) = range (O.pair.input.carrier (n + 1)).data.1 := by
    change range (ConfiguredBaseProfiledSelectedRearGaugeReanchoring.F W S G.q
      W.increment.T) = _
    unfold ConfiguredBaseProfiledSelectedRearGaugeReanchoring.F
    rw [TimeDependentSpatialReanchoring.range_shift]
    change range (ConfiguredBaseProfiledSelectedRearReanchoring.F W W.increment.T) = _
    unfold ConfiguredBaseProfiledSelectedRearReanchoring.F
    rw [TimeDependentSpatialReanchoring.range_shift, W.increment_time_one]
    have hp : perim (O.pair.input.carrier (n + 1)).data ≠ 0 := by
      rw [(O.pair.input.carrier (n + 1)).perim_eq]
      exact mul_ne_zero (by norm_num)
        (ne_of_gt ((data O).model.separation_pos (n + 1)))
    rw [← MarkedSpace.range_ev_of_perim_ne_zero hp]
    rw [(O.pair.input.carrier (n + 1)).curve_eq]
    apply congrArg range
    funext s
    simp [ConfiguredBaseProfiledSelectedRearReanchoring.rawF,
      ProfiledInterpolationFields.Y, sourceK1]
  have hcarrier : range ((edgeSourceAt O n q0).F W.increment.T) =
      range (O.pair.input.carrier (n + 1)).data.1 := by
    simpa [edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
      ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
      ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
      ConfiguredBaseProfiledInitialGaugeResidual.residual,
      ConfiguredBaseProfiledInitialGaugeResidual.geom, W, S, P, G] using hcarrierRaw
  calc
    range ((edgeSourceAt O n q0).F W.increment.T) =
        range (O.pair.input.carrier (n + 1)).data.1 := hcarrier
    _ = range W.terminalBase.1 := by
      rw [W.terminalBase_eq, range_shiftData]
    _ = range W.rear.1 := (range_of_normalizedMarking W.marking).symm

/-- Complete recursive exact package at an arbitrary rear-gauge origin. -/
noncomputable def recursiveAnalyticSuccessorAt
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (q0 : ℝ) :
    RecursiveAnalyticSuccessor (edgeOutput O (n + 1)).increment
      (ConfiguredBaseProfiledEdgeSourceFamily.sourceFamily O n)
      (edgeSourceP0 (data O) n) sourceKh (analyticKhat (data O))
      (edgeSpeedCap (data O) n) :=
  RecursiveAnalyticSuccessor.ofExact (edgeSourceAt O n q0)
    (edgeSliceFactsAt O n q0) (edgeRecursiveSidecarsAt O n q0)
    (edgeSpatialAt O n q0) (edgeTerminalCurvature_nonnegativeAt O n q0)
    (edgeTerminalRangeAt O n q0)

end ConfiguredBaseProfiledEdgeInitialGaugeRecursiveAnalyticSuccessorFamily
