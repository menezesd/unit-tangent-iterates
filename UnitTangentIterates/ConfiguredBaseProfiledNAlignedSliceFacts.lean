import UnitTangentIterates.ConfiguredBaseProfiledSourceFamily
import UnitTangentIterates.ConfiguredRecursiveSourceP0AlignedBaseSourceFamily
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSliceFactsPhaseRigid

/-! # Exact analytic slice facts for n-aligned configured sources -/
/-! # Exact analytic sidecars for the configured base sources -/

noncomputable section

set_option maxHeartbeats 1200000

open Function Set MarkedSpace PathMetric PathMetric.NormalPath RearTrack

namespace ConfiguredBaseProfiledNAlignedSliceFacts

open ConfiguredBaseProfiledSourceFamily
  ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseExactSelectedGaugeFlow
  ConfiguredBaseProfiledGenuineGaugeResidual
  ConfiguredBaseProfiledSelectedRearGaugeReanchoring
  ConfiguredBaseProfiledSelectedRearReanchoring
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveSourceP0
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareRegularitySum
  FiniteSmoothRearFamilyMarkingAwareSource
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

/-- The spatial derivative of the genuinely shifted intrinsic front-normal
velocity. -/
private def sourceEtaFs
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ℝ → ℝ → ℝ := fun t s ↦
  ProfiledInterpolationFields.enS
    (sourceK0 (data O) n) (sourceK1 (data O) n)
    (data O).model.thetaBase ((data O).Hs n) t
    (s + ConfiguredBaseProfiledSelectedRearGaugeReanchoring.sigma
      (edgeOutput O n) (selected O n)
      (reanchored O n).gauge.q t +
      rawPhi (edgeOutput O n) t 0)

private theorem sourceEtaF_deriv
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (t s : ℝ) : HasDerivAt ((sourceFamily O n).etaF t)
      (sourceEtaFs O n t s) s := by
  let W := edgeOutput O n
  let S := selected O n
  let R := reanchored O n
  have hs : HasDerivAt (fun x : ℝ ↦ x +
      ConfiguredBaseProfiledSelectedRearGaugeReanchoring.sigma W S R.gauge.q t +
      frontPhase W t) 1 s := by
    simpa using ((hasDerivAt_id s).add_const
      (ConfiguredBaseProfiledSelectedRearGaugeReanchoring.sigma W S R.gauge.q t)).add_const
        (frontPhase W t)
  have h := (W.sourceCertificate.en_space t
    (s + ConfiguredBaseProfiledSelectedRearGaugeReanchoring.sigma
      W S R.gauge.q t + frontPhase W t)).comp s hs
  simpa [sourceFamily, ConfiguredBaseProfiledGenuineGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledGenuineGaugeResidual.residual,
    ConfiguredBaseProfiledGenuineGaugeResidual.geom,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.etaF,
    ConfiguredBaseProfiledSelectedRearReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearReanchoring.etaF,
    ConfiguredBaseProfiledSelectedRearReanchoring.rawEtaF,
    sourceEtaFs, W, S, R, TimeDependentSpatialReanchoring.shift] using h

private theorem sourceEtaFs_continuous
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (t : ℝ) : Continuous (sourceEtaFs O n t) := by
  let W := edgeOutput O n
  change Continuous (fun s ↦ ProfiledInterpolationFields.enS
    (sourceK0 (data O) n) (sourceK1 (data O) n)
    (data O).model.thetaBase ((data O).Hs n) t
    (s + ConfiguredBaseProfiledSelectedRearGaugeReanchoring.sigma W
      (selected O n) (reanchored O n).gauge.q t + rawPhi W t 0))
  have hd : ∀ s, HasDerivAt
      (ProfiledInterpolationFields.enS
        (sourceK0 (data O) n) (sourceK1 (data O) n)
        (data O).model.thetaBase ((data O).Hs n) t)
      (ProfiledInterpolationFields.enSS
        (sourceK0 (data O) n) (sourceK1 (data O) n)
        (sourceK0' (data O) n) (sourceK1' (data O) n)
        (data O).model.thetaBase ((data O).Hs n) t s) s :=
    (edgeOutput O n).sourceCertificate.en_space2 t
  exact continuous_iff_continuousAt.2 fun s ↦ by
    have hh := hd (s + ConfiguredBaseProfiledSelectedRearGaugeReanchoring.sigma W
      (selected O n) (reanchored O n).gauge.q t + rawPhi W t 0)
    have hc := ((hasDerivAt_id s).add_const
      (ConfiguredBaseProfiledSelectedRearGaugeReanchoring.sigma W
        (selected O n) (reanchored O n).gauge.q t)).add_const
          (rawPhi W t 0)
    simpa only [Function.comp_apply, id_eq] using (hh.comp s hc).continuousAt

private theorem sourceEtaF_periodic
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (t : ℝ) : Function.Periodic ((sourceFamily O n).etaF t)
      ((sourceFamily O n).P t) := by
  let A := sourceFamily O n
  have hcont : Continuous (A.phi t) :=
    continuous_iff_continuousAt.2 fun u ↦ (A.phi_deriv t u).continuousAt
  have hsurj : Surjective (A.phi t) :=
    surjective_of_continuous_quasiPeriodic (A.period_pos t) hcont (A.phi_shift t)
  intro s
  obtain ⟨u, rfl⟩ := hsurj s
  rw [← A.phi_shift t u, ← A.eta_link t (u + 1), ← A.eta_link t u]
  exact (edgeOutput O n).increment_c2.eta_periodic t u

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

private theorem sourceNormal_stopped
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (t : ℝ) (ht : t ∉ Set.Ioo (0 : ℝ) (edgeOutput O n).increment.T) :
    frameNormal (sourceFamily O n).Ydot
      (rearOwnAngle (sourceFamily O n).Theta (sourceFamily O n).delta
        (sourceFamily O n).sf) t = fun _ ↦ 0 :=
  normal_stopped_of_source (sourceFamily O n) t ht

private theorem sourcePhi1_eq_flowDeriv
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (t u : ℝ) :
    (sourceFamily O n).phi1 t u = FlowDerivative.flowDeriv
      (ProfiledInterpolationFields.hx
        (sourceK0 (data O) n) (sourceK1 (data O) n)
        (data O).model.thetaBase ((data O).Hs n))
      (ProfiledInterpolationFields.PhiB (edgeOutput O n).sourcePhi)
      (2 * (data O).Hs n) t u := by
  let W := edgeOutput O n
  have hflow := FlowDerivative.hasDerivAt_flow_initial
    W.sourceBounds.hlip W.sourceCertificate.field_cont
    W.sourceCertificate.field_flow
    (mul_pos (by norm_num) ((data O).model.separation_pos n))
    W.sourceCertificate.phi_initial W.sourceCertificate.field_space u t
  have heq := (W.sourcePhi_space (PathMetricCircle.B t) u).unique
    (by simpa [ProfiledInterpolationFields.PhiB] using hflow)
  simpa [sourceFamily, ConfiguredBaseProfiledGenuineGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledGenuineGaugeResidual.residual,
    ConfiguredBaseProfiledGenuineGaugeResidual.geom,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearReanchoring.phi1,
    ConfiguredBaseInterpolationMarkingSource.phi1, W] using heq

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

private theorem source_period_eq
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    (sourceFamily O n).P =
      ConfiguredBaseInterpolationShiftedFront.period (edgeOutput O n) := by
  funext t
  simp [sourceFamily,
    ConfiguredBaseProfiledGenuineGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledGenuineGaugeResidual.residual]

/-- All finite slice facts needed by the exact recursive branch, constructed
from the same genuine-gauge data stored in the configured edge source. -/
noncomputable def sourceSliceFacts
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    AnalyticSuccessorSliceFacts (sourceFamily O n) := by
  let W := edgeOutput O n
  let A := sourceFamily O n
  let markingLower := 2 * (data O).Hs n *
    Real.exp (-((W.sourceBounds.K : NNReal) : ℝ))
  let markingUpper := InterpolationPathDist.costFac
    (data O).kstar ((data O).Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps (data O) n)
  refine
    { periodUpper := 2 * (data O).Hs n
      periodLower_pos := sourceP0_pos (data O) n
      period_lower := ?_
      period_upper := ?_
      etaFs := sourceEtaFs O n
      etaF_deriv := sourceEtaF_deriv O n
      etaFs_continuous := sourceEtaFs_continuous O n
      etaF_periodic := sourceEtaF_periodic O n
      rearNormal_c2 := rearNormal_c2_of_source A
      normal_stopped := sourceNormal_stopped O n
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
        (speedCap (data O) n) sourceKh :=
      GaugeRearFamilyFromFront.rearDriftConst_nonneg
        (ConfiguredBaseProfiledSourceFamily.speedCap_nonnegative O n)
        sourceKh_nonnegative sourceKh_lt_one
    have hInv : 1 ≤ 1 / sourceP0 (data O) n := by
      have hn := (bounds O n).numerical_A
      nlinarith [mul_nonneg hkh hR]
    have hPone : sourceP0 (data O) n ≤ 1 := by
      have hp := sourceP0_pos (data O) n
      have := (le_div_iff₀ hp).mp hInv
      simpa using this
    have hH : 1 ≤ (data O).Hs n :=
      O.large.separation_one.trans ((data O).separation_lower n)
    rw [source_period_eq O n]
    simp only [ConfiguredBaseInterpolationShiftedFront.period]
    nlinarith
  · intro t
    rw [source_period_eq O n]
    rfl
  · intro t
    have hs := A.phi_shift t 0
    have hs' : A.phi t 1 = A.phi t 0 + A.P t := by simpa using hs
    linarith
  · dsimp [markingLower]
    exact mul_pos (mul_pos (by norm_num) ((data O).model.separation_pos n))
      (Real.exp_pos _)
  · intro t ht u
    rw [sourcePhi1_eq_flowDeriv O n t u]
    have hL : 0 < 2 * (data O).Hs n :=
      mul_pos (by norm_num) ((data O).model.separation_pos n)
    have hbd : ∀ s x, |ProfiledInterpolationFields.hx
        (sourceK0 (data O) n) (sourceK1 (data O) n)
        (data O).model.thetaBase ((data O).Hs n) s x| ≤
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
      ((data O).model.separation_pos n)).le
  · intro t _ht u
    rw [sourcePhi1_eq_flowDeriv O n t u]
    exact W.sourceBounds.hP1 t u
  · intro t
    exact ⟨W.increment.m t, by
      rintro _ ⟨u, rfl⟩
      exact W.increment.abs_eta_le t u⟩
  · intro t
    have hd1 : deriv (W.increment.eta t) = W.increment_c2.eta1 t := by
      funext u
      exact (W.increment_c2.eta_deriv t u).deriv
    change BddAbove (Set.range fun u ↦
      |iteratedDeriv 1 (W.increment.eta t) u|)
    simpa only [iteratedDeriv_one, hd1] using W.increment_c2.eta1_bdd t

/-- The actual edge period is bounded by the edge-indexed configured speed
ceiling, independently of the marking multiplier. -/
theorem sourcePeriodUpper_le_wideP1
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA)
    (MA0 : ℝ) (n : ℕ) :
    (sourceSliceFacts O n).periodUpper ≤
      ConfiguredRowCeilingPolynomialEnvelopes.wideP1 (data O) MA0 n := by
  unfold ConfiguredRowCeilingPolynomialEnvelopes.wideP1
    ConfiguredRichMapStageProvider.mapP1
  apply le_trans _ (le_max_left _ _)
  change 2 * (data O).Hs n ≤
    InterpolationPathDist.costFac (data O).kstar ((data O).Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps (data O) n)
  have hr : 0 ≤ InterpolationFrame.rate1Bound (data O).kstar
      ((data O).Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps (data O) n) :=
    InterpolationFrame.rate1Bound_nonneg (data O).kstar_nonneg
      ((data O).model.separation_pos n).le
      (ConfiguredApproximateDefectPathRowwise.edgeEps_nonneg (data O) n)
  have he : 1 ≤ Real.exp (InterpolationFrame.rate1Bound (data O).kstar
      ((data O).Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps (data O) n)) :=
    Real.one_le_exp hr
  unfold InterpolationPathDist.costFac
  simpa using (mul_le_mul_of_nonneg_left he
    (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
      ((data O).model.separation_pos n).le))


/-- Transport the exact slice sidecar through the same presentation used by
`sourceOfOutput0`. -/
noncomputable def alignedSliceFacts
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ}
    (hH : 1 ≤ (data O).Hs 0) (n : ℕ) :
    AnalyticSuccessorSliceFacts
      (ConfiguredRecursiveSourceP0AlignedBaseSourceFamily.source O C
        (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
        hH n) := by
  let A := ConfiguredGaugeFirstPhysicalSequence.presentations
    O.pair.input O.model_data n
  exact (sourceSliceFacts O n).phaseRigid (sourceFamily O n)
    A.phase A.translation A.rotation A.rotation_norm

/-- The unconditional exact sliced base column with sources and slice facts
attached at the same rich-stage index. -/
noncomputable def baseSlicedCorrelated
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ}
    (hH : 1 ≤ (data O).Hs 0) :
    SlicedCorrelatedColumn0
      (ConfiguredRecursiveSourceP0AlignedBaseSourceFamily.baseCorrelated
        O C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2)
        hH) where
  slice := alignedSliceFacts O C hH
  periodUpper_le := by
    intro n
    simpa [alignedSliceFacts,
      AnalyticSuccessorSliceFacts.phaseRigid_periodUpper] using
      sourcePeriodUpper_le_wideP1 O MA0 n

end ConfiguredBaseProfiledNAlignedSliceFacts
