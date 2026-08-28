import UnitTangentIterates.ConfiguredBaseProfiledSelectedRearReanchoring
import UnitTangentIterates.ConfiguredBaseProfiledSelectedSteeringC1
import UnitTangentIterates.RearOwnFrameSpatialC2OfMixed
import UnitTangentIterates.RearJacobiSourceCost
import UnitTangentIterates.RearDriftBound
import UnitTangentIterates.RearOwnDriftFundamental
import UnitTangentIterates.SelectedInverseUnique

/-!
# Exact profiled configured residual constructor

This module is the assembly boundary between the exact `B`-profiled selected
steering construction and the configured marking-aware source.  Everything
forced by front-phase reanchoring is discharged here.  The remaining weak
time/frame transport is isolated in `Transport`, while all scalar estimates
are isolated in `Bounds`.
-/

noncomputable section

open Function Set RearTrack

namespace ConfiguredBaseProfiledResidualConstructor

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseInterpolationMarkingAwareSourceResidual
  ConfiguredBaseProfiledSelectedRearReanchoring
  FiniteSmoothRearFamilyMarkingAwareSource
  RearFamilyFrame RearOwnArclength

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → MarkedSpace.Data} {n : ℕ} {A : RearCarrier D n}

/-- The exact stopped-clock selected steering block.  This is intentionally
only `C¹`; no false globally smooth affine-time selection is assumed. -/
structure ExactSelected
    (H : ConfiguredActualSubunitCurvature.Certificate D) where
  delta : ℝ → ℝ → ℝ
  sf : ℝ → ℝ → ℝ
  periodic : ∀ t, Periodic (delta t) (2 * D.Hs n)
  strip_nonnegative : ∀ t s, 0 ≤ delta t s
  strip_le : ∀ t s, delta t s ≤ Real.arcsin H.k0
  steering : ∀ t s, HasDerivAt (delta t)
    (rawK D n t s - Real.sin (delta t s)) s
  delta_contDiff : ContDiff ℝ 1 (uncurry delta)
  sf_contDiff : ContDiff ℝ 1 (uncurry sf)
  sf_rightInverse : ∀ t x, rearArclength (delta t) (sf t x) = x
  sf_deriv : ∀ t x, HasDerivAt (sf t)
    (1 / Real.cos (delta t (sf t x))) x

/-- The exact `B`-profiled steering construction supplies `ExactSelected`
without passing through the incompatible `flatTime (B t)` adapter. -/
theorem exists_exactSelected
    (C : ConstructedPulseWidth.C3Certificate D)
    (H : ConfiguredActualSubunitCurvature.Certificate D) (n : ℕ) :
    Nonempty (ExactSelected (D := D) (n := n) H) := by
  obtain ⟨delta, sf, hper, hstrip, hsteer, hdelta, hsf, hinv, hsfD⟩ :=
    ConfiguredBaseProfiledSelectedSteeringC1.exists_selected C H n
  exact ⟨
    { delta := delta
      sf := sf
      periodic := hper
      strip_nonnegative := fun t s ↦ (hstrip t s).1
      strip_le := fun t s ↦ (hstrip t s).2
      steering := hsteer
      delta_contDiff := hdelta
      sf_contDiff := hsf
      sf_rightInverse := hinv
      sf_deriv := hsfD }⟩

namespace ExactSelected

variable (W : Output D Q n A)
  {H : ConfiguredActualSubunitCurvature.Certificate D}
  (S : ExactSelected (n := n) H)

abbrev deltaR : ℝ → ℝ → ℝ := deltaShift W S.delta
abbrev sfR : ℝ → ℝ → ℝ := sfShift W S.delta S.sf
abbrev psiR : ℝ → ℝ → ℝ :=
  rearOwnAngle (geometry W).Theta (deltaR W S) (sfR W S)
abbrev rearR : ℝ → ℝ → ℂ :=
  rearOwn (geometry W).F (geometry W).Theta (deltaR W S) (sfR W S)

theorem deltaR_contDiff : ContDiff ℝ 1 (uncurry (deltaR W S)) :=
  deltaShift_contDiff W S.delta_contDiff

theorem sfR_contDiff : ContDiff ℝ 1 (uncurry (sfR W S)) :=
  sfShift_contDiff W S.delta_contDiff S.sf_contDiff

theorem deltaR_periodic (t : ℝ) :
    Periodic (deltaR W S t) (ConfiguredBaseInterpolationShiftedFront.period W t) := by
  simpa [ConfiguredBaseInterpolationShiftedFront.period] using
    deltaShift_periodic W (P := fun _ ↦ 2 * D.Hs n) S.periodic t

theorem deltaR_strip_nonnegative (t s : ℝ) : 0 ≤ deltaR W S t s := by
  exact S.strip_nonnegative t (s + frontPhase W t)

theorem deltaR_strip_le (t s : ℝ) : deltaR W S t s ≤ Real.arcsin H.k0 := by
  exact S.strip_le t (s + frontPhase W t)

theorem deltaR_steering (t s : ℝ) : HasDerivAt (deltaR W S t)
    ((geometry W).K t s - Real.sin (deltaR W S t s)) s := by
  exact deltaShift_steering W S.steering t s

theorem sfR_rightInverse (t x : ℝ) :
    rearArclength (deltaR W S t) (sfR W S t x) = x := by
  exact sfShift_rightInverse W
    (fun t ↦ S.delta_contDiff.continuous.comp
      (continuous_const.prodMk continuous_id)) S.sf_rightInverse t x

theorem sfR_deriv (t x : ℝ) : HasDerivAt (sfR W S t)
    (1 / Real.cos (deltaR W S t (sfR W S t x))) x :=
  sfShift_deriv W S.sf_deriv t x

theorem deltaR_cos_ne_zero (t s : ℝ) : Real.cos (deltaR W S t s) ≠ 0 := by
  exact ne_of_gt (SelectedPathData.cos_steering_pos
    ((H.front_nonnegative n 0).trans (H.front_le n 0)) H.k0_lt_one
    (S.strip_nonnegative t) (S.strip_le t) (s + frontPhase W t))

theorem rear_curvature_contDiff : ContDiff ℝ 1
    (uncurry fun t x ↦ Real.tan (deltaR W S t (sfR W S t x))) := by
  have hpair : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦
      (p.1, uncurry (sfR W S) p)) :=
    contDiff_fst.prodMk (sfR_contDiff W S)
  have harg : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦
      uncurry (deltaR W S) (p.1, uncurry (sfR W S) p)) :=
    (deltaR_contDiff W S).comp hpair
  have hsin := Real.contDiff_sin.comp harg
  have hcos := Real.contDiff_cos.comp harg
  simpa [Real.tan_eq_sin_div_cos, uncurry] using
    hsin.div hcos (fun p ↦ deltaR_cos_ne_zero W S p.1 (sfR W S p.1 p.2))

abbrev kappaR : ℝ → ℝ → ℝ :=
  fun t x ↦ Real.tan (deltaR W S t (sfR W S t x))

abbrev jacobiSource : ℝ → ℝ → ℝ :=
  fun t x ↦ (geometry W).etaF t (sfR W S t x) /
    Real.cos (deltaR W S t (sfR W S t x))

abbrev curvatureSpatial : ℝ → ℝ → ℝ :=
  fun t x ↦ ((geometry W).K t (sfR W S t x) -
      Real.sin (deltaR W S t (sfR W S t x))) /
    Real.cos (deltaR W S t (sfR W S t x)) ^ 3

theorem psiR_contDiff : ContDiff ℝ 1 (uncurry (psiR W S)) := by
  have hpair : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦
      (p.1, uncurry (sfR W S) p)) :=
    contDiff_fst.prodMk (sfR_contDiff W S)
  have hTheta := (geometry W).angle_contDiff.comp hpair
  have hdelta := (deltaR_contDiff W S).comp hpair
  simpa [psiR, rearOwnAngle, RearTrack.rearAngle, uncurry] using
    hTheta.sub hdelta

theorem psiR_spatial (t x : ℝ) :
    HasDerivAt (psiR W S t) (kappaR W S t x) x := by
  exact RearOwnIsFront.hasDerivAt_rearOwnAngle
    (geometry W).angle_frenet (deltaR_steering W S) (sfR_deriv W S) t x

theorem etaF_continuous : Continuous (uncurry (geometry W).etaF) := by
  have hphase :=
    ConfiguredBaseInterpolationShiftedFront.phase_contDiff W |>.continuous
  have hpair : Continuous (fun p : ℝ × ℝ ↦
      (p.1, p.2 + frontPhase W p.1)) :=
    continuous_fst.prodMk
      (continuous_snd.add (hphase.comp continuous_fst))
  simpa [geometry, etaF, rawEtaF, frontPhase,
    TimeDependentSpatialReanchoring.shift, uncurry] using
    W.sourceCertificate.en_cont.comp hpair

theorem curvature_continuous : Continuous (uncurry (geometry W).K) := by
  have hphase :=
    ConfiguredBaseInterpolationShiftedFront.phase_contDiff W |>.continuous
  have hpair : Continuous (fun p : ℝ × ℝ ↦
      (p.1, p.2 + frontPhase W p.1)) :=
    continuous_fst.prodMk
      (continuous_snd.add (hphase.comp continuous_fst))
  simpa [geometry, K, rawK, frontPhase,
    TimeDependentSpatialReanchoring.shift, uncurry] using
    W.sourceCertificate.kappa_C1.continuous.comp hpair

theorem jacobiSource_continuous :
    Continuous (uncurry (jacobiSource W S)) := by
  have hpair : Continuous (fun p : ℝ × ℝ ↦
      (p.1, uncurry (sfR W S) p)) :=
    continuous_fst.prodMk (sfR_contDiff W S).continuous
  have heta := (etaF_continuous W).comp hpair
  have hdelta := (deltaR_contDiff W S).continuous.comp hpair
  have hcos := Real.continuous_cos.comp hdelta
  simpa [jacobiSource, uncurry] using
    heta.div hcos (fun p ↦ deltaR_cos_ne_zero W S p.1 (sfR W S p.1 p.2))

theorem curvatureSpatial_continuous :
    Continuous (uncurry (curvatureSpatial W S)) := by
  have hpair : Continuous (fun p : ℝ × ℝ ↦
      (p.1, uncurry (sfR W S) p)) :=
    continuous_fst.prodMk (sfR_contDiff W S).continuous
  have hK := (curvature_continuous W).comp hpair
  have hdelta := (deltaR_contDiff W S).continuous.comp hpair
  have hsin := Real.continuous_sin.comp hdelta
  have hcos := Real.continuous_cos.comp hdelta
  simpa [curvatureSpatial, uncurry] using
    (hK.sub hsin).div (hcos.pow 3)
      (fun p ↦ pow_ne_zero 3
        (deltaR_cos_ne_zero W S p.1 (sfR W S p.1 p.2)))

end ExactSelected

open ExactSelected

/-- Weak qualitative transport across the moving rear phase.  This is the
precise output expected from the exact-C1 spatial-frame construction. -/
structure Transport (W : Output D Q n A)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (S : ExactSelected (n := n) H) where
  Ydot : ℝ → ℝ → ℂ
  alphaT : ℝ → ℝ → ℝ
  kT : ℝ → ℝ → ℝ
  gS : ℝ → ℝ → ℝ
  Ydot_continuous : Continuous (uncurry Ydot)
  gS_continuous : Continuous (uncurry gS)
  rear_time : ∀ t x, HasDerivAt (fun r ↦ rearR W S r x) (Ydot t x) t
  anchor_flow : ∀ t, HasDerivAt
    (fun r ↦ anchorPhi W S.delta r 0)
    (-frameTangential Ydot (psiR W S) t (anchorPhi W S.delta t 0)) t
  jacobi : ∀ t x, HasDerivAt
    (fun x' ↦ frameNormal Ydot (psiR W S) t x')
    (jacobiSource W S t x -
      frameNormal Ydot (psiR W S) t x) x
  gS_deriv : ∀ t x, HasDerivAt (jacobiSource W S t) (gS t x) x
  curvatureSpatial_deriv : ∀ t x,
    HasDerivAt (kappaR W S t) (curvatureSpatial W S t x) x
  rear_angle_time_deriv : ∀ t x, HasDerivAt
    (fun r ↦ psiR W S r x) (alphaT t x) t
  rear_curvature_time_deriv : ∀ t x, HasDerivAt
    (fun r ↦ Real.tan (deltaR W S r (sfR W S r x))) (kT t x) t
  rear_angle_time_continuous : Continuous (uncurry alphaT)
  rear_curvature_time_continuous : Continuous (uncurry kT)
  rear_angle_time_spatial : ∀ t x, HasDerivAt (alphaT t) (kT t x) x
  mixed : ∀ t x, ∃ Z : ℂ,
    HasDerivAt
      (fun r ↦ Complex.exp (Complex.I * (psiR W S r x : ℂ))) Z t ∧
    HasDerivAt
      (fun y ↦
        (frameTangential Ydot (psiR W S) t y : ℂ) *
            Complex.exp (Complex.I * (psiR W S t y : ℂ)) +
        (frameNormal Ydot (psiR W S) t y : ℂ) *
            (Complex.I * Complex.exp (Complex.I * (psiR W S t y : ℂ)))) Z x

namespace Transport

/-- The spatial frame certificates are consequences of the primitive mixed,
Jacobi, source-derivative, and curvature-derivative witnesses. -/
def spatialFrames (T : Transport W H S) :
    RearOwnFrameDrift.SpatialC2
        (frameTangential T.Ydot (psiR W S)) ×
      RearOwnFrameDrift.SpatialC2
        (frameNormal T.Ydot (psiR W S)) :=
  RearOwnFrameSpatialC2OfMixed.spatialC2
    T.Ydot_continuous (psiR_contDiff W S).continuous
    (rear_curvature_contDiff W S).continuous
    T.rear_angle_time_continuous (jacobiSource_continuous W S)
    T.gS_continuous (curvatureSpatial_continuous W S)
    (psiR_spatial W S) T.rear_angle_time_deriv T.mixed T.jacobi
    T.gS_deriv T.curvatureSpatial_deriv

def tangential (T : Transport W H S) :
    RearOwnFrameDrift.SpatialC2
      (frameTangential T.Ydot (psiR W S)) :=
  (T.spatialFrames).1

def normal (T : Transport W H S) :
    RearOwnFrameDrift.SpatialC2
      (frameNormal T.Ydot (psiR W S)) :=
  (T.spatialFrames).2

end Transport

/-- The remaining scalar estimates.  No geometry or differential identities
are duplicated here. -/
structure Bounds (W : Output D Q n A) (P0 kh khat Qmax : ℝ)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (S : ExactSelected (n := n) H) (T : Transport W H S) where
  Kx : ℝ → ℝ
  Dd : ℝ → ℝ
  m : ℝ → ℝ
  kx : ℝ
  d : ℝ
  rear_period_pos : ∀ t,
    0 < rearArclength (deltaR W S t)
      (ConfiguredBaseInterpolationShiftedFront.period W t)
  rear_period_le : ∀ t,
    rearArclength (deltaR W S t)
      (ConfiguredBaseInterpolationShiftedFront.period W t) ≤ Qmax
  tangential1_bound : ∀ t x,
    |T.tangential.xi1 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa1 kh * m t
  tangential2_bound : ∀ t x,
    |T.tangential.xi2 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa2 kh * m t
  tangential_period_bound : ∀ t,
    ∀ x ∈ Icc (0 : ℝ)
      (rearArclength (deltaR W S t)
        (ConfiguredBaseInterpolationShiftedFront.period W t)),
      |frameTangential T.Ydot (psiR W S) t x| ≤
        GaugeRearFamilyFromFront.rearDriftConst Qmax kh * W.increment.m t
  rearKappa1_le : GaugeMarkedDataOfRearFamily.rearKappa1 kh ≤ khat
  Kx_bound : ∀ t x,
    |((geometry W).K t (sfR W S t x) -
        Real.sin (deltaR W S t (sfR W S t x))) /
      Real.cos (deltaR W S t (sfR W S t x)) ^ 3| ≤ Kx t
  Kx_nonnegative : ∀ t, 0 ≤ Kx t
  Kx_le : ∀ t, Kx t ≤ kx
  gS_bound : ∀ t x, |T.gS t x| ≤ Dd t
  Dd_le : ∀ t, Dd t ≤ d * m t
  density_continuous : Continuous m
  density_nonnegative : ∀ t, 0 ≤ m t
  density_support : ∀ t ∉ Ioo 0 W.increment.T, m t = 0
  density_domination : ∀ t,
    W.increment.m t / Real.sqrt (1 - kh ^ 2) ≤ m t
  numerical_A : 2 + 2 * khat *
    GaugeRearFamilyFromFront.rearDriftConst Qmax kh ≤ 1 / P0
  numerical_K : d + 2 + khat ^ 2 + 2 *
    GaugeRearFamilyFromFront.rearDriftConst Qmax kh * kx ≤
      1 / P0 ^ 2 + khat ^ 2

/-! ## Audited configured scalar choices -/

/-- The uniform cosine floor on the selected strip. -/
def auditedGamma (H : ConfiguredActualSubunitCurvature.Certificate D) : ℝ :=
  Real.sqrt (1 - H.k0 ^ 2)

/-- The configured density: the transported front density plus the exact
spatial normal-rate majorant retained by the profiled interpolation. -/
def auditedDensity (W : Output D Q n A)
    (H : ConfiguredActualSubunitCurvature.Certificate D) : ℝ → ℝ :=
  fun t ↦ W.increment.m t / auditedGamma H +
    |W.sourceBounds.c1| * W.sourceBounds.m t

/-- Retaining the density identity from the profiled path constructor exposes
the exact scalar multiplier hidden in the audited rear density. -/
theorem auditedDensity_eq_increment (W : Output D Q n A)
    (H : ConfiguredActualSubunitCurvature.Certificate D) :
    auditedDensity W H = fun t ↦
      (1 / auditedGamma H + |W.sourceBounds.c1|) * W.increment.m t := by
  funext t
  rw [auditedDensity, ← W.source_density_eq]
  ring

/-- The explicit inverse-Jacobi source constant at spatial scale one. -/
def auditedJacobiSourceConst
    (H : ConfiguredActualSubunitCurvature.Certificate D) : ℝ :=
  RearJacobiSourceCost.jacobiSourceConst H.k0 1

private theorem auditedGamma_pos
    (H : ConfiguredActualSubunitCurvature.Certificate D) :
    0 < auditedGamma H := by
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative 0 0).trans (H.front_le 0 0)
  exact Real.sqrt_pos.mpr (by nlinarith [H.k0_lt_one])

/-- The audited rear density costs only its explicit scalar multiplier times
the already configured interpolation defect. -/
theorem auditedDensity_integral_le_rowDefect_mul
    (W : Output D Q n A)
    (H : ConfiguredActualSubunitCurvature.Certificate D) :
    (∫ t in (0 : ℝ)..1, auditedDensity W H t) ≤
      (1 / auditedGamma H + |W.sourceBounds.c1|) *
        ConfiguredApproximateDefectPathRowwise.rowDefect D n := by
  have hc : 0 ≤ 1 / auditedGamma H + |W.sourceBounds.c1| :=
    add_nonneg (one_div_nonneg.mpr (auditedGamma_pos H).le) (abs_nonneg _)
  rw [auditedDensity_eq_increment, intervalIntegral.integral_const_mul]
  have hcost : (∫ t in (0 : ℝ)..1, W.increment.m t) ≤
      ConfiguredApproximateDefectPathRowwise.rowDefect D n := by
    simpa [PathMetric.NormalPath.cost, W.increment_time_one] using W.increment_cost
  exact mul_le_mul_of_nonneg_left hcost hc

/-- At the configured separation scale, the exact inverse flow coefficient
retained by the interpolation constructor is at most one. -/
theorem source_c1_abs_le_one
    (W : Output D Q n A) (hH : 1 ≤ D.Hs 0) :
    |W.sourceBounds.c1| ≤ 1 := by
  have hL : 1 ≤ D.Hs n := hH.trans (D.separation_lower n)
  have hr : 0 ≤ InterpolationFrame.rate1Bound D.kstar (D.Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps D n) :=
    InterpolationFrame.rate1Bound_nonneg D.kstar_nonneg (zero_le_one.trans hL)
      (ConfiguredApproximateDefectPathRowwise.edgeEps_nonneg D n)
  have he : 1 ≤ Real.exp (InterpolationFrame.rate1Bound D.kstar (D.Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps D n)) :=
    Real.one_le_exp hr
  have htwo : 1 ≤ 2 * D.Hs n := by nlinarith
  have hfac : 1 ≤ InterpolationPathDist.costFac D.kstar (D.Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps D n) := by
    unfold InterpolationPathDist.costFac
    exact htwo.trans (le_mul_of_one_le_right (by positivity) he)
  have hfac_pos : 0 < InterpolationPathDist.costFac D.kstar (D.Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps D n) :=
    zero_lt_one.trans_le hfac
  rw [W.source_c1_eq, abs_of_pos (one_div_pos.mpr hfac_pos)]
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hfac

/-- The factor `2 H_n` in `costFac` gives the sharper half bound needed by
the physical row budget. -/
theorem source_c1_abs_le_half
    (W : Output D Q n A) (hH : 1 ≤ D.Hs 0) :
    |W.sourceBounds.c1| ≤ 1 / 2 := by
  have hL : 1 ≤ D.Hs n := hH.trans (D.separation_lower n)
  have hr : 0 ≤ InterpolationFrame.rate1Bound D.kstar (D.Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps D n) :=
    InterpolationFrame.rate1Bound_nonneg D.kstar_nonneg (zero_le_one.trans hL)
      (ConfiguredApproximateDefectPathRowwise.edgeEps_nonneg D n)
  have he : 1 ≤ Real.exp (InterpolationFrame.rate1Bound D.kstar (D.Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps D n)) :=
    Real.one_le_exp hr
  have hfac : 2 ≤ InterpolationPathDist.costFac D.kstar (D.Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps D n) := by
    unfold InterpolationPathDist.costFac
    have htwo : 2 ≤ 2 * D.Hs n := by nlinarith
    exact htwo.trans (le_mul_of_one_le_right (by positivity) he)
  have hfac_pos : 0 < InterpolationPathDist.costFac D.kstar (D.Hs n)
      (ConfiguredApproximateDefectPathRowwise.edgeEps D n) :=
    (by norm_num : (0 : ℝ) < 2).trans_le hfac
  rw [W.source_c1_eq, abs_of_pos (one_div_pos.mpr hfac_pos)]
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hfac

/-- The configured separation floor makes the audited multiplier uniform in
the row: the hidden interpolation coefficient contributes at most one. -/
theorem auditedDensity_integral_le_uniform
    (W : Output D Q n A)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (hH : 1 ≤ D.Hs 0) :
    (∫ t in (0 : ℝ)..1, auditedDensity W H t) ≤
      (1 / auditedGamma H + 1) *
        ConfiguredApproximateDefectPathRowwise.rowDefect D n := by
  have hdefect : 0 ≤ ConfiguredApproximateDefectPathRowwise.rowDefect D n := by
    exact InterpolationPathDist.interpPathCost_nonneg D.kstar_nonneg D.kd_nonneg
      (CurvatureStabilityL1.l1Modulus_nonneg _ _ _)
      (D.model.separation_pos n).le
      (ConfiguredApproximateDefectPathRowwise.edgeEps_nonneg D n)
  have hcoeff : 1 / auditedGamma H + |W.sourceBounds.c1| ≤
      1 / auditedGamma H + 1 := by
    linarith [source_c1_abs_le_one W hH]
  exact (auditedDensity_integral_le_rowDefect_mul W H).trans
    (mul_le_mul_of_nonneg_right hcoeff hdefect)

/-- A half lower bound for the selected-strip cosine turns the uniform
multiplier into the rational constant three. -/
theorem auditedDensity_integral_le_three_of_gamma_half
    (W : Output D Q n A)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (hH : 1 ≤ D.Hs 0) (hgamma : 1 / 2 ≤ auditedGamma H) :
    (∫ t in (0 : ℝ)..1, auditedDensity W H t) ≤
      3 * ConfiguredApproximateDefectPathRowwise.rowDefect D n := by
  have hinv : 1 / auditedGamma H ≤ 2 := by
    rw [div_le_iff₀ (auditedGamma_pos H)]
    nlinarith
  have hdefect : 0 ≤ ConfiguredApproximateDefectPathRowwise.rowDefect D n := by
    exact InterpolationPathDist.interpPathCost_nonneg D.kstar_nonneg D.kd_nonneg
      (CurvatureStabilityL1.l1Modulus_nonneg _ _ _)
      (D.model.separation_pos n).le
      (ConfiguredApproximateDefectPathRowwise.edgeEps_nonneg D n)
  exact (auditedDensity_integral_le_uniform W H hH).trans
    (mul_le_mul_of_nonneg_right (by linarith) hdefect)

/-- For the actual configured terminal curvature `k₀ = 1/2`, the uniform
audited multiplier is bounded by the rational constant three. -/
theorem auditedDensity_integral_le_three
    (W : Output D Q n A)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (hH : 1 ≤ D.Hs 0) (hk0 : H.k0 = 1 / 2) :
    (∫ t in (0 : ℝ)..1, auditedDensity W H t) ≤
      3 * ConfiguredApproximateDefectPathRowwise.rowDefect D n := by
  have hgamma_half : (1 : ℝ) / 2 ≤ auditedGamma H := by
    rw [auditedGamma, hk0]
    apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  exact auditedDensity_integral_le_three_of_gamma_half W H hH hgamma_half

/-- The existing physical diagonal `2 H_n * rowDefect_n` already absorbs the
full audited density.  Thus retaining `c1` requires no rescaling of the edge
large-separation construction. -/
theorem auditedDensity_integral_le_physicalDefect
    (W : Output D Q n A)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (hH : 1 ≤ D.Hs 0) (hk0 : H.k0 = 1 / 2) :
    (∫ t in (0 : ℝ)..1, auditedDensity W H t) ≤
      (2 * D.Hs n) *
        ConfiguredApproximateDefectPathRowwise.rowDefect D n := by
  have hgamma : (2 : ℝ) / 3 ≤ auditedGamma H := by
    rw [auditedGamma, hk0]
    apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  have hinv : 1 / auditedGamma H ≤ 3 / 2 := by
    rw [div_le_iff₀ (auditedGamma_pos H)]
    nlinarith
  have hcoefficient :
      1 / auditedGamma H + |W.sourceBounds.c1| ≤ 2 := by
    linarith [source_c1_abs_le_half W hH]
  have hphysical : 2 ≤ 2 * D.Hs n := by
    have hL := hH.trans (D.separation_lower n)
    nlinarith
  have hdefect : 0 ≤ ConfiguredApproximateDefectPathRowwise.rowDefect D n := by
    exact InterpolationPathDist.interpPathCost_nonneg D.kstar_nonneg D.kd_nonneg
      (CurvatureStabilityL1.l1Modulus_nonneg _ _ _)
      (D.model.separation_pos n).le
      (ConfiguredApproximateDefectPathRowwise.edgeEps_nonneg D n)
  exact (auditedDensity_integral_le_rowDefect_mul W H).trans <| by
    exact mul_le_mul_of_nonneg_right (hcoefficient.trans hphysical) hdefect

private theorem auditedGamma_le_one
    (H : ConfiguredActualSubunitCurvature.Certificate D) :
    auditedGamma H ≤ 1 := by
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative 0 0).trans (H.front_le 0 0)
  have hs : 0 ≤ 1 - H.k0 ^ 2 := by nlinarith [H.k0_lt_one]
  have hsq := Real.sq_sqrt hs
  have hg0 := Real.sqrt_nonneg (1 - H.k0 ^ 2)
  dsimp [auditedGamma]
  nlinarith [sq_nonneg H.k0]

/-- The exact `enS` field, expressed in the same front-phase gauge as the
configured geometry. -/
private def auditedEtaS (W : Output D Q n A) : ℝ → ℝ → ℝ :=
  fun t s ↦ ProfiledInterpolationFields.enS
    (sourceK0 D n) (sourceK1 D n) D.model.thetaBase (D.Hs n)
    t (s + frontPhase W t)

private theorem auditedEtaS_deriv (W : Output D Q n A) (t s : ℝ) :
    HasDerivAt ((geometry W).etaF t) (auditedEtaS W t s) s := by
  have hshift : HasDerivAt (fun x : ℝ ↦ x + frontPhase W t) 1 s := by
    simpa using (hasDerivAt_id s).add_const (frontPhase W t)
  have h := (W.sourceCertificate.en_space t (s + frontPhase W t)).comp s hshift
  simpa [geometry, etaF, rawEtaF, auditedEtaS,
    TimeDependentSpatialReanchoring.shift] using h

/-- The audited formulas fill every scalar field of `Bounds`.  The hypotheses
are precisely the externally selected period/jet/numerical ceilings; the
strip, inverse-Jacobi, support, sign, and domination estimates are proved here. -/
def auditedBounds (W : Output D Q n A) (P0 khat Qmax : ℝ)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (S : ExactSelected (n := n) H) (T : Transport W H S)
    (hperiod : ∀ t, ConfiguredBaseInterpolationShiftedFront.period W t ≤ Qmax)
    (hkhat : GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 ≤ khat)
    (hnumA : 2 + 2 * khat *
      GaugeRearFamilyFromFront.rearDriftConst Qmax H.k0 ≤ 1 / P0)
    (hnumK : auditedJacobiSourceConst H + 2 + khat ^ 2 + 2 *
      GaugeRearFamilyFromFront.rearDriftConst Qmax H.k0 *
        SelInvFrontStripC2.stripCurvConst H.k0 ≤
          1 / P0 ^ 2 + khat ^ 2) :
    Bounds W P0 H.k0 khat Qmax H S T := by
  have hk0 : 0 ≤ H.k0 :=
    (H.front_nonnegative n 0).trans (H.front_le n 0)
  have hgamma : 0 < auditedGamma H := auditedGamma_pos H
  have hgamma1 : auditedGamma H ≤ 1 := auditedGamma_le_one H
  have hdensity0 : ∀ t, 0 ≤ auditedDensity W H t := by
    intro t
    exact add_nonneg (div_nonneg (W.increment.m_nonneg t) hgamma.le)
      (mul_nonneg (abs_nonneg _) (W.sourceBounds.hm0 t))
  have hincrement_le : ∀ t, W.increment.m t ≤ auditedDensity W H t := by
    intro t
    have hdiv : W.increment.m t ≤
        W.increment.m t / auditedGamma H := by
      rw [le_div_iff₀ hgamma]
      exact mul_le_of_le_one_right (W.increment.m_nonneg t) hgamma1
    exact hdiv.trans (le_add_of_nonneg_right
      (mul_nonneg (abs_nonneg _) (W.sourceBounds.hm0 t)))
  have hetas : ∀ t s, |auditedEtaS W t s| ≤ auditedDensity W H t := by
    intro t s
    calc
      |auditedEtaS W t s| ≤ W.sourceBounds.S1 t :=
        W.sourceBounds.hS1bd t (s + frontPhase W t)
      _ ≤ W.sourceBounds.c1 * W.sourceBounds.m t := W.sourceBounds.hS1m t
      _ ≤ |W.sourceBounds.c1| * W.sourceBounds.m t :=
        mul_le_mul_of_nonneg_right (le_abs_self W.sourceBounds.c1)
          (W.sourceBounds.hm0 t)
      _ ≤ auditedDensity W H t := le_add_of_nonneg_left
        (div_nonneg (W.increment.m_nonneg t) hgamma.le)
  have hrearPeriodPos : ∀ t, 0 < rearArclength (deltaR W S t)
      (ConfiguredBaseInterpolationShiftedFront.period W t) := by
    intro t
    exact SelectedInverseUnique.rearArclength_pos ((geometry W).period_pos t) hk0
      H.k0_lt_one
      ((deltaR_contDiff W S).continuous.comp
        (continuous_const.prodMk continuous_id))
      (fun s ↦ ⟨deltaR_strip_nonnegative W S t s, deltaR_strip_le W S t s⟩)
  have hnormalPeriod : ∀ t, Periodic
      (frameNormal T.Ydot (psiR W S) t)
      (rearArclength (deltaR W S t)
        (ConfiguredBaseInterpolationShiftedFront.period W t)) := by
    intro t
    exact RearOwnDriftFundamental.periodic_frameNormal_rearOwn
      hk0 H.k0_lt_one (deltaR_strip_nonnegative W S) (deltaR_strip_le W S)
      (deltaR_cos_ne_zero W S) (geometry W).front_frenet
      (geometry W).angle_frenet (deltaR_steering W S) (sfR_deriv W S)
      (sfR_rightInverse W S) (deltaR_periodic W S)
      (geometry W).front_periodic (geometry W).angle_periodic
      (geometry W).front_contDiff (geometry W).angle_contDiff
      (deltaR_contDiff W S) (sfR_contDiff W S) (by
        simpa [ConfiguredBaseInterpolationShiftedFront.period] using
          (contDiff_const : ContDiff ℝ 1
            (fun _ : ℝ ↦ 2 * D.Hs n))) T.rear_time t
  have hnormal : ∀ t x, |frameNormal T.Ydot (psiR W S) t x| ≤
      W.increment.m t / auditedGamma H := by
    intro t x
    exact RearOwnTangentialCost.abs_frameNormal_le_slice hk0 H.k0_lt_one
      (deltaR_strip_nonnegative W S) (deltaR_strip_le W S) hrearPeriodPos
      hnormalPeriod T.jacobi (geometry W).etaF_bound t x
  have hgammaSq : auditedGamma H ^ 2 = 1 - H.k0 ^ 2 := by
    exact Real.sq_sqrt (by nlinarith [hk0, H.k0_lt_one])
  have hxi1raw : ∀ t x, |T.tangential.xi1 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * W.increment.m t := by
    intro t x
    have heq : T.tangential.xi1 t x =
        frameNormal T.Ydot (psiR W S) t x * kappaR W S t x := rfl
    have htan := RearOwnTangential.abs_tan_le_strip hk0 H.k0_lt_one
      (deltaR_strip_nonnegative W S t (sfR W S t x))
      (deltaR_strip_le W S t (sfR W S t x))
    have hmul : |frameNormal T.Ydot (psiR W S) t x| *
        |kappaR W S t x| ≤
        (W.increment.m t / auditedGamma H) *
          (H.k0 / auditedGamma H) :=
      mul_le_mul (hnormal t x) (by simpa [kappaR] using htan)
        (abs_nonneg _) (div_nonneg (W.increment.m_nonneg t) hgamma.le)
    rw [heq, abs_mul]
    calc
      |frameNormal T.Ydot (psiR W S) t x| * |kappaR W S t x| ≤
          (W.increment.m t / auditedGamma H) *
            (H.k0 / auditedGamma H) := hmul
      _ = GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * W.increment.m t := by
        rw [GaugeMarkedDataOfRearFamily.rearKappa1]
        rw [← hgammaSq]
        field_simp [ne_of_gt hgamma]
        <;> ring
  have htangential1 : ∀ t x, |T.tangential.xi1 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * auditedDensity W H t := by
    intro t x
    exact (hxi1raw t x).trans (mul_le_mul_of_nonneg_left (hincrement_le t)
      (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hk0 H.k0_lt_one))
  have hxi2raw : ∀ t x, |T.tangential.xi2 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa2 H.k0 * W.increment.m t := by
    intro t x
    let M := W.increment.m t
    let N := frameNormal T.Ydot (psiR W S) t x
    let G := jacobiSource W S t x
    let kap := kappaR W S t x
    let kapS := curvatureSpatial W S t x
    have hM0 : 0 ≤ M := W.increment.m_nonneg t
    have hN : |N| ≤ M / auditedGamma H := hnormal t x
    have hG : |G| ≤ M / auditedGamma H := by
      exact RearOwnTangential.abs_div_cos_le_strip hk0 H.k0_lt_one
        (deltaR_strip_nonnegative W S t (sfR W S t x))
        (deltaR_strip_le W S t (sfR W S t x))
        ((geometry W).etaF_bound t (sfR W S t x))
    have hkap : |kap| ≤ H.k0 / auditedGamma H := by
      exact RearOwnTangential.abs_tan_le_strip hk0 H.k0_lt_one
        (deltaR_strip_nonnegative W S t (sfR W S t x))
        (deltaR_strip_le W S t (sfR W S t x))
    have hkapS : |kapS| ≤
        2 * H.k0 / auditedGamma H ^ 3 := by
      exact RearOwnTangential.abs_curvDeriv_le_strip hk0 H.k0_lt_one
        (deltaR_strip_nonnegative W S t (sfR W S t x))
        (deltaR_strip_le W S t (sfR W S t x))
        ((geometry W).curvature_abs_le_of_actual H le_rfl t (sfR W S t x))
    have hmain : |(G - N) * kap + N * kapS| ≤
        (M / auditedGamma H + M / auditedGamma H) *
            (H.k0 / auditedGamma H) +
          (M / auditedGamma H) * (2 * H.k0 / auditedGamma H ^ 3) := by
      calc
        |(G - N) * kap + N * kapS| ≤
            |G - N| * |kap| + |N| * |kapS| := by
              simpa [abs_mul] using abs_add_le ((G - N) * kap) (N * kapS)
        _ ≤ (|G| + |N|) * |kap| + |N| * |kapS| := by
          gcongr
          exact abs_sub G N
        _ ≤ (M / auditedGamma H + M / auditedGamma H) *
              (H.k0 / auditedGamma H) +
            (M / auditedGamma H) * (2 * H.k0 / auditedGamma H ^ 3) := by
          gcongr
    rw [show T.tangential.xi2 t x = (G - N) * kap + N * kapS by rfl]
    calc
      |(G - N) * kap + N * kapS| ≤
          (M / auditedGamma H + M / auditedGamma H) *
              (H.k0 / auditedGamma H) +
            (M / auditedGamma H) * (2 * H.k0 / auditedGamma H ^ 3) := hmain
      _ = GaugeMarkedDataOfRearFamily.rearKappa2 H.k0 * M := by
        rw [GaugeMarkedDataOfRearFamily.rearKappa2,
          RearOwnTangentialCostC2.gaugeGrowth2]
        rw [← hgammaSq]
        field_simp [ne_of_gt hgamma]
        <;> ring
  have htangential2 : ∀ t x, |T.tangential.xi2 t x| ≤
      GaugeMarkedDataOfRearFamily.rearKappa2 H.k0 * auditedDensity W H t := by
    intro t x
    exact (hxi2raw t x).trans (mul_le_mul_of_nonneg_left (hincrement_le t)
      (GaugeMarkedDataOfRearFamily.rearKappa2_nonneg hk0 H.k0_lt_one))
  have htangentialZero : ∀ t,
      frameTangential T.Ydot (psiR W S) t 0 = 0 := by
    intro t
    have hconst : HasDerivAt
        (fun r ↦ anchorPhi W S.delta r 0) 0 t := by
      convert hasDerivAt_const t (0 : ℝ) using 1
      funext r
      exact anchorPhi_zero W S.delta r
    have hu := (T.anchor_flow t).unique hconst
    simpa [anchorPhi_zero W S.delta t] using neg_eq_zero.mp hu
  have htangentialPeriod : ∀ t,
      ∀ x ∈ Icc (0 : ℝ)
        (rearArclength (deltaR W S t)
          (ConfiguredBaseInterpolationShiftedFront.period W t)),
        |frameTangential T.Ydot (psiR W S) t x| ≤
          GaugeRearFamilyFromFront.rearDriftConst Qmax H.k0 * W.increment.m t := by
    intro t x hx
    have hfund := RearOwnDriftFundamental.abs_le_of_deriv_le_on_Icc
      (hrearPeriodPos t).le (T.tangential.deriv1 t) (htangentialZero t)
      (hxi1raw t) hx
    have hcoef : rearArclength (deltaR W S t)
          (ConfiguredBaseInterpolationShiftedFront.period W t) *
          (GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * W.increment.m t) ≤
        Qmax * (GaugeMarkedDataOfRearFamily.rearKappa1 H.k0 * W.increment.m t) :=
      mul_le_mul_of_nonneg_right
        ((ArclengthInverse.rearArclength_le_of_period
          ((deltaR_contDiff W S).continuous.comp
            (continuous_const.prodMk continuous_id))
          ((geometry W).period_pos t).le).trans (hperiod t))
        (mul_nonneg
          (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg hk0 H.k0_lt_one)
          (W.increment.m_nonneg t))
    refine hfund.trans (hcoef.trans_eq ?_)
    simp [GaugeRearFamilyFromFront.rearDriftConst,
      GaugeMarkedDataOfRearFamily.rearKappa1]
    ring
  have hgS : ∀ t x, |T.gS t x| ≤
      auditedJacobiSourceConst H * auditedDensity W H t := by
    intro t x
    apply RearJacobiSourceCost.abs_source_deriv_le hk0 H.k0_lt_one one_pos
      (auditedEtaS_deriv W t)
    · intro s
      exact ((geometry W).etaF_bound t s).trans (hincrement_le t)
    · intro s
      simpa using hetas t s
    · exact deltaR_strip_nonnegative W S t
    · exact deltaR_strip_le W S t
    · exact deltaR_steering W S t
    · exact (geometry W).curvature_abs_le_of_actual H le_rfl t
    · exact sfR_deriv W S t
    · exact T.gS_deriv t
  exact
    { Kx := fun _ ↦ SelInvFrontStripC2.stripCurvConst H.k0
      Dd := fun t ↦ auditedJacobiSourceConst H * auditedDensity W H t
      m := auditedDensity W H
      kx := SelInvFrontStripC2.stripCurvConst H.k0
      d := auditedJacobiSourceConst H
      rear_period_pos := hrearPeriodPos
      rear_period_le := fun t ↦
        (ArclengthInverse.rearArclength_le_of_period
          ((deltaR_contDiff W S).continuous.comp
            (continuous_const.prodMk continuous_id))
          ((geometry W).period_pos t).le).trans (hperiod t)
      tangential1_bound := htangential1
      tangential2_bound := htangential2
      tangential_period_bound := htangentialPeriod
      rearKappa1_le := hkhat
      Kx_bound := fun t x ↦ by
        simpa [SelInvFrontStripC2.stripCurvConst] using
          GaugeRearFamilyFromFront.abs_drift_le hk0 H.k0_lt_one
            ((geometry W).curvature_abs_le_of_actual H le_rfl t (sfR W S t x))
            (deltaR_strip_nonnegative W S t (sfR W S t x))
            (deltaR_strip_le W S t (sfR W S t x))
      Kx_nonnegative := fun _ ↦
        SelInvFrontStripC2.stripCurvConst_nonneg hk0
      Kx_le := fun _ ↦ le_rfl
      gS_bound := hgS
      Dd_le := fun _ ↦ le_rfl
      density_continuous :=
        W.increment.cont_m.div_const (auditedGamma H) |>.add
          (continuous_const.mul W.sourceBounds.hmc)
      density_nonnegative := hdensity0
      density_support := fun t ht ↦ by
        have ht' : t ∉ Ioo (0 : ℝ) 1 := by
          simpa [W.increment_time_one] using ht
        simp [auditedDensity, W.increment.m_stop t ht,
          W.sourceBounds.hmstop t ht']
      density_domination := fun t ↦ le_add_of_nonneg_right
        (mul_nonneg (abs_nonneg _) (W.sourceBounds.hm0 t))
      numerical_A := hnumA
      numerical_K := hnumK }

/-- Assemble the complete residual from exact selected data, weak transported
frame data, and scalar bounds. -/
def residual (W : Output D Q n A) (P0 kh khat Qmax : ℝ)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (hkh : H.k0 = kh) (S : ExactSelected (n := n) H)
    (T : Transport W H S) (B : Bounds W P0 kh khat Qmax H S T) :
    Residual W P0 kh khat Qmax := by
  subst kh
  exact
    { geometry := geometry W
      delta := deltaR W S
      sf := sfR W S
      Ydot := T.Ydot
      alphaT := T.alphaT
      kT := T.kT
      Kx := B.Kx
      Dd := B.Dd
      gS := T.gS
      m := B.m
      kx := B.kx
      d := B.d
      kh_nonnegative := (H.front_nonnegative n 0).trans (H.front_le n 0)
      kh_lt_one := H.k0_lt_one
      strip_nonnegative := deltaR_strip_nonnegative W S
      strip_le := deltaR_strip_le W S
      steering := deltaR_steering W S
      sf_deriv := sfR_deriv W S
      sf_rightInverse := sfR_rightInverse W S
      cos_ne_zero := deltaR_cos_ne_zero W S
      rear_time_deriv := T.rear_time
      steering_contDiff := deltaR_contDiff W S
      sf_contDiff := sfR_contDiff W S
      frame_regularity := FrameRegularity.spatial
        { tangential := T.tangential
          normal := T.normal
          tangential1_bound := B.tangential1_bound
          tangential2_bound := B.tangential2_bound
          tangential_period_bound := B.tangential_period_bound }
      rear_curvature_contDiff := rear_curvature_contDiff W S
      steering_periodic := deltaR_periodic W S
      rear_period_pos := B.rear_period_pos
      rear_period_le := B.rear_period_le
      anchorPhi := anchorPhi W S.delta
      anchor_zero := anchorPhi_zero W S.delta
      anchor_flow := T.anchor_flow
      jacobi := T.jacobi
      rearKappa1_le := B.rearKappa1_le
      rear_angle_time_deriv := T.rear_angle_time_deriv
      rear_curvature_time_deriv := T.rear_curvature_time_deriv
      rear_angle_time_continuous := T.rear_angle_time_continuous
      rear_curvature_time_continuous := T.rear_curvature_time_continuous
      rear_angle_time_spatial := T.rear_angle_time_spatial
      mixed_derivative := T.mixed
      Kx_bound := B.Kx_bound
      Kx_nonnegative := B.Kx_nonnegative
      Kx_le := B.Kx_le
      Kx_continuous := curvatureSpatial_continuous W S
      gS_deriv := T.gS_deriv
      gS_bound := B.gS_bound
      Dd_le := B.Dd_le
      density_continuous := B.density_continuous
      density_nonnegative := B.density_nonnegative
      density_support := B.density_support
      density_domination := B.density_domination
      numerical_A := B.numerical_A
      numerical_K := B.numerical_K }

/-- The complete exact configured base source.  The actual curvature ceiling
is fixed to `H.k0`, so after choosing the exact selected data the only inputs
are its minimized transport and scalar bounds packages. -/
def baseSource (W : Output D Q n A) (P0 khat Qmax : ℝ)
    (H : ConfiguredActualSubunitCurvature.Certificate D)
    (S : ExactSelected (n := n) H)
    (T : Transport W H S)
    (B : Bounds W P0 H.k0 khat Qmax H S T) :
    MarkingAwareSource W.increment P0 H.k0 khat Qmax :=
  Residual.toSourceOfActual W P0 H.k0 khat Qmax
    (residual W P0 H.k0 khat Qmax H rfl S T B) H le_rfl

end ConfiguredBaseProfiledResidualConstructor
