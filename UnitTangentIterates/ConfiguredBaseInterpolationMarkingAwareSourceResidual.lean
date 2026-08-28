import UnitTangentIterates.ConfiguredBaseInterpolationShiftedFront
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSource
import UnitTangentIterates.TimeDependentSpatialReanchoring

/-!
# Residual selected-rear data for the configured base source

The configured interpolation now retains its exact profiled front and gauge
marking.  Consequently a base `MarkingAwareSource` should not be supplied as
one opaque callback.  This module fills every front and marking field and
isolates only the selected-steering/rear-family analysis that remains.
-/

noncomputable section

open Set Function

namespace ConfiguredBaseInterpolationMarkingAwareSourceResidual

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseInterpolationMarkingSource
  ConfiguredBaseInterpolationShiftedFront
  FiniteSmoothRearFamilyMarkingAwareSource

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → MarkedSpace.Data} {n : ℕ} {A : RearCarrier D n}
  (W : Output D Q n A) (P0 kh khat Qmax : ℝ)

/-- The geometric part of a base source.  Keeping this package separate lets
the selected rear construction use a spatially reanchored representative
instead of being definitionally tied to `ConfiguredBaseInterpolationShiftedFront`.
The configured shifted front remains available through `configuredGeometry`.
-/
structure Geometry where
  F : ℝ → ℝ → ℂ
  Theta : ℝ → ℝ → ℝ
  K : ℝ → ℝ → ℝ
  etaF : ℝ → ℝ → ℝ
  phi : ℝ → ℝ → ℝ
  phi1 : ℝ → ℝ → ℝ
  phi2 : ℝ → ℝ → ℝ
  front_frenet : ∀ t s,
    HasDerivAt (F t) (Complex.exp (Complex.I * (Theta t s : ℂ))) s
  angle_frenet : ∀ t s, HasDerivAt (Theta t) (K t s) s
  front_contDiff : ContDiff ℝ 1 (uncurry F)
  angle_contDiff : ContDiff ℝ 1 (uncurry Theta)
  front_periodic : ∀ t s, F t (s + period W t) = F t s
  angle_periodic : ∀ t s,
    Theta t (s + period W t) = Theta t s + 2 * Real.pi
  period_pos : ∀ t, 0 < period W t
  eta_link : ∀ t u, W.increment.eta t u = etaF t (phi t u)
  phi_shift : ∀ t u, phi t (u + 1) = phi t u + period W t
  phi_deriv : ∀ t u, HasDerivAt (phi t) (phi1 t u) u
  phi1_deriv : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u
  phi1_continuous : ∀ t, Continuous (phi1 t)
  phi2_continuous : ∀ t, Continuous (phi2 t)
  etaF_bound : ∀ t s, |etaF t s| ≤ W.increment.m t
  curvature_abs_le_of_actual :
    ∀ (H : ConfiguredActualSubunitCurvature.Certificate D) {k : ℝ},
      H.k0 ≤ k → ∀ t s, |K t s| ≤ k

/-- The original retained shifted-front geometry, as a canonical input to the
generalized residual interface. -/
def configuredGeometry : Geometry W := by
  let C := certificate W
  let M := markingCertificate W
  exact
    { F := front W
      Theta := angle W
      K := curvature W
      etaF := etaF W
      phi := phi W
      phi1 := M.phi1
      phi2 := M.phi2
      front_frenet := C.front_frenet
      angle_frenet := C.angle_frenet
      front_contDiff := ConfiguredBaseInterpolationShiftedFront.front_contDiff W
      angle_contDiff := ConfiguredBaseInterpolationShiftedFront.angle_contDiff W
      front_periodic := front_periodic W
      angle_periodic := C.angle_closing
      period_pos := C.period_pos
      eta_link := C.eta_link
      phi_shift := C.marking_shift
      phi_deriv := C.marking_deriv
      phi1_deriv := C.marking_second_deriv
      phi1_continuous := C.marking_first_continuous
      phi2_continuous := C.marking_second_continuous
      etaF_bound := C.eta_bound
      curvature_abs_le_of_actual := fun H {k} hkh ↦
        curvature_abs_le_of_actual W H hkh }

/-- Exactly the selected-rear information not already present in the retained
configured interpolation output. -/
structure Residual where
  geometry : Geometry W
  delta : ℝ → ℝ → ℝ
  sf : ℝ → ℝ → ℝ
  Ydot : ℝ → ℝ → ℂ
  alphaT : ℝ → ℝ → ℝ
  kT : ℝ → ℝ → ℝ
  Kx : ℝ → ℝ
  Dd : ℝ → ℝ
  gS : ℝ → ℝ → ℝ
  m : ℝ → ℝ
  kx : ℝ
  d : ℝ
  kh_nonnegative : 0 ≤ kh
  kh_lt_one : kh < 1
  strip_nonnegative : ∀ t s, 0 ≤ delta t s
  strip_le : ∀ t s, delta t s ≤ Real.arcsin kh
  steering : ∀ t s, HasDerivAt (delta t)
    (geometry.K t s - Real.sin (delta t s)) s
  sf_deriv : ∀ t x, HasDerivAt (sf t)
    (1 / Real.cos (delta t (sf t x))) x
  sf_rightInverse : ∀ t x,
    RearTrack.rearArclength (delta t) (sf t x) = x
  cos_ne_zero : ∀ t s, Real.cos (delta t s) ≠ 0
  rear_time_deriv : ∀ t x, HasDerivAt
    (fun r ↦ RearOwnArclength.rearOwn geometry.F geometry.Theta delta sf r x)
    (Ydot t x) t
  steering_contDiff : ContDiff ℝ 1 (uncurry delta)
  sf_contDiff : ContDiff ℝ 1 (uncurry sf)
  frame_regularity : FrameRegularity W.increment Ydot geometry.Theta delta sf
    (period W) m kh Qmax
  rear_curvature_contDiff : ContDiff ℝ 1
    (uncurry fun t x ↦ Real.tan (delta t (sf t x)))
  steering_periodic : ∀ t, Periodic (delta t) (period W t)
  rear_period_pos : ∀ t,
    0 < RearTrack.rearArclength (delta t) (period W t)
  rear_period_le : ∀ t,
    RearTrack.rearArclength (delta t) (period W t) ≤ Qmax
  /-- The selected-rear gauge flow, retained before the analytic producer is
  erased.  Fixing its marked origin forces the tangential rate to vanish
  there, so pinning is derived rather than postulated. -/
  anchorPhi : ℝ → ℝ → ℝ
  anchor_zero : ∀ t, anchorPhi t 0 = 0
  anchor_flow : ∀ t, HasDerivAt (fun r ↦ anchorPhi r 0)
    (-RearFamilyFrame.frameTangential Ydot
      (RearOwnArclength.rearOwnAngle geometry.Theta delta sf) t (anchorPhi t 0)) t
  jacobi : ∀ t x, HasDerivAt
    (fun x' ↦ RearFamilyFrame.frameNormal Ydot
      (RearOwnArclength.rearOwnAngle geometry.Theta delta sf) t x')
    (geometry.etaF t (sf t x) / Real.cos (delta t (sf t x)) -
      RearFamilyFrame.frameNormal Ydot
        (RearOwnArclength.rearOwnAngle geometry.Theta delta sf) t x) x
  rearKappa1_le : GaugeMarkedDataOfRearFamily.rearKappa1 kh ≤ khat
  rear_angle_time_deriv : ∀ t x, HasDerivAt
    (fun r ↦ RearOwnArclength.rearOwnAngle geometry.Theta delta sf r x)
    (alphaT t x) t
  rear_curvature_time_deriv : ∀ t x, HasDerivAt
    (fun r ↦ Real.tan (delta r (sf r x))) (kT t x) t
  rear_angle_time_continuous : Continuous (uncurry alphaT)
  rear_curvature_time_continuous : Continuous (uncurry kT)
  rear_angle_time_spatial : ∀ t s, HasDerivAt (alphaT t) (kT t s) s
  mixed_derivative : ∀ t s, ∃ Z,
    HasDerivAt
      (fun r ↦ Complex.exp (Complex.I *
        (RearOwnArclength.rearOwnAngle geometry.Theta delta sf r s : ℂ))) Z t ∧
    HasDerivAt
      (fun x ↦
        (RearFamilyFrame.frameTangential Ydot
          (RearOwnArclength.rearOwnAngle geometry.Theta delta sf) t x : ℂ) *
            Complex.exp (Complex.I *
              (RearOwnArclength.rearOwnAngle geometry.Theta delta sf t x : ℂ)) +
        (RearFamilyFrame.frameNormal Ydot
          (RearOwnArclength.rearOwnAngle geometry.Theta delta sf) t x : ℂ) *
            (Complex.I * Complex.exp (Complex.I *
              (RearOwnArclength.rearOwnAngle geometry.Theta delta sf t x : ℂ)))) Z s
  Kx_bound : ∀ t x,
    |(geometry.K t (sf t x) - Real.sin (delta t (sf t x))) /
      Real.cos (delta t (sf t x)) ^ 3| ≤ Kx t
  Kx_nonnegative : ∀ t, 0 ≤ Kx t
  Kx_le : ∀ t, Kx t ≤ kx
  Kx_continuous : Continuous (uncurry fun t x ↦
    (geometry.K t (sf t x) - Real.sin (delta t (sf t x))) /
      Real.cos (delta t (sf t x)) ^ 3)
  gS_deriv : ∀ t x, HasDerivAt
    (fun x' ↦ geometry.etaF t (sf t x') / Real.cos (delta t (sf t x')))
    (gS t x) x
  gS_bound : ∀ t x, |gS t x| ≤ Dd t
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

/-- Complete the exact base `MarkingAwareSource`; front and marking fields are
not assumptions. -/
def Residual.toSource (R : Residual W P0 kh khat Qmax)
    (hcurvature : ∀ t s, |R.geometry.K t s| ≤ kh) :
    MarkingAwareSource W.increment P0 kh khat Qmax := by
  exact
    { F := R.geometry.F
      Theta := R.geometry.Theta
      delta := R.delta
      K := R.geometry.K
      sf := R.sf
      P := period W
      P' := fun _ ↦ 0
      Ydot := R.Ydot
      etaF := R.geometry.etaF
      alphaT := R.alphaT
      kT := R.kT
      Kx := R.Kx
      Dd := R.Dd
      gS := R.gS
      m := R.m
      kx := R.kx
      d := R.d
      kh_nonnegative := R.kh_nonnegative
      kh_lt_one := R.kh_lt_one
      strip_nonnegative := R.strip_nonnegative
      strip_le := R.strip_le
      curvature_le := hcurvature
      front_frenet := R.geometry.front_frenet
      angle_frenet := R.geometry.angle_frenet
      steering := R.steering
      sf_deriv := R.sf_deriv
      sf_rightInverse := R.sf_rightInverse
      cos_ne_zero := R.cos_ne_zero
      rear_time_deriv := R.rear_time_deriv
      front_contDiff := R.geometry.front_contDiff
      angle_contDiff := R.geometry.angle_contDiff
      steering_contDiff := R.steering_contDiff
      sf_contDiff := R.sf_contDiff
      period_contDiff := contDiff_const
      period_deriv := fun t ↦ hasDerivAt_const t (period W t)
      frame_regularity := R.frame_regularity
      rear_curvature_contDiff := R.rear_curvature_contDiff
      steering_periodic := R.steering_periodic
      front_periodic := R.geometry.front_periodic
      angle_periodic := R.geometry.angle_periodic
      rear_period_pos := R.rear_period_pos
      rear_period_le := R.rear_period_le
      tangential_zero := fun t ↦
        TimeDependentSpatialReanchoring.tangential_zero_of_fixed_flow
          R.anchor_zero R.anchor_flow t
      jacobi := R.jacobi
      period_pos := R.geometry.period_pos
      phi := R.geometry.phi
      phi1 := R.geometry.phi1
      phi2 := R.geometry.phi2
      eta_link := R.geometry.eta_link
      phi_shift := R.geometry.phi_shift
      phi_deriv := R.geometry.phi_deriv
      phi1_deriv := R.geometry.phi1_deriv
      phi1_continuous := R.geometry.phi1_continuous
      phi2_continuous := R.geometry.phi2_continuous
      etaF_bound := R.geometry.etaF_bound
      rearKappa1_le := R.rearKappa1_le
      rear_angle_time_deriv := R.rear_angle_time_deriv
      rear_curvature_time_deriv := R.rear_curvature_time_deriv
      rear_angle_time_continuous := R.rear_angle_time_continuous
      rear_curvature_time_continuous := R.rear_curvature_time_continuous
      rear_angle_time_spatial := R.rear_angle_time_spatial
      mixed_derivative := R.mixed_derivative
      Kx_bound := R.Kx_bound
      Kx_nonnegative := R.Kx_nonnegative
      Kx_le := R.Kx_le
      Kx_continuous := R.Kx_continuous
      gS_deriv := R.gS_deriv
      gS_bound := R.gS_bound
      Dd_le := R.Dd_le
      density_continuous := R.density_continuous
      density_nonnegative := R.density_nonnegative
      density_support := R.density_support
      density_domination := R.density_domination
      numerical_A := R.numerical_A
      numerical_K := R.numerical_K }

/-- Complete the base source using the retained actual curvature ceiling. -/
def Residual.toSourceOfActual (R : Residual W P0 kh khat Qmax)
    (H : ConfiguredActualSubunitCurvature.Certificate D) (hkh : H.k0 ≤ kh) :
    MarkingAwareSource W.increment P0 kh khat Qmax :=
  Residual.toSource W P0 kh khat Qmax R
    (R.geometry.curvature_abs_le_of_actual H hkh)

end ConfiguredBaseInterpolationMarkingAwareSourceResidual
