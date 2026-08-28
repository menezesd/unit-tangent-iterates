import UnitTangentIterates.FiniteSmoothRearFamilyAppliedSource
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource

/-!
# Affine marking adapter for analytic rear-family sources

The original analytic source already identifies the marked front density at
the affine coordinate `P t * u`.  This leaf retains all of its physical and
regularity fields and installs that affine coordinate as the explicit marking
of a `MarkingAwareSource`.
-/

noncomputable section

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareAffineSourceAdapter

/-- Forget no analytic information while making the source marking explicitly
affine. -/
def affineSource
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    (A : FiniteSmoothRearFamilyAnalyticSource.Source Gamma P0 kh khat Qmax) :
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource
      Gamma P0 kh khat Qmax where
  F := A.F
  Theta := A.Theta
  delta := A.delta
  K := A.K
  sf := A.sf
  P := A.P
  P' := A.P'
  Ydot := A.Ydot
  etaF := A.etaF
  alphaT := A.alphaT
  kT := A.kT
  Kx := A.Kx
  Dd := A.Dd
  gS := A.gS
  m := A.m
  kx := A.kx
  d := A.d
  kh_nonnegative := A.kh_nonnegative
  kh_lt_one := A.kh_lt_one
  strip_nonnegative := A.strip_nonnegative
  strip_le := A.strip_le
  curvature_le := A.curvature_le
  front_frenet := A.front_frenet
  angle_frenet := A.angle_frenet
  steering := A.steering
  sf_deriv := A.sf_deriv
  sf_rightInverse := A.sf_rightInverse
  cos_ne_zero := A.cos_ne_zero
  rear_time_deriv := A.rear_time_deriv
  front_contDiff := A.front_contDiff
  angle_contDiff := A.angle_contDiff
  steering_contDiff := A.steering_contDiff
  sf_contDiff := A.sf_contDiff
  period_contDiff := A.period_contDiff
  period_deriv := A.period_deriv
  frame_regularity := .joint A.rear_velocity_contDiff A.rear_angle_contDiff
  rear_curvature_contDiff := A.rear_curvature_contDiff
  steering_periodic := A.steering_periodic
  front_periodic := A.front_periodic
  angle_periodic := A.angle_periodic
  rear_period_pos := A.rear_period_pos
  rear_period_le := A.rear_period_le
  tangential_zero := A.tangential_zero
  jacobi := A.jacobi
  period_pos := A.period_pos
  phi := fun t u ↦ A.P t * u
  phi1 := fun t _ ↦ A.P t
  phi2 := fun _ _ ↦ 0
  eta_link := A.eta_link
  phi_shift := by intro t u; ring
  phi_deriv := by
    intro t u
    simpa [mul_comm] using (hasDerivAt_id u).const_mul (A.P t)
  phi1_deriv := by intro t u; exact hasDerivAt_const u (A.P t)
  phi1_continuous := by intro t; exact continuous_const
  phi2_continuous := by intro t; exact continuous_const
  etaF_bound := by
    intro t s
    let u := s / A.P t
    have harg : A.P t * u = s := by
      dsimp [u]
      field_simp [(A.period_pos t).ne']
    rw [← harg, ← A.eta_link t u]
    exact Gamma.abs_eta_le t u
  rearKappa1_le := A.rearKappa1_le
  rear_angle_time_deriv := A.rear_angle_time_deriv
  rear_curvature_time_deriv := A.rear_curvature_time_deriv
  rear_angle_time_continuous := A.rear_angle_time_continuous
  rear_curvature_time_continuous := A.rear_curvature_time_continuous
  rear_angle_time_spatial := A.rear_angle_time_spatial
  mixed_derivative := A.mixed_derivative
  Kx_bound := A.Kx_bound
  Kx_nonnegative := A.Kx_nonnegative
  Kx_le := A.Kx_le
  Kx_continuous := A.Kx_continuous
  gS_deriv := A.gS_deriv
  gS_bound := A.gS_bound
  Dd_le := A.Dd_le
  density_continuous := A.density_continuous
  density_nonnegative := A.density_nonnegative
  density_support := A.density_support
  density_domination := A.density_domination
  numerical_A := A.numerical_A
  numerical_K := A.numerical_K

/-- The old separated slice facts become the exact affine facts used by the
variable-period physical transition. -/
def affineSeparatedFacts
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : FiniteSmoothRearFamilyAnalyticSource.Source Gamma P0 kh khat Qmax}
    (S : FiniteSmoothRearFamilyAppliedSource.SeparatedFacts A P1) :
    FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
      (affineSource A) P1 where
  P0_pos := S.P0_pos
  period_lower := S.period_lower
  period_upper := S.period_upper
  etaFs := S.etaFs
  etaF_deriv := S.etaF_deriv
  etaFs_continuous := S.etaFs_continuous
  etaF_periodic := S.etaF_periodic
  rearNormal_c2 := by
    intro t
    have H : ContDiff ℝ (2 : ℕ)
        (Function.uncurry (RearFamilyFrame.frameNormal A.Ydot
          (rearOwnAngle A.Theta A.delta A.sf))) :=
      RearOwnTangential.contDiff_frameNormal
        A.rear_velocity_contDiff A.rear_angle_contDiff
    simpa [FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearNormal,
      affineSource, Function.uncurry] using
      H.comp (contDiff_const.prodMk contDiff_id)
  eta_link_affine := A.eta_link
  normal_stopped := S.normal_stopped

end FiniteSmoothRearFamilyMarkingAwareAffineSourceAdapter
