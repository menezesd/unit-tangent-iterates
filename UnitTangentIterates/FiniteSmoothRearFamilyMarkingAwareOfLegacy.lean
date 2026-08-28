import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSource

/-!
# Affine analytic sources as marking-aware sources

The initial configured interpolation uses the affine spatial marking
`phi(t,u) = P(t)u`.  This adapter embeds its analytic source into the sound
marking-aware recursion.  Successor rows still use their genuinely nonaffine
markings and are not covered by this compatibility constructor.
-/

noncomputable section

open Function Set MarkedSpace PathMetric PathMetric.NormalPath RearTrack

namespace FiniteSmoothRearFamilyMarkingAwareSource

open FiniteSmoothRearFamilyAnalyticSource

/-- An affine legacy source is a marking-aware source with constant first
spatial marking jet and zero second jet.  The intrinsic normal-velocity bound
is derived from the source's marked density bound by surjectivity of this
positive quasi-periodic marking. -/
def MarkingAwareSource.ofLegacy
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    (A : Source Gamma P0 kh khat Qmax) :
    MarkingAwareSource Gamma P0 kh khat Qmax := by
  let B : MarkingCertificate Gamma A.etaF A.P :=
    { phi := fun t u ↦ A.P t * u
      phi1 := fun t _ ↦ A.P t
      phi2 := fun _ _ ↦ 0
      eta_link := A.eta_link
      shift := by intro t u; ring
      deriv := by
        intro t u
        simpa using (hasDerivAt_id u).const_mul (A.P t)
      deriv2 := by
        intro t u
        simpa using hasDerivAt_const u (A.P t)
      phi1_continuous := by intro t; fun_prop
      phi2_continuous := by intro t; fun_prop }
  exact
    { F := A.F
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
      frame_regularity := FrameRegularity.joint
        A.rear_velocity_contDiff A.rear_angle_contDiff
      rear_curvature_contDiff := A.rear_curvature_contDiff
      steering_periodic := A.steering_periodic
      front_periodic := A.front_periodic
      angle_periodic := A.angle_periodic
      rear_period_pos := A.rear_period_pos
      rear_period_le := A.rear_period_le
      tangential_zero := A.tangential_zero
      jacobi := A.jacobi
      period_pos := A.period_pos
      phi := B.phi
      phi1 := B.phi1
      phi2 := B.phi2
      eta_link := B.eta_link
      phi_shift := B.shift
      phi_deriv := B.deriv
      phi1_deriv := B.deriv2
      phi1_continuous := B.phi1_continuous
      phi2_continuous := B.phi2_continuous
      etaF_bound := B.etaF_bound A.period_pos
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
      numerical_K := A.numerical_K }

end FiniteSmoothRearFamilyMarkingAwareSource
