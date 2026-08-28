import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSmoothSource

/-!
# Marking-aware finite successor sources

This is the nonaffine counterpart of the finite successor-source residual.  It
retains the actual spatial marking and states the intrinsic normal-velocity
bound directly.
-/

noncomputable section

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareSmoothSource

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  RearOwnHigherRegularity RearFamilyFrame

structure MarkingAwareFiniteSourceResidual
    {p q a b : Data} {Gamma : NormalPath p q} (Delta : NormalPath a b)
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    {D : NormalizedSteering S} (R : SuccessorRegularity D)
    (khatNext QmaxNext : ℝ) where
  etaF : ℝ → ℝ → ℝ
  Kx : ℝ → ℝ
  Dd : ℝ → ℝ
  gS : ℝ → ℝ → ℝ
  m : ℝ → ℝ
  kx : ℝ
  d : ℝ
  rear_period_pos : ∀ t, 0 < nextPeriod D t
  rear_period_le : ∀ t, nextPeriod D t ≤ QmaxNext
  tangential_zero : ∀ t, frameTangential
    (RearOwnHigherRegularity.partialTime (nextFront D R.sf))
    (nextAngle D R.sf) t 0 = 0
  jacobi : ∀ t x, HasDerivAt
    (fun x' => frameNormal
      (RearOwnHigherRegularity.partialTime (nextFront D R.sf))
      (nextAngle D R.sf) t x')
    (etaF t (R.sf t x) / Real.cos (D.arclength t (R.sf t x)) -
      frameNormal (RearOwnHigherRegularity.partialTime (nextFront D R.sf))
        (nextAngle D R.sf) t x) x
  marking : MarkingCertificate Delta etaF (period A)
  etaF_bound : ∀ t s, |etaF t s| ≤ Delta.m t
  rearKappa1_le : GaugeMarkedDataOfRearFamily.rearKappa1 kap ≤ khatNext
  angleTime_spatial : ∀ t x, HasDerivAt
    (RearOwnHigherRegularity.partialTime (nextAngle D R.sf) t)
    (RearOwnHigherRegularity.partialTime (nextCurvature D R.sf) t x) x
  mixed_derivative : ∀ t x, ∃ W : ℂ,
    HasDerivAt (fun r => Complex.exp
      (Complex.I * (nextAngle D R.sf r x : ℂ))) W t ∧
    HasDerivAt (fun y =>
      (frameTangential
          (RearOwnHigherRegularity.partialTime (nextFront D R.sf))
          (nextAngle D R.sf) t y : ℂ) *
          Complex.exp (Complex.I * (nextAngle D R.sf t y : ℂ)) +
        (frameNormal
          (RearOwnHigherRegularity.partialTime (nextFront D R.sf))
          (nextAngle D R.sf) t y : ℂ) *
          (Complex.I * Complex.exp
            (Complex.I * (nextAngle D R.sf t y : ℂ)))) W x
  Kx_bound : ∀ t x,
    |(curvature A t (R.sf t x) -
        Real.sin (D.arclength t (R.sf t x))) /
      Real.cos (D.arclength t (R.sf t x)) ^ 3| ≤ Kx t
  Kx_nonnegative : ∀ t, 0 ≤ Kx t
  Kx_le : ∀ t, Kx t ≤ kx
  Kx_continuous : Continuous (uncurry fun t x =>
    (curvature A t (R.sf t x) -
        Real.sin (D.arclength t (R.sf t x))) /
      Real.cos (D.arclength t (R.sf t x)) ^ 3)
  gS_deriv : ∀ t x, HasDerivAt
    (fun x' => etaF t (R.sf t x') /
      Real.cos (D.arclength t (R.sf t x'))) (gS t x) x
  gS_bound : ∀ t x, |gS t x| ≤ Dd t
  Dd_le : ∀ t, Dd t ≤ d * m t
  density_continuous : Continuous m
  density_nonnegative : ∀ t, 0 ≤ m t
  density_support : ∀ t ∉ Ioo (0 : ℝ) Delta.T, m t = 0
  density_domination : ∀ t,
    Delta.m t / Real.sqrt (1 - kap ^ 2) ≤ m t
  numerical_A :
    2 + 2 * khatNext * GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap ≤
      1 / periodLower
  numerical_K :
    (d + 2) + khatNext ^ 2 +
        2 * GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap * kx ≤
      1 / periodLower ^ 2 + khatNext ^ 2

/-- Assemble the next finite `MarkingAwareSource`.  All geometric and regularity fields are
discharged by `SmoothSource`, normalized steering, and successor regularity;
the argument `B` contains only the finite Jacobi/density estimates. -/
def MarkingAwareFiniteSourceResidual.toSource
    {p q a b : Data} {Gamma : NormalPath p q} {Delta : NormalPath a b}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    {D : NormalizedSteering S} {R : SuccessorRegularity D}
    (B : MarkingAwareFiniteSourceResidual Delta R khatNext QmaxNext) :
    MarkingAwareSource Delta periodLower kap khatNext QmaxNext := by
  have core :=
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.MarkingAwareSource.successorFrontCore A
  have hperiodPos : ∀ t, 0 < period A t := fun t =>
    lt_of_lt_of_le S.periodLower_pos (S.period_lower t)
  have hsteeringPeriodic : ∀ t,
      Function.Periodic (D.arclength t) (period A t) := by
    intro t x
    have hne := (hperiodPos t).ne'
    dsimp [NormalizedSteering.arclength]
    convert D.periodic t (x / period A t) using 1 <;> field_simp <;> ring
  have hcurvatureBound : ∀ t x, |curvature A t x| ≤ kap := by
    intro t x
    have H := S.curvature_bound t (x / period A t)
    simpa [normalizedCurvature, mul_div_cancel₀ x (hperiodPos t).ne'] using H
  have hcos : ∀ t x, Real.cos (D.arclength t x) ≠ 0 := by
    intro t x
    have hpos : 0 < Real.sqrt (1 - kap ^ 2) :=
      Real.sqrt_pos.mpr (by nlinarith [S.kap_nonnegative, S.kap_lt_one])
    exact ne_of_gt (lt_of_lt_of_le hpos
      (Shadowing.cos_ge_of_mem_strip
        (D.strip t (x / period A t)).1
        (D.strip t (x / period A t)).2))
  have hfrontTimeSmooth := contDiff_infty_partialTime R.front_smooth
  have hangleTimeSmooth := contDiff_infty_partialTime R.angle_smooth
  have hcurvatureTimeSmooth := contDiff_infty_partialTime R.curvature_smooth
  exact
    { F := front A
      Theta := angle A
      delta := D.arclength
      K := curvature A
      sf := R.sf
      P := period A
      P' := S.periodDerivative
      Ydot := RearOwnHigherRegularity.partialTime (nextFront D R.sf)
      etaF := B.etaF
      alphaT := RearOwnHigherRegularity.partialTime (nextAngle D R.sf)
      kT := RearOwnHigherRegularity.partialTime (nextCurvature D R.sf)
      Kx := B.Kx
      Dd := B.Dd
      gS := B.gS
      m := B.m
      kx := B.kx
      d := B.d
      kh_nonnegative := S.kap_nonnegative
      kh_lt_one := S.kap_lt_one
      strip_nonnegative := fun t x =>
        (D.strip t (x / period A t)).1
      strip_le := fun t x => (D.strip t (x / period A t)).2
      curvature_le := hcurvatureBound
      front_frenet := core.front_frenet
      angle_frenet := core.angle_frenet
      steering := R.steering_deriv
      sf_deriv := R.sf_deriv
      sf_rightInverse := R.sf_rightInverse
      cos_ne_zero := hcos
      rear_time_deriv := R.front_time_deriv
      front_contDiff := (_root_.contDiff_infty.mp S.front_smooth 1)
      angle_contDiff := (_root_.contDiff_infty.mp S.angle_smooth 1)
      steering_contDiff := (_root_.contDiff_infty.mp D.contDiff_infty_arclength 1)
      sf_contDiff := (_root_.contDiff_infty.mp R.sf_smooth 1)
      period_contDiff := (_root_.contDiff_infty.mp S.period_smooth 1)
      period_deriv := S.period_deriv
      frame_regularity := FrameRegularity.joint
        (_root_.contDiff_infty.mp hfrontTimeSmooth 2)
        (_root_.contDiff_infty.mp R.angle_smooth 2)
      rear_curvature_contDiff := by
        rw [show (fun t x => Real.tan (D.arclength t (R.sf t x))) =
          nextCurvature D R.sf from funext fun t => funext fun x =>
            (R.curvature_eq_tan t x).symm]
        exact _root_.contDiff_infty.mp R.curvature_smooth 1
      steering_periodic := hsteeringPeriodic
      front_periodic := core.front_periodic
      angle_periodic := core.angle_periodic
      rear_period_pos := B.rear_period_pos
      rear_period_le := B.rear_period_le
      tangential_zero := B.tangential_zero
      jacobi := B.jacobi
      period_pos := hperiodPos
      phi := B.marking.phi
      phi1 := B.marking.phi1
      phi2 := B.marking.phi2
      eta_link := B.marking.eta_link
      phi_shift := B.marking.shift
      phi_deriv := B.marking.deriv
      phi1_deriv := B.marking.deriv2
      phi1_continuous := B.marking.phi1_continuous
      phi2_continuous := B.marking.phi2_continuous
      etaF_bound := B.etaF_bound
      rearKappa1_le := B.rearKappa1_le
      rear_angle_time_deriv := R.angle_time_deriv
      rear_curvature_time_deriv := by
        intro t x
        simpa only [R.curvature_eq_tan] using R.curvature_time_deriv t x
      rear_angle_time_continuous :=
        (_root_.contDiff_infty.mp hangleTimeSmooth 0).continuous
      rear_curvature_time_continuous :=
        (_root_.contDiff_infty.mp hcurvatureTimeSmooth 0).continuous
      rear_angle_time_spatial := B.angleTime_spatial
      mixed_derivative := B.mixed_derivative
      Kx_bound := B.Kx_bound
      Kx_nonnegative := B.Kx_nonnegative
      Kx_le := B.Kx_le
      Kx_continuous := B.Kx_continuous
      gS_deriv := B.gS_deriv
      gS_bound := B.gS_bound
      Dd_le := B.Dd_le
      density_continuous := B.density_continuous
      density_nonnegative := B.density_nonnegative
      density_support := B.density_support
      density_domination := B.density_domination
      numerical_A := B.numerical_A
      numerical_K := B.numerical_K }


end FiniteSmoothRearFamilyMarkingAwareSmoothSource
