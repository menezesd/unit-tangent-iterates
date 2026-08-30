import UnitTangentIterates.ReachableVariableSpeedFrontCurvature
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareAppliedSource
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSuccessorFront
import UnitTangentIterates.GaugeFrameTimeBounds
import UnitTangentIterates.RearOwnFrameSpatialC2OfMixed
import UnitTangentIterates.SelInvFrontJacobiC2

/-!
# Intrinsic curvature stability for a variable-speed chosen marking

The curvature equation is an equation in physical arclength.  If `u` is a
variable-speed marking with speed `g`, then

`partial_s^2 eta = eta_uu / g^2 - g_u * eta_u / g^3`.

In particular, the raw expression `iteratedDeriv 2 eta` is not the curvature
forcing unless `g = 1` and `g_u = 0`.  This module derives the intrinsic
equation retained by a marking-aware source, proves cancellation of the
tangential term along its chosen gauge flow, and applies the stopped-curvature
argument with the resulting intrinsic forcing.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric
open RearFamilyFrame RearOwnArclength RearOwnTangential RearOwnHigherRegularity
  VariableMarkedTube

namespace ReachableVariableSpeedFrontCurvatureIntrinsicStable

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront

variable {p q a b model : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax : ℝ}

/-- Marked distance from an ordinary model upgrades the variable tube to the
row-local speed floor used by the intrinsic initial-curvature estimate. -/
private theorem variableTube_with_model_distance_speed_floor
    {model p : Data} {c0 k0 d0 c C kmin delta r : ℝ}
    (hmodel : IsTubeMember c0 k0 d0 model)
    (hp : IsVariableTubeMember c C kmin delta p)
    (hdist : dist model p ≤ r) :
    IsVariableTubeMember (c0 - r) C kmin delta p := by
  refine { hp with speed_lb := ?_ }
  intro u
  have hvR := (MarkedSpace.dist_vel_apply_le model p u).trans hdist
  have htri : ‖model.2.1 u‖ ≤
      ‖model.2.1 u - p.2.1 u‖ + ‖p.2.1 u‖ := by
    calc
      ‖model.2.1 u‖ = ‖(model.2.1 u - p.2.1 u) + p.2.1 u‖ := by ring
      _ ≤ ‖model.2.1 u - p.2.1 u‖ + ‖p.2.1 u‖ := norm_add_le _ _
  linarith [hmodel.speed_lb u]

/-- Initial curvature control from the canonical model, stated directly in
the intrinsic route so no coordinate-PDE bridge enters the theorem chain. -/
theorem initial_abs_curvature_le_of_canonical_model_distance
    {p q model : Data} {g gu theta kappa : ℝ → ℝ → ℝ}
    {c0 k0 d0 c C kmin delta A0 r : ℝ}
    (Gamma : NormalPath p q)
    (hmodel : IsTubeMember c0 k0 d0 model)
    (hp : IsVariableTubeMember c C kmin delta p)
    (hloc : 0 < c0 - r)
    (hmodelAcc : ∀ u, ‖model.2.2 u‖ ≤ A0)
    (hdist : dist model p ≤ r)
    (hg_nonneg : ∀ u, 0 ≤ g 0 u)
    (hXu : ∀ u, HasDerivAt (Gamma.X 0)
      ((g 0 u : ℂ) * Complex.exp (Complex.I * (theta 0 u : ℂ))) u)
    (hgu : ∀ u, HasDerivAt (g 0) (gu 0 u) u)
    (hthetau : ∀ u, HasDerivAt (theta 0) (g 0 u * kappa 0 u) u) :
    ∀ u, |kappa 0 u| ≤ (A0 + r) / (c0 - r) ^ 2 := by
  exact
    ReachableVariableSpeedFrontCurvature.initial_abs_curvature_le_of_model_distance
      Gamma (variableTube_with_model_distance_speed_floor hmodel hp hdist) hloc
      hmodelAcc hdist hg_nonneg hXu hgu hthetau

/-- Tangential velocity in the successor front's intrinsic arclength. -/
def tangentialRate (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ℝ → ℝ → ℝ :=
  frameTangential A.Ydot (angle A)

/-- Normal velocity in the successor front's intrinsic arclength. -/
def normalRate (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ℝ → ℝ → ℝ :=
  frameNormal A.Ydot (angle A)

/-- The inverse-Jacobi source in intrinsic rear arclength. -/
def jacobiSource (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ℝ → ℝ → ℝ := fun t x =>
  A.etaF t (A.sf t x) / Real.cos (A.delta t (A.sf t x))

/-- First intrinsic arclength derivative of the successor normal velocity. -/
def normalRateS (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ℝ → ℝ → ℝ := fun t x => jacobiSource A t x - normalRate A t x

/-- Second intrinsic arclength derivative of the successor normal velocity. -/
def normalRateSS (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ℝ → ℝ → ℝ := fun t x => A.gS t x - normalRateS A t x

/-- First intrinsic arclength derivative of successor curvature. -/
def curvatureX (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    ℝ → ℝ → ℝ := fun t x =>
  (A.K t (A.sf t x) - Real.sin (A.delta t (A.sf t x))) /
    Real.cos (A.delta t (A.sf t x)) ^ 3

/-- The physical second-arclength operator in a variable-speed coordinate. -/
def arclengthSecond (speed speed1 field1 field2 : ℝ) : ℝ :=
  field2 / speed ^ 2 - speed1 * field1 / speed ^ 3

theorem normalRate_hasDerivAt
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t x : ℝ) :
    HasDerivAt (normalRate A t) (normalRateS A t x) x := by
  simpa [normalRate, normalRateS, jacobiSource, angle] using A.jacobi t x

theorem normalRateS_hasDerivAt
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t x : ℝ) :
    HasDerivAt (normalRateS A t) (normalRateSS A t x) x := by
  simpa [normalRate, normalRateS, normalRateSS, jacobiSource, angle] using
    (A.gS_deriv t x).sub (A.jacobi t x)

theorem curvature_hasDerivAt_space
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t x : ℝ) :
    HasDerivAt (curvature A t) (curvatureX A t x) x := by
  simpa [curvature, curvatureX] using
    RearOwnTangential.hasDerivAt_rearCurv_space A.steering A.sf_deriv
      A.cos_ne_zero t x

theorem tangentialRate_hasDerivAt
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t x : ℝ) :
    HasDerivAt (tangentialRate A t)
      (curvature A t x * normalRate A t x) x := by
  simpa [tangentialRate, normalRate, angle, curvature, mul_comm] using
    (RearOwnFrameSpatialC2OfMixed.hasDerivAt_frameTangential_of_mixed
      (MarkingAwareSource.successorFrontCore A).angle_frenet
      A.rear_angle_time_deriv A.mixed_derivative t x)

/-- The angle evolution in genuine successor arclength. -/
theorem intrinsic_angleRate_eq
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t x : ℝ) :
    A.alphaT t x = normalRateS A t x +
      curvature A t x * tangentialRate A t x := by
  obtain ⟨Z, hZt, hZx⟩ := A.mixed_derivative t x
  exact GaugeFrameTimeBounds.angleRate_eq t x
    ((MarkingAwareSource.successorFrontCore A).angle_frenet t)
    (normalRate_hasDerivAt A t)
    (tangentialRate_hasDerivAt A t)
    (A.rear_angle_time_deriv t x) hZt (by
      simpa [tangentialRate, normalRate, angle] using hZx)

/-- The retained source fields satisfy the genuine intrinsic curvature
evolution, including tangential advection. -/
theorem intrinsic_curvRate_eq
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t x : ℝ) :
    A.kT t x = normalRateSS A t x +
      curvature A t x ^ 2 * normalRate A t x +
      tangentialRate A t x * curvatureX A t x := by
  exact GaugeFrameTimeBounds.curvRate_eq t x
    (fun y => intrinsic_angleRate_eq A t y)
    (normalRateS_hasDerivAt A t)
    (curvature_hasDerivAt_space A t)
    (tangentialRate_hasDerivAt A t)
    (A.rear_angle_time_spatial t x)

/-- Curvature read along the chosen gauge flow. -/
def chosenCurvature
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (E : Applied Gamma A) : ℝ → ℝ → ℝ :=
  fun t u => curvature A t (E.Phi t u)

/-- The chosen flow cancels the tangential-advection term.  This is the
correct replacement for the false raw-coordinate `eta_uu` evolution. -/
theorem chosenCurvature_hasDerivAt
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (E : Applied Gamma A) (t u : ℝ) :
    HasDerivAt (fun r => chosenCurvature A E r u)
      (normalRateSS A t (E.Phi t u) +
        chosenCurvature A E t u ^ 2 * normalRate A t (E.Phi t u)) t := by
  have hdiff : Differentiable ℝ (uncurry (curvature A)) :=
    A.rear_curvature_contDiff.differentiable (by norm_num)
  have hchain := SelInvFrontJacobiC2.hasDerivAt_comp_partials hdiff (E.flow u t)
  have hpt : partialTime (curvature A) t (E.Phi t u) =
      A.kT t (E.Phi t u) :=
    (hasDerivAt_partialTime hdiff t (E.Phi t u)).unique (by
      simpa [curvature] using A.rear_curvature_time_deriv t (E.Phi t u))
  have hpx : partialArc (curvature A) t (E.Phi t u) =
      curvatureX A t (E.Phi t u) :=
    (hasDerivAt_partialArc hdiff t (E.Phi t u)).unique
      (curvature_hasDerivAt_space A t (E.Phi t u))
  rw [hpt, hpx] at hchain
  convert hchain using 1
  rw [intrinsic_curvRate_eq A t (E.Phi t u)]
  simp [chosenCurvature, tangentialRate, angle]

private theorem normalRateSS_continuous_of_spatial
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (N : RearOwnFrameDrift.SpatialC2 (normalRate A)) :
    Continuous (uncurry (normalRateSS A)) := by
  have h1 : N.xi1 = normalRateS A := by
    funext t x
    exact (N.deriv1 t x).unique (normalRate_hasDerivAt A t x)
  have h2 : N.xi2 = normalRateSS A := by
    funext t x
    have hderiv : HasDerivAt (normalRateS A t) (N.xi2 t x) x := by
      simpa only [h1] using N.deriv2 t x
    exact hderiv.unique (normalRateS_hasDerivAt A t x)
  simpa only [h2] using N.continuous2

theorem normalRate_continuous
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    Continuous (uncurry (normalRate A)) := by
  cases A.frame_regularity with
  | spatial R => exact R.normal.continuous0
  | joint hY hangle =>
      exact (RearOwnTangential.contDiff_frameNormal hY hangle).continuous

theorem normalRateSS_continuous
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) :
    Continuous (uncurry (normalRateSS A)) := by
  cases A.frame_regularity with
  | spatial R => exact normalRateSS_continuous_of_spatial A R.normal
  | joint hY hangle =>
      let N := RearOwnFrameDrift.SpatialC2.ofContDiff
        (RearOwnTangential.contDiff_frameNormal hY hangle)
      exact normalRateSS_continuous_of_spatial A N

theorem chosenCurvature_rhs_intervalIntegrable
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (E : Applied Gamma A) (u : ℝ) :
    IntervalIntegrable
      (fun t => normalRateSS A t (E.Phi t u) +
        chosenCurvature A E t u ^ 2 * normalRate A t (E.Phi t u))
      volume 0 1 := by
  have hPhi : Continuous (fun t => E.Phi t u) :=
    continuous_iff_continuousAt.2 fun t => (E.flow u t).continuousAt
  have hpair : Continuous (fun t => (t, E.Phi t u)) :=
    continuous_id.prodMk hPhi
  have hss := (normalRateSS_continuous A).comp hpair
  have heta := (normalRate_continuous A).comp hpair
  have hk := A.rear_curvature_contDiff.continuous.comp hpair
  exact (hss.add ((hk.pow 2).mul heta)).intervalIntegrable 0 1

/-- The normal velocity is bounded by the retained intrinsic source density. -/
theorem abs_normalRate_le_density
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t x : ℝ) :
    |normalRate A t x| ≤ A.m t := by
  have hperiod : ∀ r, Function.Periodic (normalRate A r) (rearPeriod A r) := by
    intro r
    simpa [normalRate, angle] using
      (RearOwnDriftFundamental.periodic_frameNormal_rearOwn
        A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
        A.cos_ne_zero A.front_frenet A.angle_frenet A.steering A.sf_deriv
        A.sf_rightInverse A.steering_periodic A.front_periodic A.angle_periodic
        A.front_contDiff A.angle_contDiff A.steering_contDiff A.sf_contDiff
        A.period_contDiff A.rear_time_deriv r)
  exact (RearOwnTangentialCost.abs_frameNormal_le_slice
    A.kh_nonnegative A.kh_lt_one A.strip_nonnegative A.strip_le
    A.rear_period_pos hperiod A.jacobi A.etaF_bound t x).trans
      (A.density_domination t)

theorem abs_jacobiSource_le_density
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t x : ℝ) :
    |jacobiSource A t x| ≤ A.m t := by
  exact (RearOwnTangential.abs_div_cos_le_strip
    A.kh_nonnegative A.kh_lt_one
    (A.strip_nonnegative t (A.sf t x)) (A.strip_le t (A.sf t x))
    (A.etaF_bound t (A.sf t x))).trans (A.density_domination t)

theorem abs_normalRateS_le_density
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t x : ℝ) :
    |normalRateS A t x| ≤ 2 * A.m t := by
  calc
    |normalRateS A t x| ≤ |jacobiSource A t x| + |normalRate A t x| := by
      simpa [normalRateS] using abs_sub (jacobiSource A t x) (normalRate A t x)
    _ ≤ A.m t + A.m t :=
      add_le_add (abs_jacobiSource_le_density A t x)
        (abs_normalRate_le_density A t x)
    _ = 2 * A.m t := by ring

theorem abs_normalRateSS_le_density
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) (t x : ℝ) :
    |normalRateSS A t x| ≤ (A.d + 2) * A.m t := by
  calc
    |normalRateSS A t x| ≤ |A.gS t x| + |normalRateS A t x| := by
      simpa [normalRateSS] using abs_sub (A.gS t x) (normalRateS A t x)
    _ ≤ A.d * A.m t + 2 * A.m t :=
      add_le_add ((A.gS_bound t x).trans (A.Dd_le t))
        (abs_normalRateS_le_density A t x)
    _ = (A.d + 2) * A.m t := by ring

/-- The concrete chosen path recovers the intrinsic second derivative from
the coordinate jets with both variable-speed correction factors present. -/
theorem chosenPath_arclengthSecond_eq
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (E : Applied Gamma A) (W : ChosenPath Gamma A E.Phi a b)
    (t u : ℝ) :
    arclengthSecond (W.phi1 t u) (W.phi2 t u)
      (W.c2.eta1 t u) (W.c2.eta2 t u) =
        normalRateSS A t (E.Phi t u) := by
  have heta1Deriv : HasDerivAt (W.Delta.eta t)
      (normalRateS A t (E.Phi t u) * W.phi1 t u) u := by
    rw [funext (W.eta_eq t)]
    exact (normalRate_hasDerivAt A t (E.Phi t u)).comp u
      (W.phi1_deriv t u)
  have heta1 : W.c2.eta1 t u =
      normalRateS A t (E.Phi t u) * W.phi1 t u :=
    (W.c2.eta_deriv t u).unique heta1Deriv
  have heta1Fun : W.c2.eta1 t = fun v =>
      normalRateS A t (E.Phi t v) * W.phi1 t v := by
    funext v
    apply (W.c2.eta_deriv t v).unique
    rw [funext (W.eta_eq t)]
    exact (normalRate_hasDerivAt A t (E.Phi t v)).comp v
      (W.phi1_deriv t v)
  have heta2Deriv : HasDerivAt
      (fun v => normalRateS A t (E.Phi t v) * W.phi1 t v)
      (normalRateSS A t (E.Phi t u) * W.phi1 t u ^ 2 +
        normalRateS A t (E.Phi t u) * W.phi2 t u) u := by
    convert ((normalRateS_hasDerivAt A t (E.Phi t u)).comp u
      (W.phi1_deriv t u)).mul (W.phi2_deriv t u) using 1 <;>
        simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  have heta2 : W.c2.eta2 t u =
      normalRateSS A t (E.Phi t u) * W.phi1 t u ^ 2 +
        normalRateS A t (E.Phi t u) * W.phi2 t u := by
    have h := W.c2.eta1_deriv t u
    rw [heta1Fun] at h
    exact h.unique heta2Deriv
  have hspeed : 0 < W.phi1 t u :=
    (mul_pos (A.rear_period_pos 0) (Real.exp_pos _)).trans_le
      (W.phi1_lower t u)
  rw [arclengthSecond, heta1, heta2]
  field_simp [hspeed.ne']
  ring

/-- The stopped-curvature theorem with the genuine intrinsic forcing.  Its
smallness condition is intentionally stated with the exact source mass; this
is the condition a concrete closing package must provide. -/
theorem chosenCurvature_lt_of_intrinsic_mass
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (E : Applied Gamma A) {kb ke : ℝ}
    (hinit : ∀ u, chosenCurvature A E 0 u ≤ kb)
    (hsmall : ((A.d + 2) + ke ^ 2) *
      (∫ t in (0 : ℝ)..1, A.m t) < ke - kb) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, chosenCurvature A E t u < ke := by
  have hmInt : IntervalIntegrable A.m volume 0 1 :=
    A.density_continuous.intervalIntegrable 0 1
  have hm2Int : IntervalIntegrable (fun t => (A.d + 2) * A.m t)
      volume 0 1 := by
    simpa only [smul_eq_mul] using hmInt.const_mul (A.d + 2)
  apply StoppedCurvature.stopped_curvature_path
    (kappa := chosenCurvature A E)
    (eta := fun t u => normalRate A t (E.Phi t u))
    (etass := fun t u => normalRateSS A t (E.Phi t u))
    (m0 := A.m) (m2 := fun t => (A.d + 2) * A.m t)
    (S0 := ∫ t in (0 : ℝ)..1, A.m t)
    (S2 := (A.d + 2) * (∫ t in (0 : ℝ)..1, A.m t))
    (ke := ke) (kb := kb)
    (chosenCurvature_hasDerivAt A E)
    (chosenCurvature_rhs_intervalIntegrable A E)
    (fun t u => abs_normalRate_le_density A t (E.Phi t u))
    (fun t u => abs_normalRateSS_le_density A t (E.Phi t u))
    hmInt hm2Int rfl (by rw [intervalIntegral.integral_const_mul])
    (fun t u => (MarkingAwareSource.successorFrontCore A).curvature_nonnegative
      t (E.Phi t u)) hinit (by
        convert hsmall using 1 <;> ring)

theorem chosenMarking_surjective
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (E : Applied Gamma A) (W : ChosenPath Gamma A E.Phi a b) (t : ℝ) :
    Surjective (E.Phi t) := by
  have hcont : Continuous (E.Phi t) :=
    continuous_iff_continuousAt.2 fun u => (W.phi1_deriv t u).continuousAt
  exact surjective_of_continuous_quasiPeriodic (A.rear_period_pos t) hcont
    (W.shift t)

/-- Active-window intrinsic curvature bound, with no coordinate-PDE
assumption. -/
theorem active_intrinsic_abs_curvature_lt_of_intrinsic_mass
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (E : Applied Gamma A) (W : ChosenPath Gamma A E.Phi a b)
    {kb ke : ℝ}
    (hinit : ∀ u, chosenCurvature A E 0 u ≤ kb)
    (hsmall : ((A.d + 2) + ke ^ 2) *
      (∫ t in (0 : ℝ)..1, A.m t) < ke - kb)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ s, |curvature A t s| < ke := by
  have hchosen := chosenCurvature_lt_of_intrinsic_mass A E hinit hsmall t ht
  intro s
  obtain ⟨u, hu⟩ := chosenMarking_surjective A E W t s
  rw [← hu, abs_of_nonneg
    ((MarkingAwareSource.successorFrontCore A).curvature_nonnegative
      t (E.Phi t u))]
  exact hchosen u

/-- Canonical-model initial control followed by the corrected intrinsic
stability theorem.  The only remaining scalar premise is the weighted source
mass inequality displayed explicitly in `hsmall`. -/
theorem active_intrinsic_abs_curvature_lt_sourceKh_of_canonicalModel
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (E : Applied Gamma A) (W : ChosenPath Gamma A E.Phi a b)
    {c0 k0 d0 c C kmin delta A0 r : ℝ}
    (hmodel : IsTubeMember c0 k0 d0 model)
    (hp : IsVariableTubeMember c C kmin delta a)
    (hloc : 0 < c0 - r)
    (hmodelAcc : ∀ u, ‖model.2.2 u‖ ≤ A0)
    (hdist : dist model a ≤ r)
    (hinitial : (A0 + r) / (c0 - r) ^ 2 ≤ TubeConstants.kbar (1 / 2))
    (hsmall : ((A.d + 2) +
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh ^ 2) *
      (∫ t in (0 : ℝ)..1, A.m t) <
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh -
          TubeConstants.kbar (1 / 2))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ s, |curvature A t s| <
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh := by
  let core := MarkingAwareSource.successorFrontCore A
  have hg_nonneg : ∀ u, 0 ≤ W.phi1 0 u := by
    intro u
    exact ((mul_pos (core.period_pos 0) (Real.exp_pos _)).trans_le
      (W.phi1_lower 0 u)).le
  have hXu : ∀ u, HasDerivAt (W.Delta.X 0)
      ((W.phi1 0 u : ℂ) * Complex.exp
        (Complex.I * (angle A 0 (E.Phi 0 u) : ℂ))) u := by
    intro u
    have h := (core.front_frenet 0 (E.Phi 0 u)).scomp u
      (W.phi1_deriv 0 u)
    have hDX : W.Delta.X 0 = fun v => front A 0 (E.Phi 0 v) :=
      funext (W.position_eq 0)
    rw [hDX]
    simpa [Function.comp_def, Complex.real_smul] using h
  have htheta : ∀ u, HasDerivAt
      (fun v => angle A 0 (E.Phi 0 v))
      (W.phi1 0 u * chosenCurvature A E 0 u) u := by
    intro u
    have h := (core.angle_frenet 0 (E.Phi 0 u)).comp u
      (W.phi1_deriv 0 u)
    simpa [chosenCurvature, mul_comm] using h
  have hinitAbs :=
    initial_abs_curvature_le_of_canonical_model_distance
        (g := W.phi1) (gu := W.phi2)
        (theta := fun t u => angle A t (E.Phi t u))
        (kappa := chosenCurvature A E) W.Delta hmodel hp hloc hmodelAcc hdist
        hg_nonneg hXu (W.phi2_deriv 0) htheta
  apply active_intrinsic_abs_curvature_lt_of_intrinsic_mass A E W
    (kb := TubeConstants.kbar (1 / 2)) (ke :=
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)
    (fun u => (le_abs_self _).trans ((hinitAbs u).trans hinitial)) hsmall ht

end ReachableVariableSpeedFrontCurvatureIntrinsicStable
