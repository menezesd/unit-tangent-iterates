import Mathlib
import UnitTangentIterates.InterpolationSecondOrder
import UnitTangentIterates.JointC1
import UnitTangentIterates.NormalGaugeFrame
import UnitTangentIterates.GaugeFlowPeriodic

/-!
# The curvature-interpolation path in normal gauge

`InterpolationEstimate.lean` produces the path of curves `X_t` of the lemma
*Curvature interpolation* and bounds its Frenet velocities: the motion is

`∂_t X_t = ξ_t τ_t + η_t ν_t` ,

with a tangential component `ξ_t` which the path metric of `PathMetric.lean`
does not allow — a normal path must move along its unit normal only, and its
slices must be parametrized with period one.

This file removes the tangential component.  Reparametrizing by the flow of the
tangential rate `−ξ` (the curves are unit speed, so the speed does not appear)
turns the motion into `η ν` (`NormalGauge.lean`,
`NormalGaugeFrame.lean`), provided the flow exists.  Existence needs the rate to
be bounded and globally Lipschitz in the arclength *uniformly in the time*,
which the interpolation does not satisfy for `t` far outside `[0,1]`: the
interpolated curvature `κ_t = (1-t)κ⁰ + tκ¹` grows linearly there.  The rate is
therefore cut off in the time by a continuous factor equal to `1` on `[0,1]`
and vanishing outside `[-1,2]` (`timeCut`); this changes nothing on the time
interval of the path, where the flow still solves `∂_tΦ = −ξ_t(Φ)`.

Since `ξ_t` is `L`-periodic in the arclength (`InterpolationEstimate.lean`),
the flow commutes with the translation by the period `2L`
(`GaugeFlowPeriodic.lean`), so the gauge parameter is *normalized*: every
reparametrized slice `u ↦ X_t(Φ(t,u))` has period one.

Main results:

* `timeCut` and its elementary properties;
* `abs_gaugeFieldDeriv_le`, `lipschitzWith_gaugeField`, `abs_gaugeField_le`,
  `periodic_gaugeField` : the cut-off rate is bounded, globally Lipschitz and
  `2L`-periodic in the arclength;
* `contDiff_one_interpCurve` : the interpolation is jointly `C¹`;
* `exists_interpolation_gauge_flow` : the gauge flow exists, starts at
  `Φ(0,u) = 2Lu`, satisfies `Φ(t, u+1) = Φ(t,u) + 2L`, so that each
  reparametrized slice has period one, and the reparametrized path moves with
  the purely normal velocity `η ν` at every time of `[0,1]`;
* `exists_interpolation_gauge_flow_instance` : the hypotheses are not vacuous.
-/

noncomputable section

open Set Function MeasureTheory

namespace InterpolationGauge

open CurvatureInterpolation InterpolationNormal InterpolationEstimate
  InterpolationSecondOrder

variable {k0 k1 : ℝ → ℝ} {θ₀ L : ℝ}

/-! ### The cut-off in the time -/

/-- The continuous cut-off in the time: it equals `1` on `[0,1]`, vanishes
outside `[-1,2]` and takes values in `[0,1]`. -/
def timeCut (t : ℝ) : ℝ := max 0 (min 1 (min (t + 1) (2 - t)))

theorem continuous_timeCut : Continuous timeCut := by
  unfold timeCut
  fun_prop

theorem timeCut_nonneg (t : ℝ) : 0 ≤ timeCut t := le_max_left _ _

theorem timeCut_le_one (t : ℝ) : timeCut t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem timeCut_eq_one {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : timeCut t = 1 := by
  have h1 : (1:ℝ) ≤ min (t + 1) (2 - t) :=
    le_min (by linarith [ht.1]) (by linarith [ht.2])
  simp [timeCut, min_eq_left h1]

theorem timeCut_eq_zero_of_lt {t : ℝ} (ht : t < -1) : timeCut t = 0 := by
  have h : min 1 (min (t + 1) (2 - t)) ≤ 0 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (by linarith))
  simp [timeCut, max_eq_left h]

theorem timeCut_eq_zero_of_gt {t : ℝ} (ht : 2 < t) : timeCut t = 0 := by
  have h : min 1 (min (t + 1) (2 - t)) ≤ 0 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (by linarith))
  simp [timeCut, max_eq_left h]

/-! ### The cut-off tangential rate -/

/-- **The gauge field**: the tangential rate `−ξ_t` of the interpolation path
(the curves are unit speed), cut off in the time. -/
def gaugeField (k0 k1 : ℝ → ℝ) (θ₀ L : ℝ) (t s : ℝ) : ℝ :=
  -(timeCut t * tangentVel k0 k1 θ₀ L t s)

theorem hasDerivAt_gaugeField (hk0 : Continuous k0) (hk1 : Continuous k1) (t s : ℝ) :
    HasDerivAt (gaugeField k0 k1 θ₀ L t)
      (-(timeCut t * (kappaInterp k0 k1 t s * normalVel k0 k1 θ₀ L t s))) s :=
  (((hasDerivAt_tangentVel (θ₀ := θ₀) (L := L) hk0 hk1 t s).const_mul
    (timeCut t))).neg

section Bounds

variable (hk0 : Continuous k0) (hk1 : Continuous k1)
  (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
  (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
  (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)

include hk0 hk1 hper0 hper1 htot0 htot1 hL

/-- The gauge field is bounded by `(3/2)Lε`. -/
theorem abs_gaugeField_le (t s : ℝ) :
    |gaugeField k0 k1 θ₀ L t s| ≤ (3/2) * L * curvDist k0 k1 L := by
  have hxi := abs_tangentVel_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL t s
  have hcut : |timeCut t| ≤ 1 := by
    rw [abs_of_nonneg (timeCut_nonneg t)]
    exact timeCut_le_one t
  have heps : 0 ≤ (3/2) * L * curvDist k0 k1 L :=
    le_trans (abs_nonneg _) hxi
  calc |gaugeField k0 k1 θ₀ L t s|
      = |timeCut t| * |tangentVel k0 k1 θ₀ L t s| := by
        rw [gaugeField, abs_neg, abs_mul]
    _ ≤ 1 * ((3/2) * L * curvDist k0 k1 L) := by
        exact mul_le_mul hcut hxi (abs_nonneg _) zero_le_one
    _ = (3/2) * L * curvDist k0 k1 L := one_mul _

/-- **The arclength derivative of the gauge field is bounded**, uniformly in
the time: the cut-off keeps the interpolated curvature bounded by `4κ_*`. -/
theorem abs_gaugeFieldDeriv_le {kstar : ℝ} (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) (t s : ℝ) :
    |(-(timeCut t * (kappaInterp k0 k1 t s * normalVel k0 k1 θ₀ L t s)))|
      ≤ 4 * kstar * ((3/2) * L * curvDist k0 k1 L) := by
  have heta := abs_normalVel_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL t s
  have heps : 0 ≤ (3/2) * L * curvDist k0 k1 L := le_trans (abs_nonneg _) heta
  have hkstar : 0 ≤ kstar := le_trans (hk0nn 0) (hk0le 0)
  have hbound : 0 ≤ 4 * kstar * ((3/2) * L * curvDist k0 k1 L) := by positivity
  rcases lt_or_ge t (-1) with ht | ht
  · rw [timeCut_eq_zero_of_lt ht]
    simpa using hbound
  rcases lt_or_ge 2 t with ht' | ht'
  · rw [timeCut_eq_zero_of_gt ht']
    simpa using hbound
  -- on the support of the cut-off the interpolated curvature is at most `4κ_*`
  have hkap : |kappaInterp k0 k1 t s| ≤ 4 * kstar := by
    have h1t : |1 - t| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    have hts : |t| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    have h0 : |(1 - t) * k0 s| ≤ 2 * kstar := by
      rw [abs_mul, abs_of_nonneg (hk0nn s)]
      exact mul_le_mul h1t (hk0le s) (hk0nn s) (by norm_num)
    have h1 : |t * k1 s| ≤ 2 * kstar := by
      rw [abs_mul, abs_of_nonneg (hk1nn s)]
      exact mul_le_mul hts (hk1le s) (hk1nn s) (by norm_num)
    calc |kappaInterp k0 k1 t s| ≤ |(1 - t) * k0 s| + |t * k1 s| := by
          simpa [kappaInterp] using abs_add_le ((1 - t) * k0 s) (t * k1 s)
      _ ≤ 2 * kstar + 2 * kstar := add_le_add h0 h1
      _ = 4 * kstar := by ring
  have hcut : |timeCut t| ≤ 1 := by
    rw [abs_of_nonneg (timeCut_nonneg t)]
    exact timeCut_le_one t
  calc |(-(timeCut t * (kappaInterp k0 k1 t s * normalVel k0 k1 θ₀ L t s)))|
      = |timeCut t| * (|kappaInterp k0 k1 t s| * |normalVel k0 k1 θ₀ L t s|) := by
        rw [abs_neg, abs_mul, abs_mul]
    _ ≤ 1 * ((4 * kstar) * ((3/2) * L * curvDist k0 k1 L)) := by
        refine mul_le_mul hcut ?_ (by positivity) zero_le_one
        exact mul_le_mul hkap heta (abs_nonneg _) (by positivity)
    _ = 4 * kstar * ((3/2) * L * curvDist k0 k1 L) := one_mul _

/-- **The gauge field is globally Lipschitz in the arclength**, uniformly in
the time. -/
theorem lipschitzWith_gaugeField {kstar : ℝ} (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) (t : ℝ) :
    LipschitzWith (Real.toNNReal (4 * kstar * ((3/2) * L * curvDist k0 k1 L)))
      (gaugeField k0 k1 θ₀ L t) := by
  have hnn : 0 ≤ 4 * kstar * ((3/2) * L * curvDist k0 k1 L) :=
    le_trans (abs_nonneg _)
      (abs_gaugeFieldDeriv_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL
        hk0nn hk1nn hk0le hk1le t 0)
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_gaugeField (θ₀ := θ₀) (L := L) hk0 hk1 t x).differentiableAt)
    (fun x => ?_)
  rw [(hasDerivAt_gaugeField (θ₀ := θ₀) (L := L) hk0 hk1 t x).deriv,
    ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hnn, Real.norm_eq_abs]
  exact abs_gaugeFieldDeriv_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL
    hk0nn hk1nn hk0le hk1le t x

omit hL in
/-- The gauge field is `2L`-periodic in the arclength. -/
theorem periodic_gaugeField (t : ℝ) :
    Function.Periodic (gaugeField k0 k1 θ₀ L t) (2 * L) := by
  have hper := tangentVel_periodic (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 t
  intro s
  simp only [gaugeField]
  rw [show s + 2 * L = s + L + L by ring, hper (s + L), hper s]

end Bounds

/-! ### Joint regularity of the interpolation -/

/-- The interpolation is jointly `C¹` in the time and the arclength. -/
theorem contDiff_one_interpCurve (hk0 : Continuous k0) (hk1 : Continuous k1) :
    ContDiff ℝ 1 (uncurry fun t s => interpCurve (kappaInterp k0 k1 t) θ₀ L s) := by
  refine JointC1.contDiff_one_of_continuous_partials
    (f1 := fun t s => interpVelocity k0 k1 θ₀ L t s)
    (f2 := fun t s => tau (tangentAngle (kappaInterp k0 k1 t) θ₀ s))
    (fun t s => hasDerivAt_interpCurve_param (θ₀ := θ₀) (L := L) hk0 hk1 s t)
    (fun t s => hasDerivAt_interpCurve (continuous_kappaInterp hk0 hk1) s)
    (continuous_uncurry_interpVelocity (θ₀ := θ₀) (L := L) hk0 hk1)
    (continuous_tau.comp (continuous_uncurry_tangentAngle (θ₀ := θ₀) hk0 hk1))

/-- The interpolation is unit speed, in the shape the normal-gauge lemma
asks. -/
theorem hasDerivAt_interpCurve_space (hk0 : Continuous k0) (hk1 : Continuous k1) (t s : ℝ) :
    HasDerivAt (fun x => interpCurve (kappaInterp k0 k1 t) θ₀ L x)
      (((1 : ℝ) : ℂ)
        * Complex.exp (Complex.I * (tangentAngle (kappaInterp k0 k1 t) θ₀ s : ℂ))) s := by
  have h := hasDerivAt_interpCurve (θ₀ := θ₀) (L := L)
    (continuous_kappaInterp hk0 hk1) (kappa := kappaInterp k0 k1 t) s
  simpa [tau, mul_comm] using h

/-- The velocity of the interpolation, in the frame shape `(ξ + iη)e^{iψ}`. -/
theorem hasDerivAt_interpCurve_time (hk0 : Continuous k0) (hk1 : Continuous k1) (t s : ℝ) :
    HasDerivAt (fun r => interpCurve (kappaInterp k0 k1 r) θ₀ L s)
      (((tangentVel k0 k1 θ₀ L t s : ℂ)
          + Complex.I * (normalVel k0 k1 θ₀ L t s : ℂ))
        * Complex.exp (Complex.I * (tangentAngle (kappaInterp k0 k1 t) θ₀ s : ℂ))) t := by
  have h := hasDerivAt_interpCurve_param (θ₀ := θ₀) (L := L) hk0 hk1 s t
  convert h using 1
  set z := interpVelocity k0 k1 θ₀ L t s with hzdef
  set ang := tangentAngle (kappaInterp k0 k1 t) θ₀ s with hangdef
  rw [show Complex.exp (Complex.I * (ang : ℂ)) = tau ang by simp [tau, mul_comm]]
  show ((tangentComp z ang : ℂ) + Complex.I * (normalComp z ang : ℂ)) * tau ang = z
  conv_rhs => rw [frame_decomp z ang]
  ring

/-! ### The gauge flow -/

section Flow

variable (hk0 : Continuous k0) (hk1 : Continuous k1)
  (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
  (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
  (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)

include hk0 hk1 hper0 hper1 htot0 htot1 hL

set_option maxHeartbeats 400000 in
/-- **The curvature-interpolation path in normal gauge.**

The tangential rate of the interpolating path, cut off in the time, has a
global flow `Φ` started at `Φ(0,u) = 2Lu`.  Because the rate is `2L`-periodic in
the arclength, `Φ(t, u+1) = Φ(t,u) + 2L`, so every reparametrized slice
`u ↦ X_t(Φ(t,u))` is a closed curve of period one in the gauge parameter — the
normalized parameter of the path metric.  On the time interval `[0,1]` of the
path the cut-off is inactive, so the flow solves `∂_tΦ = −ξ_t(Φ)` there and the
reparametrized path moves with the purely normal velocity `η_t ν_t`. -/
theorem exists_interpolation_gauge_flow {kstar : ℝ}
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = 2 * L * u) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u) (gaugeField k0 k1 θ₀ L t (Phi t u)) t) ∧
      (∀ t u, Phi t (u + 1) = Phi t u + 2 * L) ∧
      (∀ t, Continuous fun u => Phi t u) ∧
      (∀ t, Function.Periodic
        (fun u => interpCurve (kappaInterp k0 k1 t) θ₀ L (Phi t u)) 1) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ u,
        HasDerivAt (fun r => interpCurve (kappaInterp k0 k1 r) θ₀ L (Phi r u))
          ((normalVel k0 k1 θ₀ L t (Phi t u) : ℂ)
            * NormalGaugeFrame.frameNormalVector
                (tangentAngle (kappaInterp k0 k1 t) θ₀ (Phi t u))) t) := by
  set K : NNReal := Real.toNNReal (4 * kstar * ((3/2) * L * curvDist k0 k1 L)) with hK
  set M : NNReal := Real.toNNReal ((3/2) * L * curvDist k0 k1 L) with hM
  have hlip : ∀ t, LipschitzWith K (gaugeField k0 k1 θ₀ L t) := fun t =>
    lipschitzWith_gaugeField (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL
      hk0nn hk1nn hk0le hk1le t
  have hbd : ∀ t s, |gaugeField k0 k1 θ₀ L t s| ≤ (M : ℝ) := by
    intro t s
    have h := abs_gaugeField_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL t s
    have hnn : 0 ≤ (3/2) * L * curvDist k0 k1 L := le_trans (abs_nonneg _) h
    rwa [hM, Real.coe_toNNReal _ hnn]
  have hcont : ∀ s, Continuous fun t => gaugeField k0 k1 θ₀ L t s := by
    intro s
    have hpair : Continuous fun t : ℝ => ((t, s) : ℝ × ℝ) :=
      continuous_id.prodMk continuous_const
    have hxi : Continuous fun t => tangentVel k0 k1 θ₀ L t s := by
      have h := (continuous_uncurry_tangentVel (θ₀ := θ₀) (L := L) hk0 hk1).comp hpair
      simpa [Function.comp_def] using h
    exact (continuous_timeCut.mul hxi).neg
  -- one flow for each value of the normalized parameter
  have hex : ∀ u : ℝ, ∃ φ : ℝ → ℝ, φ 0 = 2 * L * u ∧
      ∀ t, HasDerivAt φ (gaugeField k0 k1 θ₀ L t (φ t)) t := fun u =>
    GlobalODE.exists_global_solution_real (h := gaugeField k0 k1 θ₀ L)
      hlip hcont hbd 0 (2 * L * u)
  choose flow hflow0 hflowd using hex
  refine ⟨fun t u => flow u t, hflow0, fun u t => hflowd u t, ?_, ?_, ?_, ?_⟩
  · -- the flow commutes with the translation by the period
    intro t u
    exact GaugeFlowPeriodic.flow_translation (K := K) (Q := 2 * L)
      hlip (periodic_gaugeField hk0 hk1 hper0 hper1 htot0 htot1)
      (fun u' t' => hflowd u' t') hflow0 u t
  · -- the flow depends continuously on the gauge parameter
    intro t
    have hC : (0:ℝ) ≤ 2 * L * Real.exp ((K : ℝ) * |t|) := by positivity
    refine (LipschitzWith.of_dist_le_mul
      (K := Real.toNNReal (2 * L * Real.exp ((K : ℝ) * |t|))) ?_).continuous
    intro u u'
    have h := GlobalODE.dist_le_of_global_solutions (f := gaugeField k0 k1 θ₀ L)
      hlip (fun r => hflowd u r) (fun r => hflowd u' r) 0 t
    rw [hflow0 u, hflow0 u'] at h
    have hdist : dist (2 * L * u) (2 * L * u') = 2 * L * dist u u' := by
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * L)]
    rw [hdist] at h
    rw [Real.coe_toNNReal _ hC]
    calc dist (flow u t) (flow u' t)
        ≤ 2 * L * dist u u' * Real.exp ((K : ℝ) * |t - 0|) := h
      _ = 2 * L * Real.exp ((K : ℝ) * |t|) * dist u u' := by rw [sub_zero]; ring
  · -- hence each reparametrized slice has period one
    intro t
    exact GaugeFlowPeriodic.periodic_comp_flow (K := K) (Q := 2 * L)
      hlip (periodic_gaugeField hk0 hk1 hper0 hper1 htot0 htot1)
      (fun u' t' => hflowd u' t') hflow0
      (fun t' => interpCurve_periodic (θ₀ := θ₀) (continuous_kappaInterp hk0 hk1)
        (periodic_kappaInterp hper0 hper1) (integral_kappaInterp hk0 hk1 htot0 htot1)) t
  · -- the normal gauge on the time interval of the path
    intro t ht u
    have hcut : timeCut t = 1 := timeCut_eq_one ht
    have hphi : HasDerivAt (fun r => flow u r)
        (-(tangentVel k0 k1 θ₀ L t (flow u t) / (1 : ℝ))) t := by
      have h := hflowd u t
      simpa [gaugeField, hcut] using h
    exact NormalGaugeFrame.hasDerivAt_normalGauge_of_frame
      (R := fun a x => interpCurve (kappaInterp k0 k1 a) θ₀ L x)
      (v := fun _ _ => (1 : ℝ)) (xi := tangentVel k0 k1 θ₀ L)
      (eta := normalVel k0 k1 θ₀ L)
      (psi := fun a x => tangentAngle (kappaInterp k0 k1 a) θ₀ x)
      (phi := fun r => flow u r) (a0 := t)
      (contDiff_one_interpCurve (θ₀ := θ₀) (L := L) hk0 hk1)
      (fun a x => hasDerivAt_interpCurve_space (θ₀ := θ₀) (L := L) hk0 hk1 a x)
      (fun a x => hasDerivAt_interpCurve_time (θ₀ := θ₀) (L := L) hk0 hk1 a x)
      one_ne_zero hphi

end Flow

/-! ### Non-vacuity -/

/-- The hypotheses of `exists_interpolation_gauge_flow` are satisfied by the
circle of curvature `1/2` and the oval of curvature `1/2 + (cos s)/4`, the two
curves of `InterpolationEstimate.lean`. -/
theorem exists_interpolation_gauge_flow_instance :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = 2 * (2 * Real.pi) * u) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (gaugeField kcirc kwave 0 (2 * Real.pi) t (Phi t u)) t) ∧
      (∀ t u, Phi t (u + 1) = Phi t u + 2 * (2 * Real.pi)) ∧
      (∀ t, Continuous fun u => Phi t u) ∧
      (∀ t, Function.Periodic
        (fun u => interpCurve (kappaInterp kcirc kwave t) 0 (2 * Real.pi) (Phi t u)) 1) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ u,
        HasDerivAt (fun r => interpCurve (kappaInterp kcirc kwave r) 0 (2 * Real.pi) (Phi r u))
          ((normalVel kcirc kwave 0 (2 * Real.pi) t (Phi t u) : ℂ)
            * NormalGaugeFrame.frameNormalVector
                (tangentAngle (kappaInterp kcirc kwave t) 0 (Phi t u))) t) :=
  exists_interpolation_gauge_flow (θ₀ := 0) (kstar := 3/4)
    continuous_kcirc continuous_kwave kcirc_periodic kwave_periodic
    kcirc_total kwave_total Real.two_pi_pos
    (fun r => (kcirc_nonneg r)) (fun r => (kwave_nonneg r))
    (fun r => kcirc_le r) (fun r => kwave_le r)

end InterpolationGauge
