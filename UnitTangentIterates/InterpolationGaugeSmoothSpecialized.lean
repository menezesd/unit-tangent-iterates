import Mathlib
import UnitTangentIterates.InterpolationGaugeSmoothFlow
import UnitTangentIterates.InterpolationGaugeCutoffSecondBound
import UnitTangentIterates.GaugeFlowPeriodic

/-! # Fully specialized smooth interpolation gauge -/

noncomputable section

open Set Function MeasureTheory FlowDerivative GaugeRate

namespace InterpolationGauge

open CurvatureInterpolation InterpolationNormal InterpolationEstimate

def interpolationSmoothC1 (kstar L eps : ℝ) : ℝ :=
  4 * kstar * ((3 / 2) * L * eps)

def interpolationSmoothC2 (kstar kd L eps : ℝ) : ℝ :=
  4 * kd * ((3 / 2) * L * eps) +
    4 * kstar * (eps + 4 * kstar * ((3 / 2) * L * eps))

/-- The smooth gauge theorem specialized completely to the curvature
interpolation. -/
theorem exists_interpolation_gauge_flow_smooth_specialized_full
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L kstar kd : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Periodic k0 L) (hper1 : Periodic k1 L)
    (htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi)
    (hL : 0 < L)
    (hd0 : ∀ s, HasDerivAt k0 (k0' s) s)
    (hd1 : ∀ s, HasDerivAt k1 (k1' s) s)
    (hk0nn : ∀ s, 0 ≤ k0 s) (hk1nn : ∀ s, 0 ≤ k1 s)
    (hk0le : ∀ s, k0 s ≤ kstar) (hk1le : ∀ s, k1 s ≤ kstar)
    (hkd0 : ∀ s, |k0' s| ≤ kd) (hkd1 : ∀ s, |k1' s| ≤ kd) :
    ∃ (Phi phi1 phi2 : ℝ → ℝ → ℝ),
      (∀ u, Phi 0 u = 2 * L * u) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (gaugeField k0 k1 theta0 L t (Phi t u)) t) ∧
      (∀ t u, Phi t (u + 1) = Phi t u + 2 * L) ∧
      (∀ t u, HasDerivAt (Phi t) (phi1 t u) u) ∧
      (∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) ∧
      (∀ t, Continuous (Phi t)) ∧
      (∀ t, Continuous (phi1 t)) ∧
      (∀ t, Continuous (phi2 t)) ∧
      (∀ t u,
        2 * L * Real.exp (-(interpolationSmoothC1 kstar L (curvDist k0 k1 L) * |t|)) ≤
          phi1 t u ∧
        phi1 t u ≤ 2 * L *
          Real.exp (interpolationSmoothC1 kstar L (curvDist k0 k1 L) * |t|)) ∧
      (∀ t u, |phi2 t u| ≤
        interpolationSmoothC2 kstar kd L (curvDist k0 k1 L) *
          (2 * L) ^ 2 * |t| *
            Real.exp (2 * interpolationSmoothC1 kstar L (curvDist k0 k1 L) * |t|)) ∧
      phi1 = flowDeriv (gaugeRate1 (interpolationXi k0 k1 theta0 L)
        (interpolationXi1 k0 k1 theta0 L) (fun _ _ => 1) (fun _ _ => 0))
          Phi (2 * L) ∧
      phi2 = GaugeFlowTimeDerivative.flowDeriv2
        (gaugeRate1 (interpolationXi k0 k1 theta0 L)
          (interpolationXi1 k0 k1 theta0 L) (fun _ _ => 1) (fun _ _ => 0))
        (gaugeRate2 (interpolationXi k0 k1 theta0 L)
          (interpolationXi1 k0 k1 theta0 L)
          (fun t s => -gaugeFieldStateSecond k0 k1 k0' k1' theta0 L t s)
          (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0)) Phi (2 * L) ∧
      Continuous (uncurry Phi) ∧
      Continuous (uncurry phi1) ∧
      Continuous (uncurry phi2) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ u,
        HasDerivAt
          (fun r => interpCurve (kappaInterp k0 k1 r) theta0 L (Phi r u))
          ((normalVel k0 k1 theta0 L t (Phi t u) : ℂ) *
            NormalGaugeFrame.frameNormalVector
              (tangentAngle (kappaInterp k0 k1 t) theta0 (Phi t u))) t) := by
  let xi2 : ℝ → ℝ → ℝ := fun t s =>
    -gaugeFieldStateSecond k0 k1 k0' k1' theta0 L t s
  have hxi2 : ∀ t s, HasDerivAt (interpolationXi1 k0 k1 theta0 L t) (xi2 t s) s := by
    intro t s
    have h := (hasDerivAt_gaugeField_stateDeriv (theta0 := theta0) (L := L)
      hk0 hk1 hd0 hd1 t s).neg
    have h' : HasDerivAt (fun x => -(-(timeCut t *
        (kappaInterp k0 k1 t x * normalVel k0 k1 theta0 L t x))))
        (-gaugeFieldStateSecond k0 k1 k0' k1' theta0 L t s) s := h
    have hfun : (fun x => -(-(timeCut t *
        (kappaInterp k0 k1 t x * normalVel k0 k1 theta0 L t x))))
        = interpolationXi1 k0 k1 theta0 L t := by
      funext x
      simp [interpolationXi1]
    rw [hfun] at h'
    exact h'
  have hxi2c : Continuous (uncurry xi2) := by
    simpa [xi2] using
      (continuous_uncurry_gaugeFieldStateSecond hk0 hk1 hk0'c hk1'c).neg
  let C1 := interpolationSmoothC1 kstar L (curvDist k0 k1 L)
  let C2 := interpolationSmoothC2 kstar kd L (curvDist k0 k1 L)
  have hC1 : 0 ≤ C1 := by
    have hkstar : 0 ≤ kstar := le_trans (hk0nn 0) (hk0le 0)
    have heps := integral_abs_sub_nonneg hk0 hk1 hL.le
    dsimp [C1, interpolationSmoothC1]
    positivity
  have hb1 : ∀ t s,
      |gaugeRate1 (interpolationXi k0 k1 theta0 L)
        (interpolationXi1 k0 k1 theta0 L)
        (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)) t s| ≤ C1 := by
    intro t s
    simpa [C1, interpolationSmoothC1, gaugeRate1, interpolationXi1] using
      abs_gaugeFieldDeriv_le (θ₀ := theta0) hk0 hk1 hper0 hper1 htot0 htot1 hL
        hk0nn hk1nn hk0le hk1le t s
  have hb2 : ∀ t s,
      |gaugeRate2 (interpolationXi k0 k1 theta0 L)
        (interpolationXi1 k0 k1 theta0 L) xi2
        (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) t s| ≤ C2 := by
    intro t s
    simpa [C2, interpolationSmoothC2, xi2, gaugeRate2] using
      abs_gaugeFieldStateSecond_le_global hk0 hk1 hper0 hper1 htot0 htot1 hL
        hk0nn hk1nn hk0le hk1le hkd0 hkd1 t s
  obtain ⟨Phi, phi1, phi2, hPhi0, hPhid, hmono, hphi1, hphi2,
      hPhic, hphi1c, hphi1bd, hphi2bd, hphi1eq, hphi2eq, hphi2c⟩ :=
    exists_interpolation_gauge_flow_spatialTwoDerivatives_full
      hk0 hk1 hxi2 hxi2c hL hC1 hb1 hb2
  have htrans : ∀ t u, Phi t (u + 1) = Phi t u + 2 * L := by
    intro t u
    exact GaugeFlowPeriodic.flow_translation
      (lipschitzWith_gaugeField (θ₀ := theta0) hk0 hk1 hper0 hper1 htot0 htot1 hL
        hk0nn hk1nn hk0le hk1le)
      (periodic_gaugeField hk0 hk1 hper0 hper1 htot0 htot1) hPhid hPhi0 u t
  have hnormal : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u,
      HasDerivAt (fun r => interpCurve (kappaInterp k0 k1 r) theta0 L (Phi r u))
        ((normalVel k0 k1 theta0 L t (Phi t u) : ℂ) *
          NormalGaugeFrame.frameNormalVector
            (tangentAngle (kappaInterp k0 k1 t) theta0 (Phi t u))) t := by
    intro t ht u
    have hphi : HasDerivAt (fun r => Phi r u)
        (-(tangentVel k0 k1 theta0 L t (Phi t u) / (1 : ℝ))) t := by
      have h := hPhid u t
      simpa [gaugeField, timeCut_eq_one ht] using h
    exact NormalGaugeFrame.hasDerivAt_normalGauge_of_frame
      (R := fun a x => interpCurve (kappaInterp k0 k1 a) theta0 L x)
      (v := fun _ _ => (1 : ℝ)) (xi := tangentVel k0 k1 theta0 L)
      (eta := normalVel k0 k1 theta0 L)
      (psi := fun a x => tangentAngle (kappaInterp k0 k1 a) theta0 x)
      (phi := fun r => Phi r u) (a0 := t)
      (contDiff_one_interpCurve (θ₀ := theta0) (L := L) hk0 hk1)
      (fun a x => hasDerivAt_interpCurve_space (θ₀ := theta0) (L := L) hk0 hk1 a x)
      (fun a x => hasDerivAt_interpCurve_time (θ₀ := theta0) (L := L) hk0 hk1 a x)
      one_ne_zero hphi
  have hlip :=
    lipschitzWith_gaugeField (θ₀ := theta0) hk0 hk1 hper0 hper1
      htot0 htot1 hL hk0nn hk1nn hk0le hk1le
  have hxi : Continuous (uncurry (interpolationXi k0 k1 theta0 L)) :=
    continuous_uncurry_interpolationXi hk0 hk1
  have hxi1 : Continuous (uncurry (interpolationXi1 k0 k1 theta0 L)) :=
    continuous_uncurry_interpolationXi1 hk0 hk1
  have hxcont : Continuous (uncurry
      (gaugeRate1 (interpolationXi k0 k1 theta0 L)
        (interpolationXi1 k0 k1 theta0 L)
        (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)))) :=
    GaugeRate.continuous_gaugeRate1 hxi hxi1 continuous_const continuous_const
      (fun _ _ => one_ne_zero)
  have hxxcont : Continuous (uncurry
      (gaugeRate2 (interpolationXi k0 k1 theta0 L)
        (interpolationXi1 k0 k1 theta0 L) xi2
        (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ))
        (fun _ _ => (0 : ℝ)))) :=
    GaugeRate.continuous_gaugeRate2 hxi hxi1 hxi2c continuous_const
      continuous_const continuous_const (fun _ _ => one_ne_zero)
  have hPhiJoint : Continuous (uncurry Phi) :=
    FlowJointContinuity.continuous_flow_prod hlip hPhid hPhi0
  have hphi1Joint : Continuous (uncurry phi1) := by
    rw [hphi1eq]
    exact FlowJointContinuity.continuous_flowDeriv_prod hlip hPhid hPhi0 hxcont
  have hphi2Joint : Continuous (uncurry phi2) := by
    rw [hphi2eq]
    exact FlowJointContinuity.continuous_flowDeriv2_prod hlip hPhid hPhi0
      hxcont hxxcont
  exact ⟨Phi, phi1, phi2, hPhi0, hPhid, htrans, hphi1, hphi2,
    hPhic, hphi1c, hphi2c, hphi1bd, hphi2bd, hphi1eq,
    by simpa [xi2] using hphi2eq, hPhiJoint, hphi1Joint, hphi2Joint, hnormal⟩

/-- Backwards-compatible projection of the specialized smooth-flow theorem. -/
theorem exists_interpolation_gauge_flow_smooth_specialized
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L kstar kd : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Periodic k0 L) (hper1 : Periodic k1 L)
    (htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi)
    (hL : 0 < L)
    (hd0 : ∀ s, HasDerivAt k0 (k0' s) s)
    (hd1 : ∀ s, HasDerivAt k1 (k1' s) s)
    (hk0nn : ∀ s, 0 ≤ k0 s) (hk1nn : ∀ s, 0 ≤ k1 s)
    (hk0le : ∀ s, k0 s ≤ kstar) (hk1le : ∀ s, k1 s ≤ kstar)
    (hkd0 : ∀ s, |k0' s| ≤ kd) (hkd1 : ∀ s, |k1' s| ≤ kd) :
    ∃ (Phi phi1 phi2 : ℝ → ℝ → ℝ),
      (∀ u, Phi 0 u = 2 * L * u) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (gaugeField k0 k1 theta0 L t (Phi t u)) t) ∧
      (∀ t u, Phi t (u + 1) = Phi t u + 2 * L) ∧
      (∀ t u, HasDerivAt (Phi t) (phi1 t u) u) ∧
      (∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) ∧
      (∀ t, Continuous (Phi t)) ∧ (∀ t, Continuous (phi1 t)) ∧
      (∀ t, Continuous (phi2 t)) ∧
      (∀ t u, 2 * L * Real.exp
          (-(interpolationSmoothC1 kstar L (curvDist k0 k1 L) * |t|)) ≤ phi1 t u ∧
        phi1 t u ≤ 2 * L * Real.exp
          (interpolationSmoothC1 kstar L (curvDist k0 k1 L) * |t|)) ∧
      (∀ t u, |phi2 t u| ≤ interpolationSmoothC2 kstar kd L (curvDist k0 k1 L) *
        (2 * L) ^ 2 * |t| * Real.exp
          (2 * interpolationSmoothC1 kstar L (curvDist k0 k1 L) * |t|)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ u,
        HasDerivAt
          (fun r => interpCurve (kappaInterp k0 k1 r) theta0 L (Phi r u))
          ((normalVel k0 k1 theta0 L t (Phi t u) : ℂ) *
            NormalGaugeFrame.frameNormalVector
              (tangentAngle (kappaInterp k0 k1 t) theta0 (Phi t u))) t) := by
  obtain ⟨Phi, phi1, phi2, h0, ht, htr, h1, h2, hPc, h1c, h2c,
      hb1, hb2, -, -, -, -, -, hn⟩ :=
    exists_interpolation_gauge_flow_smooth_specialized_full
      hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL hd0 hd1
      hk0nn hk1nn hk0le hk1le hkd0 hkd1
  exact ⟨Phi, phi1, phi2, h0, ht, htr, h1, h2, hPc, h1c, h2c,
    hb1, hb2, hn⟩

end InterpolationGauge
