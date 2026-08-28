import Mathlib
import UnitTangentIterates.InterpolationGauge
import UnitTangentIterates.InterpolationSecondOrder
import UnitTangentIterates.GaugeFlowSmooth
import UnitTangentIterates.FlowSecondDerivativeJointContinuity

/-! # Spatially smooth interpolation gauge flow -/

noncomputable section

open Set Function FlowDerivative GaugeRate

namespace InterpolationGauge

open CurvatureInterpolation InterpolationNormal InterpolationEstimate
  InterpolationSecondOrder

/-- Tangential field whose unit-speed gauge rate is `gaugeField`. -/
def interpolationXi (k0 k1 : ℝ → ℝ) (theta0 L : ℝ) (t s : ℝ) : ℝ :=
  timeCut t * tangentVel k0 k1 theta0 L t s

/-- First state derivative of `interpolationXi`. -/
def interpolationXi1 (k0 k1 : ℝ → ℝ) (theta0 L : ℝ) (t s : ℝ) : ℝ :=
  timeCut t *
    (kappaInterp k0 k1 t s * normalVel k0 k1 theta0 L t s)

theorem hasDerivAt_interpolationXi
    {k0 k1 : ℝ → ℝ} {theta0 L : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1) (t s : ℝ) :
    HasDerivAt (interpolationXi k0 k1 theta0 L t)
      (interpolationXi1 k0 k1 theta0 L t s) s := by
  exact (hasDerivAt_tangentVel (θ₀ := theta0) (L := L) hk0 hk1 t s).const_mul
    (timeCut t)

theorem continuous_uncurry_interpolationXi
    {k0 k1 : ℝ → ℝ} {theta0 L : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous (uncurry (interpolationXi k0 k1 theta0 L)) := by
  exact (continuous_timeCut.comp continuous_fst).mul
    (continuous_uncurry_tangentVel (θ₀ := theta0) (L := L) hk0 hk1)

theorem continuous_uncurry_interpolationXi1
    {k0 k1 : ℝ → ℝ} {theta0 L : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous (uncurry (interpolationXi1 k0 k1 theta0 L)) := by
  exact (continuous_timeCut.comp continuous_fst).mul
    ((continuous_uncurry_kappaInterp hk0 hk1).mul
      (continuous_uncurry_normalVel (θ₀ := theta0) (L := L) hk0 hk1))

/-- A strengthened interpolation gauge flow.  The only residual analytic
hypotheses are the second state derivative of `interpolationXi`, its joint
continuity, and uniform bounds for the first two derivatives of the resulting
unit-speed gauge rate. -/
theorem exists_interpolation_gauge_flow_spatialTwoDerivatives_full
    {k0 k1 : ℝ → ℝ} {xi2 : ℝ → ℝ → ℝ} {theta0 L C1 C2 : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hxi2 : ∀ t s, HasDerivAt (interpolationXi1 k0 k1 theta0 L t)
      (xi2 t s) s)
    (hxi2c : Continuous (uncurry xi2))
    (hL : 0 < L)
    (hC1 : 0 ≤ C1)
    (hb1 : ∀ t s,
      |gaugeRate1 (interpolationXi k0 k1 theta0 L)
        (interpolationXi1 k0 k1 theta0 L)
        (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)) t s| ≤ C1)
    (hb2 : ∀ t s,
      |gaugeRate2 (interpolationXi k0 k1 theta0 L)
        (interpolationXi1 k0 k1 theta0 L) xi2
        (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) t s| ≤ C2) :
    ∃ (Phi phi1 phi2 : ℝ → ℝ → ℝ),
      (∀ u, Phi 0 u = 2 * L * u) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (gaugeField k0 k1 theta0 L t (Phi t u)) t) ∧
      (∀ t, StrictMono (Phi t)) ∧
      (∀ t u, HasDerivAt (Phi t) (phi1 t u) u) ∧
      (∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) ∧
      (∀ t, Continuous (Phi t)) ∧
      (∀ t, Continuous (phi1 t)) ∧
      (∀ t u, 2 * L * Real.exp (-(C1 * |t|)) ≤ phi1 t u ∧
        phi1 t u ≤ 2 * L * Real.exp (C1 * |t|)) ∧
      (∀ t u,
        |phi2 t u| ≤ C2 * (2 * L) ^ 2 * |t| * Real.exp (2 * C1 * |t|)) ∧
      phi1 = flowDeriv (gaugeRate1 (interpolationXi k0 k1 theta0 L)
        (interpolationXi1 k0 k1 theta0 L) (fun _ _ => 1) (fun _ _ => 0))
          Phi (2 * L) ∧
      phi2 = GaugeFlowTimeDerivative.flowDeriv2
        (gaugeRate1 (interpolationXi k0 k1 theta0 L)
          (interpolationXi1 k0 k1 theta0 L) (fun _ _ => 1) (fun _ _ => 0))
        (gaugeRate2 (interpolationXi k0 k1 theta0 L)
          (interpolationXi1 k0 k1 theta0 L) xi2
          (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0)) Phi (2 * L) ∧
      (∀ t, Continuous (phi2 t)) := by
  have hL2 : 0 < 2 * L := by
    linarith
  obtain ⟨Phi, hPhi0, hPhit, hmono, hPhi1, hPhi1bounds, hPhi2⟩ :=
    GaugeFlowSmooth.exists_gaugeFlow_smooth_of_bounds
      (xi := interpolationXi k0 k1 theta0 L)
      (xi1 := interpolationXi1 k0 k1 theta0 L) (xi2 := xi2)
      (v := fun _ _ => (1 : ℝ)) (v1 := fun _ _ => (0 : ℝ))
      (v2 := fun _ _ => (0 : ℝ)) (L := C1) (K2 := C2) (ell := 2 * L)
      hC1 (hasDerivAt_interpolationXi hk0 hk1) hxi2
      (fun _ x => hasDerivAt_const x 1) (fun _ x => hasDerivAt_const x 0)
      (fun _ _ => one_ne_zero) (continuous_uncurry_interpolationXi hk0 hk1)
      (continuous_uncurry_interpolationXi1 hk0 hk1) hxi2c
      continuous_const continuous_const continuous_const hb1 hb2 hL2
  let phi1 : ℝ → ℝ → ℝ :=
    flowDeriv (gaugeRate1 (interpolationXi k0 k1 theta0 L)
      (interpolationXi1 k0 k1 theta0 L) (fun _ _ => 1) (fun _ _ => 0)) Phi (2 * L)
  let phi2 : ℝ → ℝ → ℝ := fun t u =>
    phi1 t u * ∫ s in (0 : ℝ)..t,
      gaugeRate2 (interpolationXi k0 k1 theta0 L)
        (interpolationXi1 k0 k1 theta0 L) xi2
        (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) s (Phi s u) * phi1 s u
  have hflowHyp := gaugeRate_flow_hypotheses_of_bounds hC1
      (hasDerivAt_interpolationXi hk0 hk1) hxi2
      (fun _ x => hasDerivAt_const x 1) (fun _ x => hasDerivAt_const x 0)
      (fun _ _ => one_ne_zero) (continuous_uncurry_interpolationXi hk0 hk1)
      (continuous_uncurry_interpolationXi1 hk0 hk1) hxi2c
      continuous_const continuous_const continuous_const hb1 hb2
  obtain ⟨hlip, hcont, hxd, hxcont, hxxd, hxxcont, hxxbd⟩ := hflowHyp
  have hphi2cont : ∀ t, Continuous (phi2 t) := by
    intro t
    exact FlowJointContinuity.continuous_flowDeriv2_slice hlip hPhit hPhi0
      hxcont hxxcont
  refine ⟨Phi, phi1, phi2, hPhi0, ?_, hmono, hPhi1, ?_, ?_, ?_,
    hPhi1bounds, ?_, rfl, rfl, hphi2cont⟩
  · intro u t
    simpa [gaugeField, interpolationXi, gaugeRate] using hPhit u t
  · intro t u
    exact (hPhi2 t u).1
  · intro t
    exact continuous_iff_continuousAt.2 fun u => (hPhi1 t u).continuousAt
  · intro t
    exact continuous_iff_continuousAt.2 fun u => ((hPhi2 t u).1).continuousAt
  · intro t u
    exact (hPhi2 t u).2

/-- Backwards-compatible projection of the full smooth-flow theorem. -/
theorem exists_interpolation_gauge_flow_spatialTwoDerivatives
    {k0 k1 : ℝ → ℝ} {xi2 : ℝ → ℝ → ℝ} {theta0 L C1 C2 : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hxi2 : ∀ t s, HasDerivAt (interpolationXi1 k0 k1 theta0 L t)
      (xi2 t s) s)
    (hxi2c : Continuous (uncurry xi2))
    (hL : 0 < L)
    (hC1 : 0 ≤ C1)
    (hb1 : ∀ t s,
      |gaugeRate1 (interpolationXi k0 k1 theta0 L)
        (interpolationXi1 k0 k1 theta0 L)
        (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)) t s| ≤ C1)
    (hb2 : ∀ t s,
      |gaugeRate2 (interpolationXi k0 k1 theta0 L)
        (interpolationXi1 k0 k1 theta0 L) xi2
        (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) t s| ≤ C2) :
    ∃ (Phi phi1 phi2 : ℝ → ℝ → ℝ),
      (∀ u, Phi 0 u = 2 * L * u) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (gaugeField k0 k1 theta0 L t (Phi t u)) t) ∧
      (∀ t, StrictMono (Phi t)) ∧
      (∀ t u, HasDerivAt (Phi t) (phi1 t u) u) ∧
      (∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) ∧
      (∀ t, Continuous (Phi t)) ∧
      (∀ t, Continuous (phi1 t)) ∧
      (∀ t u, 2 * L * Real.exp (-(C1 * |t|)) ≤ phi1 t u ∧
        phi1 t u ≤ 2 * L * Real.exp (C1 * |t|)) ∧
      (∀ t u,
        |phi2 t u| ≤ C2 * (2 * L) ^ 2 * |t| * Real.exp (2 * C1 * |t|)) := by
  obtain ⟨Phi, phi1, phi2, h0, ht, hm, h1, h2, hPc, h1c, hb1', hb2', -⟩ :=
    exists_interpolation_gauge_flow_spatialTwoDerivatives_full
      hk0 hk1 hxi2 hxi2c hL hC1 hb1 hb2
  exact ⟨Phi, phi1, phi2, h0, ht, hm, h1, h2, hPc, h1c, hb1', hb2'⟩

end InterpolationGauge
