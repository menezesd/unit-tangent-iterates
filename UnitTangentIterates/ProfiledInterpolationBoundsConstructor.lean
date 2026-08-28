import Mathlib
import UnitTangentIterates.ProfiledInterpolationBounds
import UnitTangentIterates.InterpolationPathDist

/-! # Canonical quantitative bounds for the profiled interpolation

`ProfiledInterpolationBounds.Bounds` is the interface consumed by the
variable-speed junction theorem.  This file constructs all of its scalar
majorants from the quantitative curvature hypotheses used by the interpolation
path theorem.  The only residual input is the pair of profiled flow-derivative
ceilings; these are logically separate ODE estimates.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace ProfiledInterpolationBoundsConstructor

open CurvatureInterpolation InterpolationEstimate InterpolationGauge
  InterpolationPathDist InterpolationVariableSpeedConstants
  InterpolationControlledJunctionFinal ProfiledInterpolationFields
  ProfiledInterpolationGlobalBounds PathMetricCircle

/-- The two ODE estimates not supplied by the curvature and marked-density
estimates.  All other fields of `ProfiledInterpolationBounds.Bounds` are
constructed below. -/
structure FlowResidual
    (k0 k1 k0' k1' : ℝ → ℝ) (theta0 L kstar kd eps : ℝ)
    (Phi : ℝ → ℝ → ℝ) : Prop where
  flowDeriv_le : ∀ t u, FlowDerivative.flowDeriv
    (hx k0 k1 theta0 L) (PhiB Phi) (2 * L) t u ≤ costFac kstar L eps
  flowDeriv2_le : ∀ t u, |GaugeFlowTimeDerivative.flowDeriv2
    (hx k0 k1 theta0 L) (hxx k0 k1 k0' k1' theta0 L)
    (PhiB Phi) (2 * L) t u| ≤ interpolationG1 kstar kd L eps

/-- The first spatial derivative of the unprofiled interpolation gauge field. -/
def rawHx (k0 k1 : ℝ → ℝ) (theta0 L : ℝ) : ℝ → ℝ → ℝ := fun t s ↦
  -(timeCut t * (kappaInterp k0 k1 t s * normalVel k0 k1 theta0 L t s))

/-- The second spatial derivative of the unprofiled interpolation gauge field. -/
def rawHxx (k0 k1 k0' k1' : ℝ → ℝ) (theta0 L : ℝ) : ℝ → ℝ → ℝ :=
  gaugeFieldStateSecond k0 k1 k0' k1' theta0 L

/-- The raw Jacobi estimates pass through the stopping profile.  Continuity
needed by the time-change identities follows from the actual interpolation
fields and the flow equation, rather than being an additional hypothesis. -/
theorem flowResidual_of_raw_bounds
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L kstar kd eps : ℝ}
    {Phi : ℝ → ℝ → ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 ≤ L) (heps : 0 ≤ eps)
    (hPhid : ∀ u t, HasDerivAt (fun r ↦ Phi r u)
      (gaugeField k0 k1 theta0 L t (Phi t u)) t)
    (hraw1 : ∀ a v, FlowDerivative.flowDeriv
      (rawHx k0 k1 theta0 L) Phi (2 * L) a v ≤
        2 * L * Real.exp (InterpolationFrame.rate1Bound kstar L eps * |a|))
    (hraw2 : ∀ a v, |GaugeFlowTimeDerivative.flowDeriv2
      (rawHx k0 k1 theta0 L) (rawHxx k0 k1 k0' k1' theta0 L)
      Phi (2 * L) a v| ≤
        InterpolationFrame.rate2Bound kstar kd L eps * (2 * L) ^ 2 * |a| *
          Real.exp (2 * InterpolationFrame.rate1Bound kstar L eps * |a|)) :
    FlowResidual k0 k1 k0' k1' theta0 L kstar kd eps Phi := by
  have hxcont : Continuous (uncurry (rawHx k0 k1 theta0 L)) := by
    simpa [rawHx, InterpolationGauge.interpolationXi1] using
      (InterpolationGauge.continuous_uncurry_interpolationXi1 hk0 hk1).neg
  have hxxcont : Continuous (uncurry (rawHxx k0 k1 k0' k1' theta0 L)) := by
    simpa [rawHxx] using
      InterpolationGauge.continuous_uncurry_gaugeFieldStateSecond
        hk0 hk1 hk0'c hk1'c
  have hPhiTime : ∀ u, Continuous fun s ↦ Phi s u := by
    intro u
    have hd : Differentiable ℝ (fun s ↦ Phi s u) :=
      fun s ↦ (hPhid u s).differentiableAt
    exact hd.continuous
  refine ⟨?_, ?_⟩
  · intro t u
    have hxgc : Continuous fun s ↦ rawHx k0 k1 theta0 L s (Phi s u) :=
      hxcont.comp (continuous_id.prodMk (hPhiTime u))
    have hb := ProfiledInterpolationFlowBounds.flowDeriv_le
      hkstar hL heps hxgc hraw1 (t := t) (u := u)
    have hprofile : (fun r x ↦ w r * rawHx k0 k1 theta0 L (B r) x) =
        ProfiledInterpolationFields.hx k0 k1 theta0 L := by
      funext r x
      simp only [ProfiledInterpolationFields.hx, rawHx]
    rw [hprofile] at hb
    exact hb
  · intro t u
    have hxgc : Continuous fun s ↦ rawHx k0 k1 theta0 L s (Phi s u) :=
      hxcont.comp (continuous_id.prodMk (hPhiTime u))
    have hxxgc : Continuous fun s ↦ rawHxx k0 k1 k0' k1' theta0 L s (Phi s u) :=
      hxxcont.comp (continuous_id.prodMk (hPhiTime u))
    have hFgc : Continuous fun s ↦ FlowDerivative.flowDeriv
        (rawHx k0 k1 theta0 L) Phi (2 * L) s u :=
      FlowDerivative.continuous_flowDeriv_time hPhid hxcont u
    have hb := ProfiledInterpolationFlowBounds.flowDeriv2_le
      hkstar hkd hL heps hxgc hxxgc hFgc hraw2 (t := t) (u := u)
    have hxprofile : (fun r x ↦ w r * rawHx k0 k1 theta0 L (B r) x) =
        ProfiledInterpolationFields.hx k0 k1 theta0 L := by
      funext r x
      simp only [ProfiledInterpolationFields.hx, rawHx]
    have hxxprofile : (fun r x ↦ w r * rawHxx k0 k1 k0' k1' theta0 L (B r) x) =
        ProfiledInterpolationFields.hxx k0 k1 k0' k1' theta0 L := by
      rfl
    rw [hxprofile, hxxprofile] at hb
    exact hb

/-- The output equations and estimates of
`exists_interpolation_gauge_flow_smooth_specialized_full` discharge the raw
Jacobi bounds exactly: `interpolationSmoothC1/C2` are definitionally the
canonical `rate1Bound/rate2Bound`. -/
theorem flowResidual_of_smooth_data
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L kstar kd eps : ℝ}
    {Phi phi1 phi2 : ℝ → ℝ → ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hkstar : 0 ≤ kstar) (hkd : 0 ≤ kd) (hL : 0 ≤ L) (heps : 0 ≤ eps)
    (hPhid : ∀ u t, HasDerivAt (fun r ↦ Phi r u)
      (gaugeField k0 k1 theta0 L t (Phi t u)) t)
    (hphi1bd : ∀ t u, phi1 t u ≤ 2 * L *
      Real.exp (InterpolationGauge.interpolationSmoothC1 kstar L eps * |t|))
    (hphi2bd : ∀ t u, |phi2 t u| ≤
      InterpolationGauge.interpolationSmoothC2 kstar kd L eps *
        (2 * L) ^ 2 * |t| *
          Real.exp (2 * InterpolationGauge.interpolationSmoothC1 kstar L eps * |t|))
    (hphi1eq : phi1 = FlowDerivative.flowDeriv
      (GaugeRate.gaugeRate1 (InterpolationGauge.interpolationXi k0 k1 theta0 L)
        (InterpolationGauge.interpolationXi1 k0 k1 theta0 L)
        (fun _ _ ↦ 1) (fun _ _ ↦ 0)) Phi (2 * L))
    (hphi2eq : phi2 = GaugeFlowTimeDerivative.flowDeriv2
      (GaugeRate.gaugeRate1 (InterpolationGauge.interpolationXi k0 k1 theta0 L)
        (InterpolationGauge.interpolationXi1 k0 k1 theta0 L)
        (fun _ _ ↦ 1) (fun _ _ ↦ 0))
      (GaugeRate.gaugeRate2 (InterpolationGauge.interpolationXi k0 k1 theta0 L)
        (InterpolationGauge.interpolationXi1 k0 k1 theta0 L)
        (fun t s ↦ -gaugeFieldStateSecond k0 k1 k0' k1' theta0 L t s)
        (fun _ _ ↦ 1) (fun _ _ ↦ 0) (fun _ _ ↦ 0)) Phi (2 * L)) :
    FlowResidual k0 k1 k0' k1' theta0 L kstar kd eps Phi := by
  apply flowResidual_of_raw_bounds hk0 hk1 hk0'c hk1'c
    hkstar hkd hL heps hPhid
  · intro a v
    have hb := hphi1bd a v
    rw [hphi1eq] at hb
    have hraw : GaugeRate.gaugeRate1
        (InterpolationGauge.interpolationXi k0 k1 theta0 L)
        (InterpolationGauge.interpolationXi1 k0 k1 theta0 L)
        (fun _ _ ↦ 1) (fun _ _ ↦ 0) = rawHx k0 k1 theta0 L := by
      funext t s
      simp [rawHx, GaugeRate.gaugeRate1, InterpolationGauge.interpolationXi1]
    rw [hraw] at hb
    simpa [InterpolationGauge.interpolationSmoothC1,
      InterpolationFrame.rate1Bound] using hb
  · intro a v
    have hb := hphi2bd a v
    rw [hphi2eq] at hb
    have hraw1 : GaugeRate.gaugeRate1
        (InterpolationGauge.interpolationXi k0 k1 theta0 L)
        (InterpolationGauge.interpolationXi1 k0 k1 theta0 L)
        (fun _ _ ↦ 1) (fun _ _ ↦ 0) = rawHx k0 k1 theta0 L := by
      funext t s
      simp [rawHx, GaugeRate.gaugeRate1, InterpolationGauge.interpolationXi1]
    have hraw2 : GaugeRate.gaugeRate2
        (InterpolationGauge.interpolationXi k0 k1 theta0 L)
        (InterpolationGauge.interpolationXi1 k0 k1 theta0 L)
        (fun t s ↦ -gaugeFieldStateSecond k0 k1 k0' k1' theta0 L t s)
        (fun _ _ ↦ 1) (fun _ _ ↦ 0) (fun _ _ ↦ 0) =
        rawHxx k0 k1 k0' k1' theta0 L := by
      funext t s
      simp [rawHxx, GaugeRate.gaugeRate2]
    rw [hraw1, hraw2] at hb
    simpa [InterpolationGauge.interpolationSmoothC1,
      InterpolationGauge.interpolationSmoothC2, InterpolationFrame.rate1Bound,
      InterpolationFrame.rate2Bound] using hb

/-- The canonical smooth interpolation gauge comes equipped with a closed
`FlowResidual`; no flow ceiling remains to be supplied by a configured edge. -/
theorem exists_smooth_flow_with_residual
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
      (∀ u t, HasDerivAt (fun r ↦ Phi r u)
        (gaugeField k0 k1 theta0 L t (Phi t u)) t) ∧
      (∀ t u, Phi t (u + 1) = Phi t u + 2 * L) ∧
      (∀ t u, HasDerivAt (Phi t) (phi1 t u) u) ∧
      (∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) ∧
      (∀ t, Continuous (Phi t)) ∧
      (∀ t, Continuous (phi1 t)) ∧
      (∀ t, Continuous (phi2 t)) ∧
      FlowResidual k0 k1 k0' k1' theta0 L kstar kd (curvDist k0 k1 L) Phi ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ u,
        HasDerivAt
          (fun r ↦ interpCurve (kappaInterp k0 k1 r) theta0 L (Phi r u))
          ((normalVel k0 k1 theta0 L t (Phi t u) : ℂ) *
            NormalGaugeFrame.frameNormalVector
              (tangentAngle (kappaInterp k0 k1 t) theta0 (Phi t u))) t) := by
  obtain ⟨Phi, phi1, phi2, h0, ht, htr, h1, h2, hPc, h1c, h2c,
      hb1, hb2, heq1, heq2, -, -, -, hn⟩ :=
    InterpolationGauge.exists_interpolation_gauge_flow_smooth_specialized_full
      hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL hd0 hd1
      hk0nn hk1nn hk0le hk1le hkd0 hkd1
  have hkstar : 0 ≤ kstar := le_trans (hk0nn 0) (hk0le 0)
  have hkd : 0 ≤ kd := le_trans (abs_nonneg _) (hkd0 0)
  have heps : 0 ≤ curvDist k0 k1 L :=
    InterpolationNormal.integral_abs_sub_nonneg hk0 hk1 hL.le
  have hF : FlowResidual k0 k1 k0' k1' theta0 L kstar kd
      (curvDist k0 k1 L) Phi :=
    flowResidual_of_smooth_data hk0 hk1 hk0'c hk1'c hkstar hkd hL.le heps ht
      (fun t u ↦ (hb1 t u).2) hb2 heq1 heq2
  exact ⟨Phi, phi1, phi2, h0, ht, htr, h1, h2, hPc, h1c, h2c, hF, hn⟩

set_option maxHeartbeats 1000000 in
/-- Construct the complete quantitative package from the same explicit edge
hypotheses that construct the canonical interpolation and its normal path.

The resulting defect parameter is the actual curvature distance.  The
majorants are canonical:

* `m = w * interpPathCost`;
* `S0,S1,S2 = w * costE,costG1,costG2`;
* `C = kstar*m` and `C2 = kd*m + kstar*S1`;
* normalized frame coefficients are `1`, `1/costFac`, and
  `1/costFac^2`.
-/
theorem exists_bounds_of_curvature_data
    {p q : Data} {k0 k1 k0' k1' : ℝ → ℝ}
    {theta0 L kstar kd dsup : ℝ} {Phi : ℝ → ℝ → ℝ}
    (Q : Certificate k0 k1 k0' k1' theta0 L Phi)
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Periodic k0 L) (hper1 : Periodic k1 L)
    (htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi)
    (hL : 0 < L)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r)
    (hd1 : ∀ r, HasDerivAt k1 (k1' r) r)
    (hd : ∀ r, |k1 r - k0 r| ≤ dsup)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar)
    (hPhi0 : ∀ u, Phi 0 u = 2 * L * u)
    (hPhid : ∀ u t, HasDerivAt (fun r ↦ Phi r u)
      (gaugeField k0 k1 theta0 L t (Phi t u)) t)
    (hPhinormal : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u,
      HasDerivAt
        (fun r ↦ interpCurve (kappaInterp k0 k1 r) theta0 L (Phi r u))
        ((normalVel k0 k1 theta0 L t (Phi t u) : ℂ) *
          NormalGaugeFrame.frameNormalVector
            (tangentAngle (kappaInterp k0 k1 t) theta0 (Phi t u))) t)
    (hp : ∀ u, p.1 u = interpCurve k0 theta0 L (2 * L * u))
    (hq : ∀ u, q.1 u = interpCurve k1 theta0 L (Phi 1 u))
    (F : FlowResidual k0 k1 k0' k1' theta0 L kstar kd
      (curvDist k0 k1 L) Phi) :
    ∃ D : ProfiledInterpolationBounds.Bounds p q k0 k1 k0' k1'
        theta0 L kstar kd dsup (curvDist k0 k1 L) Phi,
      D.K = globalK kstar kd dsup L (curvDist k0 k1 L) ∧
      D.K2 = globalK2 kstar kd dsup L (curvDist k0 k1 L) ∧
      D.c1 = 1 / costFac kstar L (curvDist k0 k1 L) ∧
      D.m = fun t ↦ w t *
        interpPathCost kstar kd dsup L (curvDist k0 k1 L) := by
  let eps := curvDist k0 k1 L
  let P := interpPathCost kstar kd dsup L eps
  let fac := costFac kstar L eps
  let s0 : ℝ → ℝ := fun t ↦ w t * costE L eps
  let s1 : ℝ → ℝ := fun t ↦ w t * costG1 kstar L eps
  let s2 : ℝ → ℝ := fun t ↦ w t * costG2 kstar kd dsup L eps
  let majorant : ℝ → ℝ := fun t ↦ w t * P
  have heps : 0 ≤ eps :=
    InterpolationNormal.integral_abs_sub_nonneg hk0 hk1 hL.le
  have hkstar : 0 ≤ kstar := le_trans (hk0nn 0) (hk0le 0)
  have hkd : 0 ≤ kd := le_trans (abs_nonneg _) (hkd0 0)
  have hdsup : 0 ≤ dsup := le_trans (abs_nonneg _) (hd 0)
  have hP : 0 ≤ P := interpPathCost_nonneg hkstar hkd hdsup hL.le heps
  have hfac : 0 < fac := by
    dsimp [fac, costFac]
    positivity
  have hE : 0 ≤ costE L eps := costE_nonneg hL.le heps
  have hG1 : 0 ≤ costG1 kstar L eps := costG1_nonneg hkstar hL.le heps
  have hG2 : 0 ≤ costG2 kstar kd dsup L eps :=
    costG2_nonneg hkd hdsup hL.le heps
  have hEP : costE L eps ≤ P :=
    costE_le_interpPathCost hkstar hkd hdsup hL.le heps
  have hG1P : costG1 kstar L eps * fac ≤ P := by
    simpa [fac] using
      costG1_mul_costFac_le hkstar hkd hdsup hL.le heps
  have hG2P : costG2 kstar kd dsup L eps * fac ^ 2 ≤ P := by
    simpa [fac] using
      costG2_mul_costFac_sq_le hkstar hkd hdsup hL.le heps
  have hkappa : ∀ t x, |kappa k0 k1 t x| ≤ kstar := by
    intro t x
    have hB := ProfiledInterpolationFields.B_mem_Icc t
    have hnonneg : 0 ≤ kappa k0 k1 t x := by
      dsimp [kappa, kappaInterp]
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr hB.2) (hk0nn x))
        (mul_nonneg hB.1 (hk1nn x))
    rw [abs_of_nonneg hnonneg]
    exact kappaInterp_le hk0le hk1le hB x
  have hkX : ∀ t x, |kX k0' k1' t x| ≤ kd := by
    intro t x
    have hB := ProfiledInterpolationFields.B_mem_Icc t
    rw [kX]
    calc
      |(1 - B t) * k0' x + B t * k1' x| ≤
          |1 - B t| * |k0' x| + |B t| * |k1' x| := by
            simpa [abs_mul] using
              abs_add_le ((1 - B t) * k0' x) (B t * k1' x)
      _ ≤ (1 - B t) * kd + B t * kd := by
        rw [abs_of_nonneg (sub_nonneg.mpr hB.2), abs_of_nonneg hB.1]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hkd0 x) (sub_nonneg.mpr hB.2))
          (mul_le_mul_of_nonneg_left (hkd1 x) hB.1)
      _ = kd := by ring
  have hen0 : ∀ t x, |en k0 k1 theta0 L t x| ≤ s0 t := by
    intro t x
    have hwnn := w_nonneg t
    rw [en, abs_mul, abs_of_nonneg hwnn]
    exact mul_le_mul_of_nonneg_left
      (by simpa [eps, costE] using
        abs_normalVel_le hk0 hk1 hper0 hper1 htot0 htot1 hL (B t) x) hwnn
  have hen1 : ∀ t x, |enS k0 k1 theta0 L t x| ≤ s1 t := by
    intro t x
    have hwnn := w_nonneg t
    have hraw := InterpolationEstimate.abs_normalVelDeriv_le
      (θ₀ := theta0) (kstar := kstar) (t := B t)
      hk0 hk1 hper0 hper1 htot0 htot1 hL
      (ProfiledInterpolationFields.B_mem_Icc t)
      hk0nn hk1nn hk0le hk1le x
    rw [enS, abs_mul, abs_of_nonneg hwnn]
    exact mul_le_mul_of_nonneg_left
      (by simpa [eps, costG1] using hraw) hwnn
  have hen2 : ∀ t x, |enSS k0 k1 k0' k1' theta0 L t x| ≤ s2 t := by
    intro t x
    have hwnn := w_nonneg t
    have hraw := InterpolationSecondOrder.abs_normalVelSecondDeriv_le
      (θ₀ := theta0) (kstar := kstar) (dsup := dsup) (kd := kd) (t := B t)
      hk0 hk1 hper0 hper1 htot0 htot1 hL
      (ProfiledInterpolationFields.B_mem_Icc t)
      hd hkd0 hkd1 hk0nn hk1nn hk0le hk1le x
    rw [enSS, abs_mul, abs_of_nonneg hwnn]
    exact mul_le_mul_of_nonneg_left
      (by simpa [eps, costG2] using hraw) hwnn
  have hfield : ∀ t x, |h k0 k1 theta0 L t x| ≤ s0 t := by
    intro t x
    have hwnn := w_nonneg t
    rw [h, abs_mul, abs_of_nonneg hwnn]
    exact mul_le_mul_of_nonneg_left
      (by simpa [eps, costE] using
        abs_gaugeField_le hk0 hk1 hper0 hper1 htot0 htot1 hL (B t) x) hwnn
  have hs0major : ∀ t, s0 t ≤ majorant t := by
    intro t
    exact mul_le_mul_of_nonneg_left hEP (w_nonneg t)
  have hs1fac : ∀ t, s1 t * fac ≤ majorant t := by
    intro t
    dsimp [s1, majorant]
    calc
      w t * costG1 kstar L eps * fac = w t * (costG1 kstar L eps * fac) := by ring
      _ ≤ w t * P := mul_le_mul_of_nonneg_left hG1P (w_nonneg t)
  have hs2fac : ∀ t, s2 t * fac ^ 2 ≤ majorant t := by
    intro t
    dsimp [s2, majorant]
    calc
      w t * costG2 kstar kd dsup L eps * fac ^ 2 =
          w t * (costG2 kstar kd dsup L eps * fac ^ 2) := by ring
      _ ≤ w t * P := mul_le_mul_of_nonneg_left hG2P (w_nonneg t)
  have hm0 : ∀ t, 0 ≤ majorant t := fun t ↦ mul_nonneg (w_nonneg t) hP
  have hs1nn : ∀ t, 0 ≤ s1 t := fun t ↦ mul_nonneg (w_nonneg t) hG1
  obtain ⟨Gamma, hT, hX, heta, hm, _hcost⟩ :=
    normalPath_interp_of_gauge_full hk0 hk1 hk0'c hk1'c hper0 hper1
      htot0 htot1 hL hd0 hd1 hd hkd0 hkd1 hk0nn hk1nn hk0le hk1le
      Phi hPhi0 hPhid hPhinormal p q hp hq
  refine ⟨{
    K := globalK kstar kd dsup L eps
    K2 := globalK2 kstar kd dsup L eps
    C := fun t ↦ kstar * majorant t
    C2 := fun t ↦ kd * majorant t + kstar * s1 t
    Kx := fun _ ↦ kd
    Rb := s0
    S0 := s0
    S1 := s1
    S2 := s2
    m := majorant
    c0 := 1
    c1 := 1 / fac
    c2 := 1 / fac ^ 2
    r := 1
    kx := kd
    hlip := by
      intro t
      exact lipschitzWith_of_deriv_le_nnreal (Q.field_space t) fun x ↦
        abs_hx_le_global hkstar hkd hdsup hL.le heps (hkappa t x)
          ((hen0 t x).trans (hs0major t))
    hxxK := by
      intro t x
      exact abs_hxx_le_global hkstar hkd hdsup hL.le heps
        (hkX t x) (hkappa t x) (hen0 t x) (hen1 t x)
    hP1 := F.flowDeriv_le
    hG1 := F.flowDeriv2_le
    hk := hkappa
    hC := by
      intro t x
      exact abs_hx_le (hkappa t x) ((hen0 t x).trans (hs0major t))
        hkstar (hm0 t)
    hC2 := by
      intro t x
      exact abs_hxx_le (hkX t x) (hkappa t x)
        ((hen0 t x).trans (hs0major t)) (hen1 t x) hkd hkstar
    hCnn := fun t ↦ mul_nonneg hkstar (hm0 t)
    hC2nn := fun t ↦ add_nonneg (mul_nonneg hkd (hm0 t))
      (mul_nonneg hkstar (hs1nn t))
    hcost := by intro t; ring_nf; rfl
    hcost2 := by
      intro t
      have hC0 : 0 ≤ kstar * majorant t := mul_nonneg hkstar (hm0 t)
      have hC20 : 0 ≤ kd * majorant t + kstar * s1 t :=
        add_nonneg (mul_nonneg hkd (hm0 t)) (mul_nonneg hkstar (hs1nn t))
      have hsharp := ProfiledInterpolationFlowBounds.sharp_field_costs
        hkstar hkd hL.le heps (hm0 t) (hs1nn t)
        (by rw [abs_of_nonneg hC0])
        (by rw [abs_of_nonneg hC20]) (hs1fac t)
      rw [abs_of_nonneg hC0, abs_of_nonneg hC20] at hsharp
      simpa [eps, fac] using hsharp
    hKxbd := hkX
    hRbd := hfield
    hKxnn := fun _ ↦ hkd
    hS0bd := hen0
    hS1bd := hen1
    hS2bd := hen2
    hS0m := by intro t; simpa using hs0major t
    hS1m := by
      intro t
      calc
        s1 t ≤ majorant t / fac := (le_div_iff₀ hfac).2 (hs1fac t)
        _ = 1 / fac * majorant t := by field_simp
    hS2m := by
      intro t
      calc
        s2 t ≤ majorant t / fac ^ 2 :=
          (le_div_iff₀ (sq_pos_of_pos hfac)).2 (hs2fac t)
        _ = 1 / fac ^ 2 * majorant t := by field_simp
    hRbm := by intro t; simpa using hs0major t
    hKxm := fun _ ↦ le_rfl
    hr := zero_le_one
    hm0 := hm0
    hnumA := by
      simpa [fac] using frame_angle_numerical hkstar hkd hL
    hnumK := by
      simpa [fac] using frame_curvature_numerical hkstar hkd hL
    hstart := by
      intro u
      change interpCurve (kappaInterp k0 k1 (B 0)) theta0 L
        (Phi (B 0) u) = p.1 u
      rw [B_zero, hPhi0]
      simpa [kappaInterp] using (hp u).symm
    hfinish := by
      intro u
      change interpCurve (kappaInterp k0 k1 (B 1)) theta0 L
        (Phi (B 1) u) = q.1 u
      rw [B_one]
      simpa [kappaInterp] using (hq u).symm
    hmc := continuous_w.mul continuous_const
    hmstop := by
      intro t ht
      simp [majorant, w_eq_zero ht]
    hmbd := by
      intro t u
      exact (hen0 t (PhiB Phi t u)).trans (hs0major t)
    hmsup := by
      intro t j hj
      have hsup := Gamma.le_m_sup t j hj
      rw [hm, heta] at hsup
      simpa [pathEta, scaledEta, en, PhiB] using hsup
    hcostIntegral := by
      dsimp [majorant]
      rw [intervalIntegral.integral_mul_const, integral_w, one_mul]
  }, rfl, rfl, rfl, rfl⟩

end ProfiledInterpolationBoundsConstructor
