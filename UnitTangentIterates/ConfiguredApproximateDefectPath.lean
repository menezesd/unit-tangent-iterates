import Mathlib
import UnitTangentIterates.ProfiledInterpolationBoundsConstructor
import UnitTangentIterates.ConstructedConfiguredSequenceWeighted
import UnitTangentIterates.InterpolationPathDistL1

/-! # Controlled approximate defect paths for configured model edges

This module connects the concrete curvature interpolation to the approximate
base-defect hypothesis.  It records precisely the data not retained by
`ConfiguredModelSequence`: second-order smoothness, the external marked
endpoint realization, uniform choices of the controlled constants, and the
comparison of interpolation cost with the paper's marked-distance defect.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed

namespace ConfiguredApproximateDefectPath

open ModelOrbitDefect CurvatureInterpolation InterpolationEstimate
  InterpolationPathDist InterpolationVariableSpeedConstants
  InterpolationControlledJunctionFinal ProfiledInterpolationFields
  ProfiledInterpolationBoundsConstructor
  PathMetric.WeightedMarkedDefectThreshold

/-- Decreasing the positive `P0` denominator enlarges the two estimates in
which it occurs and preserves a variable-speed certificate. -/
theorem IsVariableSpeedNormalPath.mono_P0
    {p q : Data} {Gamma : NormalPath p q}
    {P0 P0' P1 khat G1 Cg : ℝ}
    (h : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Gamma)
    (hP0' : 0 < P0') (hle : P0' ≤ P0) :
    IsVariableSpeedNormalPath P0' P1 khat G1 Cg Gamma := by
  obtain ⟨g, gu, gt, gut, theta, kappa, etas, kt, hgnn, hgub, hguB, hkap,
    hXu, hgud, hthetau, hgt, hgtc, hgtbd, hgut, hgutc, hgutbd,
    hthetat, hetasc, hetas, hkappat, hktc, hkt⟩ := h
  have hP0 : 0 < P0 := hP0'.trans_le hle
  have hinv : 1 / P0 ≤ 1 / P0' := by
    exact one_div_le_one_div_of_le hP0' hle
  have hinvsq : 1 / P0 ^ 2 ≤ 1 / P0' ^ 2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hP0')
    simpa [pow_two] using mul_self_le_mul_self hP0'.le hle
  refine ⟨g, gu, gt, gut, theta, kappa, etas, kt, hgnn, hgub, hguB, hkap,
    hXu, hgud, hthetau, hgt, hgtc, hgtbd, hgut, hgutc, hgutbd,
    hthetat, hetasc, ?_, hkappat, hktc, ?_⟩
  · intro t u
    exact (hetas t u).trans (mul_le_mul_of_nonneg_right hinv (Gamma.m_nonneg t))
  · intro t u
    exact (hkt t u).trans (mul_le_mul_of_nonneg_right
      (add_le_add hinvsq le_rfl) (Gamma.m_nonneg t))

/-- The exact residual at the boundary between a configured curvature edge and
the external marked recursive orbit.  The endpoint clause is stated for any
solution of the canonical gauge IVP, avoiding a noncanonical choice of flow. -/
structure Residual
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (B : Data → Data) (Q : ℕ → Data)
    (P0 P1 G1 Cg defectScale : ℝ) : Prop where
  model_kstar : D.model.kstar = D.kstar
  model_kd : D.model.kd = D.kd
  KP_C2 : ∀ n, ContDiff ℝ 2
    (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
  kH_C2 : ∀ n, ContDiff ℝ 2 (D.model.configs n).kH
  endpoints : ∀ n (Phi : ℝ → ℝ → ℝ),
    (∀ u, Phi 0 u = 2 * D.Hs n * u) →
    (∀ u t, HasDerivAt (fun r ↦ Phi r u)
      (InterpolationGauge.gaugeField
        (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
        (D.model.configs n).kH D.model.thetaBase (D.Hs n) t (Phi t u)) t) →
    (∀ u, (Q n).1 u = interpCurve
      (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
      D.model.thetaBase (D.Hs n) (2 * D.Hs n * u)) ∧
    (∀ u, (B (Q (n + 1))).1 u =
      interpCurve (D.model.configs n).kH D.model.thetaBase (D.Hs n) (Phi 1 u))
  P0_pos : 0 < P0
  P0_le : ∀ n, P0 ≤ interpolationP0 D.kstar D.kd (D.Hs n)
    (curvDist
      (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
      (D.model.configs n).kH (D.Hs n))
  P1_dom : ∀ n, costFac D.kstar (D.Hs n)
    (curvDist
      (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
      (D.model.configs n).kH (D.Hs n)) ≤ P1
  G1_dom : ∀ n, interpolationG1 D.kstar D.kd (D.Hs n)
    (curvDist
      (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
      (D.model.configs n).kH (D.Hs n)) ≤ G1
  Cg_dom : ∀ n, interpolationCgFinal D.kstar D.kd (D.Hs n)
    (curvDist
      (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
      (D.model.configs n).kH (D.Hs n)) ≤ Cg
  cost_dom : ∀ n,
    interpPathCost D.kstar D.kd
      (CurvatureStabilityL1.l1Modulus (2 * D.kd)
        (curvDist
          (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
          (D.model.configs n).kH (D.Hs n)) (D.Hs n))
      (D.Hs n)
      (curvDist
        (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
        (D.model.configs n).kH (D.Hs n)) ≤
    canonicalMarkedDefect D.matchCoefficient defectScale D.kstar D.kd
      D.beta D.Hs n

set_option maxHeartbeats 2000000 in
/-- A configured edge, together with only the residual facts above, produces
the approximate controlled base-defect path required by the final assembly. -/
theorem exists_approx_defect_path
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {B : Data → Data} {Q : ℕ → Data}
    {P0 P1 G1 Cg defectScale : ℝ}
    (R : Residual D B Q P0 P1 G1 Cg defectScale)
    (n : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ Lambda : NormalPath (Q n) (B (Q (n + 1))),
      cost Lambda ≤ canonicalMarkedDefect D.matchCoefficient defectScale
        D.kstar D.kd D.beta D.Hs n + eta ∧
      IsVariableSpeedNormalPath P0 P1 D.kstar G1 Cg Lambda := by
  let c := D.model.configs n
  let L := D.Hs n
  let k0 := modelCurvature c.yu c.yu' L
  let k1 := c.kH
  let k0' := c.KP'
  let k1' := kHderiv c.Y (modelCurvature c.y c.yd (D.Hs (n + 1))) c.sf
  let eps := curvDist k0 k1 L
  let dsup := CurvatureStabilityL1.l1Modulus (2 * D.kd) eps L
  have hL : 0 < L := D.model.separation_pos n
  have hkstar : 0 ≤ D.kstar := D.kstar_nonneg
  have hkd : 0 < D.kd := by simpa [c, R.model_kd] using c.hkd
  have hk0c : Continuous k0 := by simpa [c, L, k0] using c.continuous_KP
  have hk1c : Continuous k1 := by simpa [c, k1] using c.continuous_kH
  have hk0'c : Continuous k0' := by simpa [c, k0'] using c.continuous_KP'
  have hk1'c : Continuous k1' := by simpa [c, k1'] using c.continuous_kHderiv
  have hper0 : Periodic k0 L := by simpa [c, L, k0] using c.periodic_KP
  have hper1 : Periodic k1 L := by simpa [c, L, k1] using c.periodic_kH
  have htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi := by
    simpa [c, L, k0] using c.integral_KP_eq_pi
  have htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi := by
    simpa [c, L, k1] using c.integral_kH_eq_pi
  have hd0 : ∀ r, HasDerivAt k0 (k0' r) r := by
    intro r
    simpa [c, L, k0, k0'] using c.hd1 r
  have hd1 : ∀ r, HasDerivAt k1 (k1' r) r := by
    intro r
    simpa [c, k1, k1'] using c.hasDerivAt_kH r
  have hkd0 : ∀ r, |k0' r| ≤ D.kd := by
    intro r
    simpa [c, k0', R.model_kd] using c.abs_KP'_le r
  have hkd1 : ∀ r, |k1' r| ≤ D.kd := by
    intro r
    simpa [c, k1', R.model_kd] using c.abs_kHderiv_le r
  have hk0nn : ∀ r, 0 ≤ k0 r := by intro r; simpa [c, L, k0] using c.KP_nonneg r
  have hk1nn : ∀ r, 0 ≤ k1 r := by intro r; simpa [c, k1] using c.kH_nonneg r
  have hk0le : ∀ r, k0 r ≤ D.kstar := by
    intro r
    simpa [c, L, k0, R.model_kstar] using c.KP_le r
  have hk1le : ∀ r, k1 r ≤ D.kstar := by
    intro r
    simpa [c, k1, R.model_kstar] using c.kH_le r
  have hdsup : ∀ r, |k1 r - k0 r| ≤ dsup := by
    intro r
    exact InterpolationPathDistL1.sup_le_of_curvDist hL hkd hper0 hper1
      hd0 hd1 hkd0 hkd1 r
  obtain ⟨Phi, phi1, phi2, hPhi0, hPhid, htrans, _hphi1, _hphi2,
      _hPc, _hphi1c, _hphi2c, hF, hnormal⟩ :=
    exists_smooth_flow_with_residual hk0c hk1c hk0'c hk1'c hper0 hper1
      htot0 htot1 hL hd0 hd1 hk0nn hk1nn hk0le hk1le hkd0 hkd1
  have hQcert : Certificate k0 k1 k0' k1' D.model.thetaBase L Phi :=
    ProfiledInterpolationFields.exists_certificate
      (by simpa [c, L, k0] using R.KP_C2 n)
      (by simpa [c, k1] using R.kH_C2 n)
      hk0'c hk1'c hd0 hd1 hper0 hper1 htot0 htot1 hPhid hPhi0 htrans
  obtain ⟨hp, hq⟩ := R.endpoints n Phi
    (by simpa [L] using hPhi0) (by simpa [k0, k1, L] using hPhid)
  obtain ⟨Dbounds, _hK, _hK2, _hc1, hm⟩ :=
    exists_bounds_of_curvature_data hQcert hk0c hk1c hk0'c hk1'c
      hper0 hper1 htot0 htot1 hL hd0 hd1 hdsup hkd0 hkd1
      hk0nn hk1nn hk0le hk1le hPhi0 hPhid hnormal hp hq hF
  obtain ⟨Gamma, _hT, _hX, _hetaGamma, _hmGamma, hcost, hvar⟩ :=
    ProfiledInterpolationBounds.exists_path hQcert Dbounds hL
  have hcostEdge : cost Gamma ≤ interpPathCost D.kstar D.kd dsup L eps := by
    calc
      cost Gamma = (∫ t in (0 : ℝ)..1, Dbounds.m t) := hcost
      _ ≤ interpPathCost D.kstar D.kd dsup L eps := Dbounds.hcostIntegral
  have hvarP0 : IsVariableSpeedNormalPath P0
      (costFac D.kstar L eps) D.kstar
      (interpolationG1 D.kstar D.kd L eps)
      (interpolationCgFinal D.kstar D.kd L eps) Gamma :=
    IsVariableSpeedNormalPath.mono_P0 hvar R.P0_pos (by simpa [L, eps] using R.P0_le n)
  have hvarUniform : IsVariableSpeedNormalPath P0 P1 D.kstar G1 Cg Gamma :=
    IsVariableSpeedNormalPath.mono Gamma hvarP0 hkstar
      (by simpa [L, eps] using R.P1_dom n)
      (by simpa [L, eps] using R.G1_dom n)
      (by simpa [L, eps] using R.Cg_dom n)
  refine ⟨Gamma, ?_, hvarUniform⟩
  calc
    cost Gamma ≤ interpPathCost D.kstar D.kd dsup L eps := hcostEdge
    _ ≤ canonicalMarkedDefect D.matchCoefficient defectScale D.kstar D.kd
        D.beta D.Hs n := by simpa [c, L, k0, k1, eps, dsup] using R.cost_dom n
    _ ≤ canonicalMarkedDefect D.matchCoefficient defectScale D.kstar D.kd
        D.beta D.Hs n + eta := by linarith

/-- Family form matching `ApproximatePaperAssemblyResidual.hdefect`. -/
theorem hdefect
    (D : ConstructedConfiguredSequenceWeighted.Data)
    {B : Data → Data} {Q : ℕ → Data}
    {P0 P1 G1 Cg defectScale : ℝ}
    (R : Residual D B Q P0 P1 G1 Cg defectScale) :
    ∀ n : ℕ, ∀ eta : ℝ, 0 < eta →
      ∃ Lambda : NormalPath (Q n) (B (Q (n + 1))),
        cost Lambda ≤ canonicalMarkedDefect D.matchCoefficient defectScale
          D.kstar D.kd D.beta D.Hs n + eta ∧
        IsVariableSpeedNormalPath P0 P1 D.kstar G1 Cg Lambda :=
  fun n eta heta ↦ exists_approx_defect_path D R n eta heta

/-- **Corrected `P1` — linear `Hs` growth.**
`costFac = 2·Hs·exp(rate1Bound) ≥ 2·Hs` (`UniformP1Obstruction`), so no
finite uniform `P1` can dominate `costFac` when `Hs n → ∞`.
The paper's `e_n = (1+L_n)^2·‖κ‖_{L^1}` already carries the polynomial
`L` factor, and `K^n·Hs_n·exp(-β·Hs_n)` is still summable when
`K·exp(-β·ΔH) < 1` (`WeightedSummabilityLinearFactor`). -/
def ResidualLinearP1 (D : ConstructedConfiguredSequenceWeighted.Data) : Prop :=
  ∀ n, InterpolationPathDist.costFac D.kstar (D.Hs n)
    (curvDist
      (modelCurvature (D.model.configs n).yu (D.model.configs n).yu' (D.Hs n))
      (D.model.configs n).kH (D.Hs n)) ≤ 4 * D.Hs n

end ConfiguredApproximateDefectPath
