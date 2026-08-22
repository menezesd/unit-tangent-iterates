import Mathlib
import UnitTangentIterates.RearOwnPathDistIntrinsic
import UnitTangentIterates.FrontVelocitySpeed

/-!
# The path-distance bound for the selected rears, with the constants fixed by
the speed of the path

The constants of the path-distance bound for the selected rears are computed
from a sup bound `E_F` for the front normal velocity along the path.  In
`RearOwnPathDistIntrinsic.pathDist_le_of_front_intrinsic` that bound is
*produced* by a compactness argument over the time window, so the constant of
the conclusion depends on the path through a quantity of which nothing is
known; a Lipschitz bound uniform over a family of paths cannot be read off from
it.

This file states the same bounds with `E_F` supplied instead by the **cost
density of the path**.  The normal speed of a path of fronts *is* the front
normal velocity (`FrontVelocitySpeed.frontNormalVelocity_le_of_link`), so any
bound `M` for the cost density is a bound for `E_F`, and the constant of the
conclusion is then a fixed function of `M`.  Since
`PathMetricSpeed.exists_unitTime_bounded_speed` shows that near-optimal paths
may always be taken with `M` at most `3/2` times their cost, the constant
becomes a function of the pseudodistance of the two curves alone.

* `pathDist_le_of_front_curvature_speed` — the bound of
  `RearOwnPathDistCurvature.pathDist_le_of_front_curvature` with `E_F := M`;
* `pathDist_le_of_front_intrinsic_speed` — the bound of
  `RearOwnPathDistIntrinsic.pathDist_le_of_front_intrinsic` with `E_F := M`,
  the periodicity of the front normal velocity and the derivative of the rear
  period still derived from the front data.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistSpeed

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity RearOwnPathDistIntrinsic FrontVelocitySpeed

variable {F : ℝ → ℝ → ℂ} {Θ δ : ℝ → ℝ → ℝ} {P : ℝ → ℝ}

/-- **The path-distance bound of the selected rears, with the front normal
velocity bounded by the cost density of the path.**  Same statement as
`RearOwnPathDistCurvature.pathDist_le_of_front_curvature`, with the sup bound
`E_F` replaced by any bound `M` for the cost density of the path: the normal
speed of a path of fronts is the front normal velocity, and the cost density
dominates the normal speed. -/
theorem pathDist_le_of_front_curvature_speed {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh M Md Klip CK : ℝ} {Qf' : ℝ → ℝ} {K Kd sf : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
    (hKdper : ∀ t, Function.Periodic (Kd t) (P t))
    (hKdbd : ∀ t s, |Kd t s| ≤ Md)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hPC3 : ContDiff ℝ (3 : ℕ) P) (hKC3 : ContDiff ℝ (3 : ℕ) (uncurry K))
    (hKdC3 : ContDiff ℝ (3 : ℕ) (uncurry Kd))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hetaFper : ∀ t,
      Function.Periodic (frontNormalVelocityAt (partialTime F) Θ δ t) (P t))
    (hlink : ∀ t u, Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u))
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    (hm : ∀ t, Γ.m t ≤ M)
    (hFrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, ∀ s,
      frontNormalVelocityAt (partialTime F) Θ δ t s = 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      ((∀ t, RearBaseDrift.frontBaseDrift (partialTime F) Θ δ t = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
            (M / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
            ((M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
                * (kh / Real.sqrt (1 - kh ^ 2))
              + M / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hEF : ∀ t s, |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ M :=
    fun t s => frontNormalVelocity_le_of_link (δ := δ) Γ hPpos hlink hm t s
  exact RearOwnPathDistCurvature.pathDist_le_of_front_curvature Γ p' (Qf' := Qf') (EF := M)
    hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper hFc4 hΘc4
    hKdper hKdbd hKlip hKtaylor hCK hPC3 hKC3 hKdC3 hsfinv hetaFper hlink hQd hEF hFrest
    hstart

/-- **The same bound with the periodicity of the front normal velocity and the
derivative of the rear period produced.**  Same statement as
`RearOwnPathDistIntrinsic.pathDist_le_of_front_intrinsic`, except that the sup
bound of the front normal velocity is not produced by compactness — with a
constant of which nothing is known — but is any bound `M` for the cost density
of the path. -/
theorem pathDist_le_of_front_intrinsic_speed {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh M Md Klip CK : ℝ} {K Kd sf : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
    (hKdper : ∀ t, Function.Periodic (Kd t) (P t))
    (hKdbd : ∀ t s, |Kd t s| ≤ Md)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hPC3 : ContDiff ℝ (3 : ℕ) P) (hKC3 : ContDiff ℝ (3 : ℕ) (uncurry K))
    (hKdC3 : ContDiff ℝ (3 : ℕ) (uncurry Kd))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hlink : ∀ t u, Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u))
    (hm : ∀ t, Γ.m t ≤ M)
    (hFrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, ∀ s,
      frontNormalVelocityAt (partialTime F) Θ δ t s = 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      ((∀ t, RearBaseDrift.frontBaseDrift (partialTime F) Θ δ t = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
            (M / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
            ((M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
                * (kh / Real.sqrt (1 - kh ^ 2))
              + M / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hstrip : ∀ t s, δ t s ∈ Icc (0 : ℝ) (Real.arcsin kh) := fun t s =>
    ⟨hstrip0 t s, hstrip1 t s⟩
  have hδc4 : ContDiff ℝ (4 : ℕ) (uncurry δ) :=
    SteeringVariablePeriod.contDiff_four_uncurry_delta (K := K) (Kd := Kd) (Pf := P)
      (kap := kh) hkh0 hkh1 hPpos hsteer hstrip hdper hKdper hKdbd hKlip hKtaylor hCK
      hPC3 hKC3 hKdC3
  have hδdiff : Differentiable ℝ (uncurry δ) := hδc4.differentiable (by norm_num)
  have hFdiff : Differentiable ℝ (uncurry F) := hFc4.differentiable (by norm_num)
  have hPdiff : Differentiable ℝ P := hPC3.differentiable (by norm_num)
  -- the periodicity of the front normal velocity
  have hetaFper : ∀ t,
      Function.Periodic (frontNormalVelocityAt (partialTime F) Θ δ t) (P t) :=
    periodic_frontNormalVelocityAt (δ := δ) hFdiff hF hFper hΘper hPdiff
  -- the derivative of the rear period
  have hδ4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry δ) := by norm_num; exact_mod_cast hδc4
  have hdtc : Continuous (uncurry (partialTime δ)) :=
    (contDiff_partialTime_self hδ4).continuous
  have hKcont : Continuous (uncurry K) := hKC3.continuous
  have hlipδ : ∀ a b s, |δ a s - δ b s| ≤ (Klip / Real.sqrt (1 - kh ^ 2)) * |a - b| := by
    intro a b s
    have h := SteeringVariablePeriod.abs_delta_sub_le (kap := kh) (K := K) (Klip := Klip)
      hkh0 hkh1 hKcont hsteer hstrip hKlip a b s
    calc |δ a s - δ b s| ≤ Klip * |a - b| / Real.sqrt (1 - kh ^ 2) := h
      _ = (Klip / Real.sqrt (1 - kh ^ 2)) * |a - b| := by ring
  obtain ⟨Qf', hQd⟩ := exists_hasDerivAt_rearPeriod (δ := δ) (P := P) hδdiff hdtc hlipδ hPdiff
  exact pathDist_le_of_front_curvature_speed Γ p' (Qf' := Qf') (M := M)
    hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper hFc4 hΘc4
    hKdper hKdbd hKlip hKtaylor hCK hPC3 hKC3 hKdC3 hsfinv hetaFper hlink hQd hm hFrest
    hstart

/-- **The same bound with the link replaced by the geometric identification of
the slices.**  Same statement as
`RearOwnPathDistSlices.pathDist_le_of_front_slices`, with the sup bound of the
front normal velocity supplied by a bound `M` for the cost density of the path
instead of being produced by compactness. -/
theorem pathDist_le_of_front_slices_speed {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh M Md Klip CK : ℝ} {K Kd sf : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
    (hKdper : ∀ t, Function.Periodic (Kd t) (P t))
    (hKdbd : ∀ t s, |Kd t s| ≤ Md)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hPC3 : ContDiff ℝ (3 : ℕ) P) (hKC3 : ContDiff ℝ (3 : ℕ) (uncurry K))
    (hKdC3 : ContDiff ℝ (3 : ℕ) (uncurry Kd))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hX : ∀ t u, Γ.X t u = F t (P t * u))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ)))
    (hm : ∀ t, Γ.m t ≤ M)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
            (M / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
            ((M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
                * (kh / Real.sqrt (1 - kh ^ 2))
              + M / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hFdiff : Differentiable ℝ (uncurry F) := hFc4.differentiable (by norm_num)
  have hPdiff : Differentiable ℝ P := hPC3.differentiable (by norm_num)
  have hlink : ∀ t u,
      Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u) :=
    fun t u => RearOwnPathDistSlices.eta_eq_frontNormalVelocity (δ := δ) Γ hFdiff hF hPdiff
      hX hnu t u
  have hFrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, ∀ s,
      frontNormalVelocityAt (partialTime F) Θ δ t s = 0 :=
    fun t ht s => RearOwnPathDistSlices.frontNormalVelocity_eq_zero_of_rest Γ hPpos hlink ht s
  obtain ⟨Phi, hPhi0, hbase, hPhi⟩ :=
    pathDist_le_of_front_intrinsic_speed Γ p' (M := M) hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer
      hstrip0 hstrip1 hdper hK hKc hFper hΘper hFc4 hΘc4 hKdper hKdbd hKlip hKtaylor hCK
      hPC3 hKC3 hKdC3 hsfinv hlink hm hFrest hstart
  refine ⟨Phi, hPhi0, fun h => hbase fun t => ?_, hPhi⟩
  -- the front does not move at the marked point, so the base drift vanishes there
  have hXF : (fun r => Γ.X r 0) = fun r => F r 0 := by
    funext r
    rw [hX r 0, mul_zero]
  have hd := Γ.hasDerivAt_time t 0
  rw [hXF, h t] at hd
  simp only [Complex.ofReal_zero, zero_mul] at hd
  have hFdot : partialTime F t 0 = 0 :=
    (hasDerivAt_partialTime hFdiff t 0).unique hd
  exact RearBaseDrift.frontBaseDrift_eq_zero_of_velocity_zero hFdot

end RearOwnPathDistSpeed
