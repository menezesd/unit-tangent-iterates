import Mathlib
import UnitTangentIterates.RearOwnPathDistNormalized
import UnitTangentIterates.FrontFromPathNormalized
import UnitTangentIterates.RearOwnPathDistSpeed

/-!
# The normalized path-distance bound, with the constants fixed by the speed of
the path

`RearOwnPathDistNormalized.pathDist_le_of_front_normalized` and
`FrontFromPathNormalized.pathDist_le_of_path_normalized` are the forms of the
path-distance bound for the selected rears in which the front data are given on
the normalized circle, so that nothing forces the arclength period to stand
still.  Both produce the sup bound `E_F` of the front normal velocity by
compactness, so the constant of their conclusion depends on the path through a
quantity of which nothing is known.

This file states both with `E_F` supplied by the **cost density of the path**
instead, as `RearOwnPathDistSpeed.lean` does for the arclength forms.  The
constant is then a function of the tube constants, of the duration of the path
and of the speed bound `M` alone; by
`PathMetricSpeed.exists_unitTime_bounded_speed` a near-optimal path may always
be taken of duration one with `M` at most `3/2` times its cost, so all of them
are controlled by the pseudodistance of the two curves.

* `pathDist_le_of_front_normalized_speed`;
* `pathDist_le_of_path_normalized_speed`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistNormalizedSpeed

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  RearOwnPathDistSlices RearOwnPathDistNormalized FrontVelocitySpeed

variable {F : ℝ → ℝ → ℂ} {Θ δ K dn Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The normalized path-distance bound with the front normal velocity bounded
by the cost density of the path.**  Same statement as
`RearOwnPathDistNormalized.pathDist_le_of_front_normalized`, with the sup bound
`E_F` replaced by any bound `M` for the cost density of the path. -/
theorem pathDist_le_of_front_normalized_speed {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {M Md MP CK CP : ℝ} {sf : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hdelta : ∀ t s, δ t s = dn t (s / P t)) (hKeq : ∀ t s, K t s = Kn t (s / P t))
    (hsol : ∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ)
    (hstrip : ∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh))
    (hdnper : ∀ t, Function.Periodic (dn t) 1) (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hKnbd : ∀ t σ, |Kn t σ| ≤ kh) (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md)
    (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
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
  have hle34 : ((3 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (3 : ℕ) ≤ 4)
  have hPC3 : ContDiff ℝ (3 : ℕ) P := hPC4.of_le hle34
  -- the steering data in the arclength
  have hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s :=
    hasDerivAt_delta_arclength hPpos hdelta hKeq hsol
  have hdper : ∀ t, Function.Periodic (δ t) (P t) :=
    periodic_delta_arclength hPpos hdelta hdnper
  have hstrip0 : ∀ t s, 0 ≤ δ t s := fun t s => by rw [hdelta]; exact (hstrip t _).1
  have hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh := fun t s => by
    rw [hdelta]; exact (hstrip t _).2
  have hKbd : ∀ t s, |K t s| ≤ kh := fun t s => by rw [hKeq]; exact hKnbd t _
  have hKc : ∀ t, Continuous (K t) := by
    intro t
    have hfun : K t = fun s => Kn t (s / P t) := funext (hKeq t)
    rw [hfun]
    exact (hKnC3.continuous.comp (continuous_const.prodMk
      (continuous_id.div_const (P t))))
  -- the joint regularity of the steering angle, with no restriction on the period
  have hdnC4 : ContDiff ℝ (4 : ℕ) (uncurry dn) :=
    SteeringNormalizedPeriod.contDiff_four_uncurry_delta (P0 := P0) (P1 := P1) (kap := kh)
      (Md := Md) (MP := MP) (Klip := Klip) (Plip := Plip) (CK := CK) (CP := CP)
      hP0 hkh0 hkh1 hPl hPu hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd
      hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC3 hPdC3 hKnC3 hKdnC3
  have hδc4 : ContDiff ℝ (4 : ℕ) (uncurry δ) := by
    have h := SteeringNormalizedPeriod.contDiff_arclength_of_normalized (n := 4)
      (delta := dn) (Pf := P) hdnC4 hPC4 hPpos
    have heq : (uncurry δ) = uncurry fun t s => dn t (s / P t) := by
      funext x; exact hdelta x.1 x.2
    rw [heq]; exact h
  have hδdiff : Differentiable ℝ (uncurry δ) := hδc4.differentiable (by norm_num)
  have hFdiff : Differentiable ℝ (uncurry F) := hFc4.differentiable (by norm_num)
  have hPdiff : Differentiable ℝ P := hPC4.differentiable (by norm_num)
  -- the link with the fronts and the rest condition
  have hlink : ∀ t u,
      Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u) :=
    fun t u => eta_eq_frontNormalVelocity (δ := δ) Γ hFdiff hF hPdiff hX hnu t u
  have hFrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, ∀ s,
      frontNormalVelocityAt (partialTime F) Θ δ t s = 0 :=
    fun t ht s => frontNormalVelocity_eq_zero_of_rest Γ hPpos hlink ht s
  -- the periodicity of the front normal velocity
  have hetaFper : ∀ t,
      Function.Periodic (frontNormalVelocityAt (partialTime F) Θ δ t) (P t) :=
    periodic_frontNormalVelocityAt (δ := δ) hFdiff hF hFper hΘper hPdiff
  -- its sup bound, from the speed of the path
  have hEF : ∀ t s, |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ M :=
    fun t s => frontNormalVelocity_le_of_link (δ := δ) Γ hPpos hlink hm t s
  -- the derivative of the rear period, from the local Lipschitz bound
  have hδ4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry δ) := by norm_num; exact_mod_cast hδc4
  have hdtc : Continuous (uncurry (partialTime δ)) :=
    (contDiff_partialTime_self hδ4).continuous
  have hPR : ∀ t, |P t| < P1 + 1 := by
    intro t
    rw [abs_of_pos (hPpos t)]
    linarith [hPu t]
  have hR : (0 : ℝ) ≤ P1 + 1 := by
    have : 0 < P1 := lt_of_lt_of_le (hPpos 0) (hPu 0)
    linarith
  have hlipδ : ∀ a b s, |s| ≤ P1 + 1 → |δ a s - δ b s|
      ≤ (SteeringNormalizedPeriod.lipConst P0 P1 kh Klip Plip
          + 2 * P1 * kh * ((P1 + 1) * Plip / P0 ^ 2)) * |a - b| :=
    fun a b s hs => abs_delta_sub_le_of_normalized (R := P1 + 1) hP0 hkh0 hkh1 hR hPl hPu
      hdelta hKnC3.continuous hsol hstrip hKnbd hKnlip hPlip a b s hs
  obtain ⟨Qf', hQd⟩ := exists_hasDerivAt_rearPeriod_local (δ := δ) (P := P)
    (R := P1 + 1) hδdiff hdtc hPR hlipδ hPdiff
  obtain ⟨Phi, hPhi0, hbase, hPhi⟩ :=
    RearOwnPathDistFrontOnly.pathDist_le_of_front_curve Γ p' (Qf' := Qf') (EF := M)
      hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hKbd hKc hFper hΘper hFc4
      hΘc4 hδc4 hsfinv hetaFper hlink hQd hEF hFrest hstart
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

open FrontFromPath in
/-- **The same bound for the canonical front data of the path itself.**  Same
statement as `FrontFromPathNormalized.pathDist_le_of_path_normalized`, with the
sup bound of the front normal velocity supplied by a bound `M` for the cost
density of the path. -/
theorem pathDist_le_of_path_normalized_speed {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {V A : ℝ → ℝ → ℂ} {M Md MP CK CP : ℝ} {sf : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1) (hVper : ∀ t, Periodic (V t) 1)
    (hAper : ∀ t, Periodic (A t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * (V t u / (P t : ℂ)))
    (hdelta : ∀ t s, δ t s = dn t (s / P t))
    (hKeq : ∀ t s, curvOfPath V A P t s = Kn t (s / P t))
    (hsol : ∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ)
    (hstrip : ∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh))
    (hdnper : ∀ t, Function.Periodic (dn t) 1) (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hKnbd : ∀ t σ, |Kn t σ| ≤ kh) (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md)
    (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)))
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath V A P)))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hm : ∀ t, Γ.m t ≤ M)
    (hstart : ∀ u, p'.1 u
      = rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf 0
          (rearArclength (δ 0) (P 0) * u)) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u
          = rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
            (M / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
            ((M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
                * (kh / Real.sqrt (1 - kh ^ 2))
              + M / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hVcont : ∀ t, Continuous (V t) := fun t =>
    continuous_iff_continuousAt.2 fun u => (hA t u).continuousAt
  have hcurvcont : ∀ t, Continuous (curvOfPath V A P t) := fun t =>
    continuous_curvOfPath (hVcont t) (hAcont t)
  refine pathDist_le_of_front_normalized_speed Γ p' (M := M) hP0 hkh0 hkh1 hPl hPu
    hdelta hKeq hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor
    hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 (fun t s => ?_)
    (fun t s => hasDerivAt_angleOfPath (hcurvcont t) s)
    (fun t s => periodic_frontOfPath (hXper t) (hPpos t) s)
    (fun t s => angleOfPath_add_period (hVper t) (hAper t) (hVcont t) (hAcont t) (hPpos t)
      (hturn t) s)
    hFc4 hΘc4 hsfinv (fun t u => ?_) (fun t u => ?_) hm hstart
  · rw [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s]
    exact hasDerivAt_frontOfPath_tangent (hV t) (hPpos t) s
  · have hu : P t * u / P t = u := by have := hPpos t; field_simp
    rw [frontOfPath, hu]
  · have hu : P t * u / P t = u := by have := hPpos t; field_simp
    rw [hnu t u, exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) (P t * u),
      tangentOfPath, hu]

end RearOwnPathDistNormalizedSpeed
