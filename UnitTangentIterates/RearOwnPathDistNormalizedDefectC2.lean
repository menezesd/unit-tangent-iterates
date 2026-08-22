import Mathlib
import UnitTangentIterates.RearOwnPathDistNormalized
import UnitTangentIterates.RearOwnPathDistFrontOnlyDefectC2

/-!
# The path pseudodistance in the normalized parameter, together with the C²
defect of its gauge marking

The two assemblies of `RearOwnPathDistNormalized.lean` restated with the extra
conclusions about the gauge marking `Φ` in which the pseudodistance is read: it
fixes the base point, reads exactly one rear period, deviates from the affine
marking of the terminal period by at most `2 P₁ κ̂/(1 − κ̂²) · cost Γ`, and leaves
the terminal marked curve within `markingC2Bound` of the marked reference curve
`b` in the `C²` metric.  The extra
hypothesis is the geometric one already used to fix the base point in the
original statements: the path does not move at its marked point, `η(t, 0) = 0`.

Main results: `pathDist_and_distC2_le_of_front_normalized`,
`exists_sf_pathDist_and_distC2_le_of_front_normalized`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistNormalizedDefectC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  RearOwnPathDistSlices RearOwnPathDistNormalized MarkingDeviationC2 MarkingFlowDefectC2
  RearOwnTangentialCostC2

variable {F : ℝ → ℝ → ℂ} {Θ δ K dn Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The path pseudodistance of the selected rears in the normalized parameter,
together with the C² defect of its gauge marking.**
`RearOwnPathDistNormalized.pathDist_le_of_front_normalized` with the extra
conclusions about the marking. -/
theorem pathDist_and_distC2_le_of_front_normalized {p q : Data} (Γ : NormalPath p q) (p' b : Data)
    {Md MP CK CP : ℝ} {sf : ℝ → ℝ → ℝ}
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
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u))
    (hmark : ∀ t, Γ.eta t 0 = 0)
    -- the terminal curve, a member of the tube tracing the terminal slice
    {cq kminq dltq kb kL : ℝ} {Θb kb' : ℝ → ℝ}
    (hcq : 0 < cq) (hb : IsTubeMember cq kminq dltq b)
    (hperimb : perim b = rearArclength (δ Γ.T) (P Γ.T))
    (hevb : ∀ x, ev b x = rearOwn F Θ δ sf Γ.T x)
    (hevd : ∀ s, HasDerivAt (ev b) (Complex.exp (Complex.I * (Θb s : ℂ))) s)
    (hΘb : ∀ s, HasDerivAt Θb (kb' s) s) (hkbd : ∀ s, |kb' s| ≤ kb)
    (hklip : ∀ s t, |kb' s - kb' t| ≤ kL * |s - t|) :
    ∃ EF : ℝ, 0 ≤ EF ∧
      (∀ t s, |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ EF) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
        (∀ t, Phi t 0 = 0) ∧ (∀ t, Phi t 1 = rearArclength (δ t) (P t)) ∧
        (∀ u t, HasDerivAt (fun r => Phi r u)
          (-frameTangential (partialTime (rearOwn F Θ δ sf)) (rearOwnAngle Θ δ sf) t
            (Phi t u)) t) ∧
        (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
          ≤ 2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ) ∧
        (∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
          (∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u) → (∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) →
          dist q' b ≤ markingC2Bound (2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ)
            (flowDefectC1Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ))
            (flowDefectC2Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ)
              (gaugeGrowth2 kh * cost Γ))
            (rearArclength (δ Γ.T) (P Γ.T)) kb kL) ∧
        ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
          pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
              (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
              ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                  * (kh / Real.sqrt (1 - kh ^ 2))
                + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
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
  -- the periodicity of the front normal velocity and its sup bound
  have hetaFper : ∀ t,
      Function.Periodic (frontNormalVelocityAt (partialTime F) Θ δ t) (P t) :=
    periodic_frontNormalVelocityAt (δ := δ) hFdiff hF hFper hΘper hPdiff
  have hF4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry F) := by norm_num; exact_mod_cast hFc4
  have hΘ3 : ContDiff ℝ (3 : ℕ) (uncurry Θ) := hΘc4.of_le hle34
  have hFdot3 : ContDiff ℝ (3 : ℕ) (uncurry (partialTime F)) := contDiff_partialTime_self hF4
  have hetaC3 : ContDiff ℝ (3 : ℕ)
      (uncurry (frontNormalVelocityAt (partialTime F) Θ δ)) :=
    contDiff_frontNormalVelocityAt hFdot3 hΘ3
  obtain ⟨EF, hEF0, hEF⟩ := exists_bound_of_periodic_rest (P := P)
    (eta := frontNormalVelocityAt (partialTime F) Θ δ) hetaC3.continuous Γ.T_pos
    hPpos hPu hetaFper hFrest
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
  -- the front does not move at the marked point, so the base drift vanishes there
  have hdrift : ∀ t, RearBaseDrift.frontBaseDrift (partialTime F) Θ δ t = 0 := by
    intro t
    have hXF : (fun r => Γ.X r 0) = fun r => F r 0 := by
      funext r
      rw [hX r 0, mul_zero]
    have hd := Γ.hasDerivAt_time t 0
    rw [hXF, hmark t] at hd
    simp only [Complex.ofReal_zero, zero_mul] at hd
    have hFdot : partialTime F t 0 = 0 :=
      (hasDerivAt_partialTime hFdiff t 0).unique hd
    exact RearBaseDrift.frontBaseDrift_eq_zero_of_velocity_zero hFdot
  obtain ⟨Phi, hPhi0, hbase, hone, hflow, hdefect, hdistC2, hPhi⟩ :=
    RearOwnPathDistFrontOnlyDefectC2.pathDist_and_distC2_le_of_front_curve Γ p' b
      (Qf' := Qf') (EF := EF)
      hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hKbd hKc hFper hΘper hFc4
      hΘc4 hδc4 hsfinv hetaFper hlink hQd hEF hFrest hstart hdrift
    hcq hb hperimb hevb hevd hΘb hkbd hklip
  exact ⟨EF, hEF0, hEF, Phi, hPhi0, hbase, hone, hflow, hdefect, hdistC2, hPhi⟩

/-- **The same, with the change of variable from the rear to the front arclength
produced rather than assumed.**
`RearOwnPathDistNormalized.exists_sf_pathDist_le_of_front_normalized` with the
extra conclusions about the marking. -/
theorem exists_sf_pathDist_and_distC2_le_of_front_normalized {p q : Data} (Γ : NormalPath p q)
    {Md MP CK CP : ℝ}
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
    (hX : ∀ t u, Γ.X t u = F t (P t * u))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ)))
    (hmark : ∀ t, Γ.eta t 0 = 0) :
    ∃ sf : ℝ → ℝ → ℝ, (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∀ (p' b : Data) (cq kminq dltq kb kL : ℝ) (Θb kb' : ℝ → ℝ),
        (∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) →
        0 < cq → IsTubeMember cq kminq dltq b →
        perim b = rearArclength (δ Γ.T) (P Γ.T) →
        (∀ x, ev b x = rearOwn F Θ δ sf Γ.T x) →
        (∀ s, HasDerivAt (ev b) (Complex.exp (Complex.I * (Θb s : ℂ))) s) →
        (∀ s, HasDerivAt Θb (kb' s) s) → (∀ s, |kb' s| ≤ kb) →
        (∀ s t, |kb' s - kb' t| ≤ kL * |s - t|) →
        ∃ EF : ℝ, 0 ≤ EF ∧
          (∀ t s, |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ EF) ∧
          ∃ Phi : ℝ → ℝ → ℝ,
            (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
            (∀ t, Phi t 0 = 0) ∧ (∀ t, Phi t 1 = rearArclength (δ t) (P t)) ∧
            (∀ u t, HasDerivAt (fun r => Phi r u)
              (-frameTangential (partialTime (rearOwn F Θ δ sf)) (rearOwnAngle Θ δ sf) t
                (Phi t u)) t) ∧
            (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
              ≤ 2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ) ∧
            (∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
              (∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u) → (∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) →
              dist q' b ≤ markingC2Bound (2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ)
                (flowDefectC1Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ))
                (flowDefectC2Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ)
                  (gaugeGrowth2 kh * cost Γ))
                (rearArclength (δ Γ.T) (P Γ.T)) kb kL) ∧
            ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
              pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
                  (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                  ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                      * (kh / Real.sqrt (1 - kh ^ 2))
                    + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
                (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hle34 : ((3 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (3 : ℕ) ≤ 4)
  have hPC3 : ContDiff ℝ (3 : ℕ) P := hPC4.of_le hle34
  have hstrip0 : ∀ t s, 0 ≤ δ t s := fun t s => by rw [hdelta]; exact (hstrip t _).1
  have hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh := fun t s => by
    rw [hdelta]; exact (hstrip t _).2
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
  obtain ⟨sf, hsf⟩ := SelectedChangeOfVariable.exists_sf_family (kap := kh) hkh0 hkh1
    (hδc4.continuous) hstrip0 hstrip1
  refine ⟨sf, hsf, ?_⟩
  intro p' b cq kminq dltq kb kL Θb kb' hstart hcq hb hperimb hevb hevd hΘb hkbd hklip
  exact pathDist_and_distC2_le_of_front_normalized Γ p' b (Md := Md) (MP := MP) (CK := CK) (CP := CP)
    hP0 hkh0 hkh1 hPl hPu hdelta hKeq hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd
    hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hF hΘ hFper
    hΘper hFc4 hΘc4 hsf hX hnu hstart hmark
    hcq hb hperimb hevb hevd hΘb hkbd hklip

end RearOwnPathDistNormalizedDefectC2
