import Mathlib
import UnitTangentIterates.RearOwnPathDistIntrinsic
import UnitTangentIterates.RearOwnPathDistCurvatureDefectC2

/-!
# The path pseudodistance with the last auxiliary data removed, together with the
C² defect of its gauge marking

`RearOwnPathDistIntrinsic.pathDist_le_of_front_intrinsic` produces the
periodicity of the front normal velocity, its sup bound and the derivative of
the rear period from the front data alone.  This file restates it with the extra
conclusions about the gauge marking `Φ` in which the pseudodistance is read —
`Φ` fixes the base point, reads exactly one rear period, deviates from the affine
marking of the terminal period by at most `2 P₁ κ̂/(1 − κ̂²) · cost Γ`, and leaves
the terminal marked curve within `markingC2Bound` of the marked reference curve
`b` in the `C²` metric — under the single extra hypothesis that the base drift of
the front vanishes.

Main result: `pathDist_and_distC2_le_of_front_intrinsic`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistIntrinsicDefectC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2

variable {F : ℝ → ℝ → ℂ} {Θ δ : ℝ → ℝ → ℝ} {P : ℝ → ℝ}

/-- **The path pseudodistance of the selected rears with the last auxiliary data
removed, together with the C² defect of its gauge marking.**
`RearOwnPathDistIntrinsic.pathDist_le_of_front_intrinsic` with the extra
conclusions about the marking. -/
theorem pathDist_and_distC2_le_of_front_intrinsic {p q : Data} (Γ : NormalPath p q) (p' b : Data)
    {P0 P1 kh Md Klip CK : ℝ} {K Kd sf : ℝ → ℝ → ℝ}
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
    (hFrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, ∀ s,
      frontNormalVelocityAt (partialTime F) Θ δ t s = 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u))
    (hdrift : ∀ t, RearBaseDrift.frontBaseDrift (partialTime F) Θ δ t = 0)
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
  -- its sup bound
  have hF4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry F) := by norm_num; exact_mod_cast hFc4
  have hle34 : ((3 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (3 : ℕ) ≤ 4)
  have hΘ3 : ContDiff ℝ (3 : ℕ) (uncurry Θ) := hΘc4.of_le hle34
  have hFdot3 : ContDiff ℝ (3 : ℕ) (uncurry (partialTime F)) := contDiff_partialTime_self hF4
  have hetaC3 : ContDiff ℝ (3 : ℕ)
      (uncurry (frontNormalVelocityAt (partialTime F) Θ δ)) :=
    contDiff_frontNormalVelocityAt hFdot3 hΘ3
  obtain ⟨EF, hEF0, hEF⟩ := exists_bound_of_periodic_rest (P := P)
    (eta := frontNormalVelocityAt (partialTime F) Θ δ) hetaC3.continuous Γ.T_pos
    hPpos hPu hetaFper hFrest
  -- the derivative of the rear period
  have hδ4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry δ) := by norm_num; exact_mod_cast hδc4
  have hdtc : Continuous (uncurry (partialTime δ)) :=
    (contDiff_partialTime_self hδ4).continuous
  have hKcont : Continuous (uncurry K) := hKC3.continuous
  have hlipδ : ∀ a b s, |δ a s - δ b s| ≤ (Klip / Real.sqrt (1 - kh ^ 2)) * |a - b| := by
    intro a b s
    have := SteeringVariablePeriod.abs_delta_sub_le (kap := kh) (K := K) (Klip := Klip)
      hkh0 hkh1 hKcont hsteer hstrip hKlip a b s
    calc |δ a s - δ b s| ≤ Klip * |a - b| / Real.sqrt (1 - kh ^ 2) := this
      _ = (Klip / Real.sqrt (1 - kh ^ 2)) * |a - b| := by ring
  obtain ⟨Qf', hQd⟩ := exists_hasDerivAt_rearPeriod (δ := δ) (P := P) hδdiff hdtc hlipδ hPdiff
  obtain ⟨Phi, hPhi0, hbase, hone, hflow, hdefect, hdistC2, hPhi⟩ :=
    RearOwnPathDistCurvatureDefectC2.pathDist_and_distC2_le_of_front_curvature Γ p' b
      (Qf' := Qf') (EF := EF)
      hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper hFc4 hΘc4
      hKdper hKdbd hKlip hKtaylor hCK hPC3 hKC3 hKdC3 hsfinv hetaFper hlink hQd hEF hFrest
      hstart hdrift
    hcq hb hperimb hevb hevd hΘb hkbd hklip
  exact ⟨EF, hEF0, hEF, Phi, hPhi0, hbase, hone, hflow, hdefect, hdistC2, hPhi⟩

end RearOwnPathDistIntrinsicDefectC2
