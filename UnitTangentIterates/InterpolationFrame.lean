import Mathlib
import UnitTangentIterates.InterpolationGauge
import UnitTangentIterates.UniformFrameBounds

/-!
# The frame bundle of the curvature-interpolation path

`UnitTangentIterates/InterpolationGauge.lean` reparametrizes the curvature
interpolation of the lemma *Curvature interpolation* by the flow of its
tangential rate, so that the resulting family moves with purely normal
velocity.  The path metric of `UnitTangentIterates/PathMetric.lean` measures the
normal velocity in the **gauge parameter**, and the comparison between the
arclength densities and the gauge densities
(`GaugeDensities.gauge_densities_le`) is expressed through a bundle
`UniformFrameBounds.GaugeFrameData`: two bounds for the arclength derivatives of
the tangential rate `−ξ/v` of the family.

This file builds that bundle for the interpolation.  The curves are unit speed,
so `v ≡ 1` and the rate is the cut-off tangential velocity `−timeCut(a)·ξ_a`;
its two arclength derivatives are computed from the first variations

`∂_sξ = κ_a η`,  `∂_sη = B − κ_a ξ`,  `∂_s(κ_a η) = κ_a' η + κ_a(B − κ_a ξ)`,

and bounded, uniformly in the path parameter, using the cut-off: on its support
`|1 − a| ≤ 2` and `|a| ≤ 2`, so `|κ_a| ≤ 4κ_*` and `|κ_a'| ≤ 4k'`.

Main results:

* `abs_angleShift_le'` : the accumulated curvature difference is bounded by
  `ε = ‖κ¹ − κ⁰‖_{L¹(0,L)}` **everywhere** on the line, by periodicity;
* `abs_xiCut1_le`, `abs_xiCut2_le` : the two arclength derivatives of the
  cut-off tangential velocity are bounded by `rate1Bound` and `rate2Bound`;
* `interpFrame` : the frame bundle of the interpolation;
* `gaugeRate_interpFrame` : its tangential rate is the gauge field of
  `InterpolationGauge.lean`, so the flow constructed there is its gauge flow.
-/

noncomputable section

open Real MeasureTheory Set

namespace InterpolationFrame

open CurvatureInterpolation InterpolationNormal InterpolationEstimate
  InterpolationSecondOrder InterpolationGauge UniformFrameBounds

variable {k0 k1 k0' k1' : ℝ → ℝ} {θ₀ L : ℝ}

/-! ### The accumulated curvature difference, everywhere on the line -/

/-- `|B(s)| ≤ ε` for every `s`: the accumulated curvature difference is
`L`-periodic because both curvatures have total turning `π`. -/
theorem abs_angleShift_le' (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L) (s : ℝ) :
    |angleShift k0 k1 s| ≤ curvDist k0 k1 L := by
  obtain ⟨y, hy, hval⟩ :=
    (angleShift_periodic hk0 hk1 hper0 hper1 htot0 htot1).exists_mem_Ico₀ hL s
  rw [hval]
  exact abs_angleShift_le hk0 hk1 ⟨hy.1, hy.2.le⟩

/-! ### The cut-off tangential velocity and its two arclength derivatives -/

/-- The tangential rate of the interpolation, cut off in the path parameter:
`ξ` of the bundle. -/
def xiCut (k0 k1 : ℝ → ℝ) (θ₀ L : ℝ) (a x : ℝ) : ℝ :=
  timeCut a * tangentVel k0 k1 θ₀ L a x

/-- Its first arclength derivative, `∂_sξ = κ_a η`. -/
def xiCut1 (k0 k1 : ℝ → ℝ) (θ₀ L : ℝ) (a x : ℝ) : ℝ :=
  timeCut a * (kappaInterp k0 k1 a x * normalVel k0 k1 θ₀ L a x)

/-- Its second arclength derivative, `∂_s²ξ = κ_a' η + κ_a ∂_sη`. -/
def xiCut2 (k0 k1 k0' k1' : ℝ → ℝ) (θ₀ L : ℝ) (a x : ℝ) : ℝ :=
  timeCut a * (((1 - a) * k0' x + a * k1' x) * normalVel k0 k1 θ₀ L a x
    + kappaInterp k0 k1 a x * normalVelDeriv k0 k1 θ₀ L a x)

/-- The bound for the first arclength derivative of the tangential rate. -/
def rate1Bound (kstar L eps : ℝ) : ℝ := 4 * kstar * ((3/2) * L * eps)

/-- The bound for the second arclength derivative of the tangential rate. -/
def rate2Bound (kstar kd L eps : ℝ) : ℝ :=
  4 * kd * ((3/2) * L * eps) + 4 * kstar * (eps + 4 * kstar * ((3/2) * L * eps))

theorem rate1Bound_nonneg {kstar L eps : ℝ} (hk : 0 ≤ kstar) (hL : 0 ≤ L) (he : 0 ≤ eps) :
    0 ≤ rate1Bound kstar L eps := by
  unfold rate1Bound; positivity

theorem rate2Bound_nonneg {kstar kd L eps : ℝ} (hk : 0 ≤ kstar) (hkd : 0 ≤ kd)
    (hL : 0 ≤ L) (he : 0 ≤ eps) : 0 ≤ rate2Bound kstar kd L eps := by
  unfold rate2Bound; positivity

theorem hasDerivAt_xiCut (hk0 : Continuous k0) (hk1 : Continuous k1) (a x : ℝ) :
    HasDerivAt (xiCut k0 k1 θ₀ L a) (xiCut1 k0 k1 θ₀ L a x) x :=
  (hasDerivAt_tangentVel (θ₀ := θ₀) (L := L) hk0 hk1 a x).const_mul (timeCut a)

theorem hasDerivAt_xiCut1 (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r) (a x : ℝ) :
    HasDerivAt (xiCut1 k0 k1 θ₀ L a) (xiCut2 k0 k1 k0' k1' θ₀ L a x) x := by
  have hk := hasDerivAt_kappaInterp (k0' := k0') (k1' := k1') hd0 hd1 a x
  have he := hasDerivAt_normalVel (θ₀ := θ₀) (L := L) hk0 hk1 a x
  exact (hk.mul he).const_mul (timeCut a)

/-- The interpolated curvature is bounded by `4κ_*` on the support of the
cut-off. -/
theorem abs_kappaInterp_le_of_cut {k0 k1 : ℝ → ℝ} {kstar a : ℝ} (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar)
    (ha0 : -1 ≤ a) (ha1 : a ≤ 2) (x : ℝ) :
    |kappaInterp k0 k1 a x| ≤ 4 * kstar := by
  have h1t : |1 - a| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hts : |a| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have h0 : |(1 - a) * k0 x| ≤ 2 * kstar := by
    rw [abs_mul, abs_of_nonneg (hk0nn x)]
    exact mul_le_mul h1t (hk0le x) (hk0nn x) (by norm_num)
  have h1 : |a * k1 x| ≤ 2 * kstar := by
    rw [abs_mul, abs_of_nonneg (hk1nn x)]
    exact mul_le_mul hts (hk1le x) (hk1nn x) (by norm_num)
  calc |kappaInterp k0 k1 a x| ≤ |(1 - a) * k0 x| + |a * k1 x| := by
        simpa [kappaInterp] using abs_add_le ((1 - a) * k0 x) (a * k1 x)
    _ ≤ 2 * kstar + 2 * kstar := add_le_add h0 h1
    _ = 4 * kstar := by ring

/-! ### The uniform bounds -/

section Bounds

variable (hk0 : Continuous k0) (hk1 : Continuous k1)
  (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
  (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
  (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)

include hk0 hk1 hper0 hper1 htot0 htot1 hL

/-- The first arclength derivative of the cut-off tangential rate is bounded,
uniformly in the path parameter. -/
theorem abs_xiCut1_le {kstar : ℝ} (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) (a x : ℝ) :
    |xiCut1 k0 k1 θ₀ L a x| ≤ rate1Bound kstar L (curvDist k0 k1 L) := by
  have h := abs_gaugeFieldDeriv_le (θ₀ := θ₀) (L := L) hk0 hk1 hper0 hper1 htot0 htot1 hL
    hk0nn hk1nn hk0le hk1le a x
  rw [abs_neg] at h
  simpa [xiCut1, rate1Bound] using h

/-- The arclength derivative of the normal velocity is bounded on the support of
the cut-off. -/
theorem abs_normalVelDeriv_le_of_cut {kstar a : ℝ} (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar)
    (ha0 : -1 ≤ a) (ha1 : a ≤ 2) (x : ℝ) :
    |normalVelDeriv k0 k1 θ₀ L a x|
      ≤ curvDist k0 k1 L + 4 * kstar * ((3/2) * L * curvDist k0 k1 L) := by
  have hB := abs_angleShift_le' hk0 hk1 hper0 hper1 htot0 htot1 hL x
  have hxi := abs_tangentVel_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL a x
  have hkap := abs_kappaInterp_le_of_cut hk0nn hk1nn hk0le hk1le ha0 ha1 x
  have hkstar : 0 ≤ kstar := le_trans (hk0nn 0) (hk0le 0)
  have hprod : |kappaInterp k0 k1 a x * tangentVel k0 k1 θ₀ L a x|
      ≤ (4 * kstar) * ((3/2) * L * curvDist k0 k1 L) := by
    rw [abs_mul]
    exact mul_le_mul hkap hxi (abs_nonneg _) (by positivity)
  calc |normalVelDeriv k0 k1 θ₀ L a x|
      ≤ |angleShift k0 k1 x| + |kappaInterp k0 k1 a x * tangentVel k0 k1 θ₀ L a x| := by
        simpa [normalVelDeriv, sub_eq_add_neg] using
          abs_add_le (angleShift k0 k1 x)
            (-(kappaInterp k0 k1 a x * tangentVel k0 k1 θ₀ L a x))
    _ ≤ curvDist k0 k1 L + 4 * kstar * ((3/2) * L * curvDist k0 k1 L) := add_le_add hB hprod

/-- The second arclength derivative of the cut-off tangential rate is bounded,
uniformly in the path parameter. -/
theorem abs_xiCut2_le {kstar kd : ℝ} (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd) (a x : ℝ) :
    |xiCut2 k0 k1 k0' k1' θ₀ L a x| ≤ rate2Bound kstar kd L (curvDist k0 k1 L) := by
  have heps : 0 ≤ curvDist k0 k1 L := integral_abs_sub_nonneg hk0 hk1 hL.le
  have hkstar : 0 ≤ kstar := le_trans (hk0nn 0) (hk0le 0)
  have hkd : 0 ≤ kd := le_trans (abs_nonneg _) (hkd0 0)
  have hbound : 0 ≤ rate2Bound kstar kd L (curvDist k0 k1 L) :=
    rate2Bound_nonneg hkstar hkd hL.le heps
  rcases lt_or_ge a (-1) with ha | ha
  · rw [xiCut2, timeCut_eq_zero_of_lt ha]
    simpa using hbound
  rcases lt_or_ge 2 a with ha' | ha'
  · rw [xiCut2, timeCut_eq_zero_of_gt ha']
    simpa using hbound
  have hcut : |timeCut a| ≤ 1 := by
    rw [abs_of_nonneg (timeCut_nonneg a)]
    exact timeCut_le_one a
  have heta := abs_normalVel_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL a x
  have hkap := abs_kappaInterp_le_of_cut hk0nn hk1nn hk0le hk1le ha ha' x
  have hetas := abs_normalVelDeriv_le_of_cut (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL
    hk0nn hk1nn hk0le hk1le ha ha' x
  have hkder : |(1 - a) * k0' x + a * k1' x| ≤ 4 * kd := by
    have h1t : |1 - a| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    have hts : |a| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    have h0 : |(1 - a) * k0' x| ≤ 2 * kd := by
      rw [abs_mul]
      exact mul_le_mul h1t (hkd0 x) (abs_nonneg _) (by norm_num)
    have h1 : |a * k1' x| ≤ 2 * kd := by
      rw [abs_mul]
      exact mul_le_mul hts (hkd1 x) (abs_nonneg _) (by norm_num)
    calc |(1 - a) * k0' x + a * k1' x| ≤ |(1 - a) * k0' x| + |a * k1' x| :=
          abs_add_le _ _
      _ ≤ 2 * kd + 2 * kd := add_le_add h0 h1
      _ = 4 * kd := by ring
  have hterm1 : |((1 - a) * k0' x + a * k1' x) * normalVel k0 k1 θ₀ L a x|
      ≤ (4 * kd) * ((3/2) * L * curvDist k0 k1 L) := by
    rw [abs_mul]
    exact mul_le_mul hkder heta (abs_nonneg _) (by positivity)
  have hterm2 : |kappaInterp k0 k1 a x * normalVelDeriv k0 k1 θ₀ L a x|
      ≤ (4 * kstar) * (curvDist k0 k1 L + 4 * kstar * ((3/2) * L * curvDist k0 k1 L)) := by
    rw [abs_mul]
    exact mul_le_mul hkap hetas (abs_nonneg _) (by positivity)
  calc |xiCut2 k0 k1 k0' k1' θ₀ L a x|
      = |timeCut a| * |((1 - a) * k0' x + a * k1' x) * normalVel k0 k1 θ₀ L a x
          + kappaInterp k0 k1 a x * normalVelDeriv k0 k1 θ₀ L a x| := by
        rw [xiCut2, abs_mul]
    _ ≤ 1 * (((4 * kd) * ((3/2) * L * curvDist k0 k1 L))
          + (4 * kstar) * (curvDist k0 k1 L + 4 * kstar * ((3/2) * L * curvDist k0 k1 L))) := by
        refine mul_le_mul hcut ?_ (abs_nonneg _) zero_le_one
        exact le_trans (abs_add_le _ _) (add_le_add hterm1 hterm2)
    _ = rate2Bound kstar kd L (curvDist k0 k1 L) := by rw [rate2Bound]; ring

end Bounds

/-! ### The frame bundle -/

/-- **The frame bundle of the curvature-interpolation path.**  The curves are
unit speed, so the tangential rate is the cut-off tangential velocity, whose two
arclength derivatives are bounded by `rate1Bound` and `rate2Bound`. -/
def interpFrame (k0 k1 k0' k1' : ℝ → ℝ) (θ₀ L kstar kd : ℝ)
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd) : GaugeFrameData where
  xi := xiCut k0 k1 θ₀ L
  xi1 := xiCut1 k0 k1 θ₀ L
  xi2 := xiCut2 k0 k1 k0' k1' θ₀ L
  v := fun _ _ => 1
  v1 := fun _ _ => 0
  v2 := fun _ _ => 0
  rateLip := rate1Bound kstar L (curvDist k0 k1 L)
  rateBound2 := rate2Bound kstar kd L (curvDist k0 k1 L)
  hxi := fun a x => hasDerivAt_xiCut hk0 hk1 a x
  hxi1 := fun a x => hasDerivAt_xiCut1 hk0 hk1 hd0 hd1 a x
  hv := fun _ x => hasDerivAt_const x 1
  hv1 := fun _ x => hasDerivAt_const x 0
  hvne := fun _ _ => one_ne_zero
  hxic := by
    have hcut : Continuous fun p : ℝ × ℝ => timeCut p.1 := continuous_timeCut.comp continuous_fst
    exact hcut.mul (continuous_uncurry_tangentVel (θ₀ := θ₀) (L := L) hk0 hk1)
  hxi1c := by
    have hcut : Continuous fun p : ℝ × ℝ => timeCut p.1 := continuous_timeCut.comp continuous_fst
    exact hcut.mul ((continuous_uncurry_kappaInterp hk0 hk1).mul
      (continuous_uncurry_normalVel (θ₀ := θ₀) (L := L) hk0 hk1))
  hxi2c := by
    have hcut : Continuous fun p : ℝ × ℝ => timeCut p.1 := continuous_timeCut.comp continuous_fst
    have hkd : Continuous fun p : ℝ × ℝ => (1 - p.1) * k0' p.2 + p.1 * k1' p.2 := by
      fun_prop
    exact hcut.mul ((hkd.mul (continuous_uncurry_normalVel (θ₀ := θ₀) (L := L) hk0 hk1)).add
      ((continuous_uncurry_kappaInterp hk0 hk1).mul
        (continuous_uncurry_normalVelDeriv (θ₀ := θ₀) (L := L) hk0 hk1)))
  hvc := continuous_const
  hv1c := continuous_const
  hv2c := continuous_const
  hrate1 := by
    intro a x
    have h := abs_xiCut1_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL
      hk0nn hk1nn hk0le hk1le a x
    simpa [GaugeRate.gaugeRate1] using h
  hrate2 := by
    intro a x
    have h := abs_xiCut2_le (θ₀ := θ₀) hk0 hk1 hper0 hper1 htot0 htot1 hL
      hk0nn hk1nn hk0le hk1le hkd0 hkd1 a x
    simpa [GaugeRate.gaugeRate2] using h

section FrameLemmas

variable (k0 k1 k0' k1' : ℝ → ℝ) (θ₀ L kstar kd : ℝ)
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)
    (hd0 : ∀ r, HasDerivAt k0 (k0' r) r) (hd1 : ∀ r, HasDerivAt k1 (k1' r) r)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)

@[simp] theorem interpFrame_xi :
    (interpFrame k0 k1 k0' k1' θ₀ L kstar kd hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL
      hd0 hd1 hk0nn hk1nn hk0le hk1le hkd0 hkd1).xi = xiCut k0 k1 θ₀ L := rfl

@[simp] theorem interpFrame_v :
    (interpFrame k0 k1 k0' k1' θ₀ L kstar kd hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL
      hd0 hd1 hk0nn hk1nn hk0le hk1le hkd0 hkd1).v = fun _ _ => 1 := rfl

@[simp] theorem interpFrame_rateLip :
    (interpFrame k0 k1 k0' k1' θ₀ L kstar kd hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL
        hd0 hd1 hk0nn hk1nn hk0le hk1le hkd0 hkd1).rateLip
      = rate1Bound kstar L (curvDist k0 k1 L) := rfl

@[simp] theorem interpFrame_rateBound2 :
    (interpFrame k0 k1 k0' k1' θ₀ L kstar kd hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL
        hd0 hd1 hk0nn hk1nn hk0le hk1le hkd0 hkd1).rateBound2
      = rate2Bound kstar kd L (curvDist k0 k1 L) := rfl

end FrameLemmas

/-- The tangential rate of the bundle is the gauge field of
`InterpolationGauge.lean`: the flow constructed there is the gauge flow of the
bundle. -/
theorem gaugeRate_interpFrame (a x : ℝ) :
    GaugeRate.gaugeRate (xiCut k0 k1 θ₀ L) (fun _ _ => (1:ℝ)) a x
      = gaugeField k0 k1 θ₀ L a x := by
  simp [GaugeRate.gaugeRate, xiCut, gaugeField]

/-- The tangential rate of the bundle is `2L`-periodic in the arclength. -/
theorem periodic_xiCut (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (a : ℝ) :
    Function.Periodic (xiCut k0 k1 θ₀ L a) (2 * L) := by
  have hper := tangentVel_periodic (θ₀ := θ₀) (L := L) hk0 hk1 hper0 hper1 htot0 htot1 a
  intro s
  simp only [xiCut]
  rw [show s + 2 * L = s + L + L by ring, hper (s + L), hper s]

end InterpolationFrame
