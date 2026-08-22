import Mathlib
import UnitTangentIterates.InterpolationEstimate

/-!
# The second-order density of the curvature-interpolation path

The lemma *Curvature interpolation* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* bounds the three functionals `W`, `S₀`, `S₁` of the
interpolating path (`UnitTangentIterates/InterpolationEstimate.lean`).  The path
metric of `UnitTangentIterates/PathMetric.lean` also asks for the second-order
density `S₂`, which the interpolation lemma does not control: bounding
`∂_s²η` needs one derivative of the two curvatures.

This file supplies it.  Besides the normal first variation
`∂_sη = B − κ_t ξ` proved in `InterpolationEstimate.lean`, the tangential one

`∂_sξ = κ_t η`

holds for the same path (`hasDerivAt_tangentVel`), so differentiating once more

`∂_s²η = (κ¹ − κ⁰) − κ_t' ξ − κ_t² η`.

With `|κ¹ − κ⁰| ≤ d`, `|κ_t'| ≤ k'` and `κ_t ≤ κ_*`, the bounds
`|η|, |ξ| ≤ (3/2)Lε` of the interpolation give

`|∂_s²η| ≤ d + (k' + κ_*²)(3/2)Lε`,

everywhere on the line, and the corresponding functional obeys the same bound.

Main results:

* `hasDerivAt_tangentVel` : the tangential first variation `∂_sξ = κ_t η`;
* `hasDerivAt_normalVelDeriv` : `∂_s²η = (κ¹ − κ⁰) − κ_t' ξ − κ_t² η`;
* `abs_normalVelSecondDeriv_le` : the sup bound, everywhere on the line;
* `S2norm_le`, `integral_S2norm_le` : the bound for the second-order density of
  the path.
-/

noncomputable section

open Real MeasureTheory intervalIntegral

namespace InterpolationSecondOrder

open CurvatureInterpolation InterpolationNormal InterpolationEstimate

variable {k0 k1 k0' k1' : ℝ → ℝ} {θ₀ L : ℝ}

/-- **The tangential first variation** `∂_s ξ = κ_t η` of the interpolating
path. -/
theorem hasDerivAt_tangentVel (hk0 : Continuous k0) (hk1 : Continuous k1) (t s : ℝ) :
    HasDerivAt (tangentVel k0 k1 θ₀ L t)
      (kappaInterp k0 k1 t s * normalVel k0 k1 θ₀ L t s) s := by
  have hθ : HasDerivAt (tangentAngle (kappaInterp k0 k1 t) θ₀) (kappaInterp k0 k1 t s) s :=
    hasDerivAt_tangentAngle (continuous_kappaInterp hk0 hk1) s
  have hV := hasDerivAt_interpVelocity_arclength (θ₀ := θ₀) (L := L) hk0 hk1 t s
  have hre : HasDerivAt (fun x => (interpVelocity k0 k1 θ₀ L t x).re)
      (Complex.I * (angleShift k0 k1 s : ℂ)
        * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ s)).re s := by
    simpa using (Complex.reCLM.hasFDerivAt.comp s hV.hasFDerivAt).hasDerivAt
  have him : HasDerivAt (fun x => (interpVelocity k0 k1 θ₀ L t x).im)
      (Complex.I * (angleShift k0 k1 s : ℂ)
        * tau (tangentAngle (kappaInterp k0 k1 t) θ₀ s)).im s := by
    simpa using (Complex.imCLM.hasFDerivAt.comp s hV.hasFDerivAt).hasDerivAt
  have hcos : HasDerivAt (fun x => Real.cos (tangentAngle (kappaInterp k0 k1 t) θ₀ x))
      (-Real.sin (tangentAngle (kappaInterp k0 k1 t) θ₀ s) * kappaInterp k0 k1 t s) s :=
    (Real.hasDerivAt_cos _).comp s hθ
  have hsin : HasDerivAt (fun x => Real.sin (tangentAngle (kappaInterp k0 k1 t) θ₀ x))
      (Real.cos (tangentAngle (kappaInterp k0 k1 t) θ₀ s) * kappaInterp k0 k1 t s) s :=
    (Real.hasDerivAt_sin _).comp s hθ
  have h := (hre.mul hcos).add (him.mul hsin)
  convert h using 1
  rw [mul_I_tau_re, mul_I_tau_im]
  simp only [normalVel, normalComp]
  ring

/-- The interpolating curvature is differentiable in the arclength as soon as
the two curvatures are. -/
theorem hasDerivAt_kappaInterp (h0 : ∀ r, HasDerivAt k0 (k0' r) r)
    (h1 : ∀ r, HasDerivAt k1 (k1' r) r) (t s : ℝ) :
    HasDerivAt (kappaInterp k0 k1 t) ((1 - t) * k0' s + t * k1' s) s := by
  have h : HasDerivAt (fun r => (1 - t) * k0 r + t * k1 r)
      ((1 - t) * k0' s + t * k1' s) s :=
    ((h0 s).const_mul (1 - t)).add ((h1 s).const_mul t)
  exact h

/-- The second arclength derivative `∂_s²η = (κ¹ − κ⁰) − κ_t' ξ − κ_t² η` of the
normal velocity. -/
def normalVelSecondDeriv (k0 k1 k0' k1' : ℝ → ℝ) (θ₀ L t s : ℝ) : ℝ :=
  (k1 s - k0 s) - ((1 - t) * k0' s + t * k1' s) * tangentVel k0 k1 θ₀ L t s
    - kappaInterp k0 k1 t s * (kappaInterp k0 k1 t s * normalVel k0 k1 θ₀ L t s)

/-- **The second variation of the normal velocity.** -/
theorem hasDerivAt_normalVelDeriv (hk0 : Continuous k0) (hk1 : Continuous k1)
    (h0 : ∀ r, HasDerivAt k0 (k0' r) r) (h1 : ∀ r, HasDerivAt k1 (k1' r) r) (t s : ℝ) :
    HasDerivAt (normalVelDeriv k0 k1 θ₀ L t)
      (normalVelSecondDeriv k0 k1 k0' k1' θ₀ L t s) s := by
  have hB : HasDerivAt (angleShift k0 k1) (k1 s - k0 s) s := by
    have hc : Continuous fun u => k1 u - k0 u := by fun_prop
    simpa [angleShift] using (hc.integral_hasStrictDerivAt (0:ℝ) s).hasDerivAt
  have hk := hasDerivAt_kappaInterp (k0' := k0') (k1' := k1') h0 h1 t s
  have hxi := hasDerivAt_tangentVel (θ₀ := θ₀) (L := L) hk0 hk1 t s
  have h := hB.sub (hk.mul hxi)
  convert h using 1
  simp only [normalVelSecondDeriv]
  ring

section Bounds

variable (hk0 : Continuous k0) (hk1 : Continuous k1)
  (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
  (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
  (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)

include hk0 hk1 hper0 hper1 htot0 htot1 hL

/-- **The sup bound on the second arclength derivative of the normal
velocity**: `|∂_s²η| ≤ d + (k' + κ_*²)(3/2)Lε`, where `d` bounds `|κ¹ − κ⁰|`,
`k'` bounds the derivatives of the two curvatures and `κ_*` bounds them. -/
theorem abs_normalVelSecondDeriv_le {kstar dsup kd : ℝ} {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hd : ∀ r, |k1 r - k0 r| ≤ dsup)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) (s : ℝ) :
    |normalVelSecondDeriv k0 k1 k0' k1' θ₀ L t s|
      ≤ dsup + (kd + kstar ^ 2) * ((3/2) * L * curvDist k0 k1 L) := by
  have heps : 0 ≤ curvDist k0 k1 L := integral_abs_sub_nonneg hk0 hk1 hL.le
  have hb : 0 ≤ (3/2) * L * curvDist k0 k1 L := by positivity
  have hxi : |tangentVel k0 k1 θ₀ L t s| ≤ (3/2) * L * curvDist k0 k1 L :=
    abs_tangentVel_le hk0 hk1 hper0 hper1 htot0 htot1 hL t s
  have heta : |normalVel k0 k1 θ₀ L t s| ≤ (3/2) * L * curvDist k0 k1 L :=
    abs_normalVel_le hk0 hk1 hper0 hper1 htot0 htot1 hL t s
  have hkap0 : 0 ≤ kappaInterp k0 k1 t s := by
    have ha : 0 ≤ (1 - t) * k0 s := mul_nonneg (by linarith [ht.2]) (hk0nn s)
    have hb' : 0 ≤ t * k1 s := mul_nonneg ht.1 (hk1nn s)
    simpa [kappaInterp] using add_nonneg ha hb'
  have hkaple : kappaInterp k0 k1 t s ≤ kstar := kappaInterp_le hk0le hk1le ht s
  have hkder : |(1 - t) * k0' s + t * k1' s| ≤ kd := by
    have h1 : |(1 - t) * k0' s| ≤ (1 - t) * kd := by
      rw [abs_mul, abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)]
      exact mul_le_mul_of_nonneg_left (hkd0 s) (by linarith [ht.2])
    have h2 : |t * k1' s| ≤ t * kd := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact mul_le_mul_of_nonneg_left (hkd1 s) ht.1
    calc |(1 - t) * k0' s + t * k1' s| ≤ |(1 - t) * k0' s| + |t * k1' s| := abs_add_le _ _
      _ ≤ (1 - t) * kd + t * kd := by linarith
      _ = kd := by ring
  have hkd0' : 0 ≤ kd := le_trans (abs_nonneg _) (hkd0 0)
  have hterm1 : |((1 - t) * k0' s + t * k1' s) * tangentVel k0 k1 θ₀ L t s|
      ≤ kd * ((3/2) * L * curvDist k0 k1 L) := by
    rw [abs_mul]
    exact mul_le_mul hkder hxi (abs_nonneg _) hkd0'
  have hterm2 : |kappaInterp k0 k1 t s * (kappaInterp k0 k1 t s * normalVel k0 k1 θ₀ L t s)|
      ≤ kstar ^ 2 * ((3/2) * L * curvDist k0 k1 L) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hkap0]
    have hk2 : kappaInterp k0 k1 t s * kappaInterp k0 k1 t s ≤ kstar ^ 2 := by
      nlinarith
    calc kappaInterp k0 k1 t s * (kappaInterp k0 k1 t s * |normalVel k0 k1 θ₀ L t s|)
        = (kappaInterp k0 k1 t s * kappaInterp k0 k1 t s) * |normalVel k0 k1 θ₀ L t s| := by
          ring
      _ ≤ kstar ^ 2 * ((3/2) * L * curvDist k0 k1 L) := by
          have := abs_nonneg (normalVel k0 k1 θ₀ L t s)
          nlinarith [mul_nonneg hkap0 hkap0]
  have htri : |normalVelSecondDeriv k0 k1 k0' k1' θ₀ L t s|
      ≤ |k1 s - k0 s| + |((1 - t) * k0' s + t * k1' s) * tangentVel k0 k1 θ₀ L t s|
        + |kappaInterp k0 k1 t s * (kappaInterp k0 k1 t s * normalVel k0 k1 θ₀ L t s)| := by
    have h1 := abs_sub (k1 s - k0 s - ((1 - t) * k0' s + t * k1' s) * tangentVel k0 k1 θ₀ L t s)
      (kappaInterp k0 k1 t s * (kappaInterp k0 k1 t s * normalVel k0 k1 θ₀ L t s))
    have h2 := abs_sub (k1 s - k0 s)
      (((1 - t) * k0' s + t * k1' s) * tangentVel k0 k1 θ₀ L t s)
    simp only [normalVelSecondDeriv]
    linarith
  have hds := hd s
  have hfinal : dsup + kd * ((3/2) * L * curvDist k0 k1 L)
      + kstar ^ 2 * ((3/2) * L * curvDist k0 k1 L)
      = dsup + (kd + kstar ^ 2) * ((3/2) * L * curvDist k0 k1 L) := by ring
  linarith

end Bounds

/-- The second-order density of the interpolation path at time `t`: the sup
norm over the fundamental interval of `∂_s²η`. -/
def S2norm (k0 k1 k0' k1' : ℝ → ℝ) (θ₀ L t : ℝ) : ℝ :=
  sSup ((fun s => |normalVelSecondDeriv k0 k1 k0' k1' θ₀ L t s|) '' Set.Icc 0 L)

theorem continuous_uncurry_normalVelSecondDeriv (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hc0 : Continuous k0') (hc1 : Continuous k1') :
    Continuous fun p : ℝ × ℝ => normalVelSecondDeriv k0 k1 k0' k1' θ₀ L p.1 p.2 := by
  have hxi := continuous_uncurry_tangentVel (θ₀ := θ₀) (L := L) hk0 hk1
  have heta := continuous_uncurry_normalVel (θ₀ := θ₀) (L := L) hk0 hk1
  have hkap := continuous_uncurry_kappaInterp (k0 := k0) (k1 := k1) hk0 hk1
  have hkder : Continuous fun p : ℝ × ℝ => (1 - p.1) * k0' p.2 + p.1 * k1' p.2 :=
    ((continuous_const.sub continuous_fst).mul (hc0.comp continuous_snd)).add
      (continuous_fst.mul (hc1.comp continuous_snd))
  simp only [normalVelSecondDeriv]
  exact (((hk1.comp continuous_snd).sub (hk0.comp continuous_snd)).sub
    (hkder.mul hxi)).sub (hkap.mul (hkap.mul heta))

theorem continuous_S2norm (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hc0 : Continuous k0') (hc1 : Continuous k1') :
    Continuous (S2norm k0 k1 k0' k1' θ₀ L) := by
  show Continuous fun t : ℝ =>
    sSup ((fun s => |normalVelSecondDeriv k0 k1 k0' k1' θ₀ L t s|) '' Set.Icc 0 L)
  exact isCompact_Icc.continuous_sSup
    (f := fun t s => |normalVelSecondDeriv k0 k1 k0' k1' θ₀ L t s|)
    (continuous_uncurry_normalVelSecondDeriv (θ₀ := θ₀) (L := L) hk0 hk1 hc0 hc1).abs

/-- **The second-order density of the interpolation path**: for curvatures with
bounded derivatives the density `S₂` obeys the same bound at every time. -/
theorem S2norm_le {kstar dsup kd : ℝ} {t : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hd : ∀ r, |k1 r - k0 r| ≤ dsup)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) :
    S2norm k0 k1 k0' k1' θ₀ L t
      ≤ dsup + (kd + kstar ^ 2) * ((3/2) * L * curvDist k0 k1 L) := by
  have heps : 0 ≤ curvDist k0 k1 L := integral_abs_sub_nonneg hk0 hk1 hL.le
  have hkd0' : 0 ≤ kd := le_trans (abs_nonneg _) (hkd0 0)
  have hdsup : 0 ≤ dsup := le_trans (abs_nonneg _) (hd 0)
  refine Real.sSup_le ?_ (by positivity)
  rintro x ⟨s, -, rfl⟩
  exact abs_normalVelSecondDeriv_le hk0 hk1 hper0 hper1 htot0 htot1 hL ht hd hkd0 hkd1
    hk0nn hk1nn hk0le hk1le s

/-- The second-order functional of the interpolation path obeys the same
bound. -/
theorem integral_S2norm_le {kstar dsup kd : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hc0 : Continuous k0') (hc1 : Continuous k1')
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)
    (hd : ∀ r, |k1 r - k0 r| ≤ dsup)
    (hkd0 : ∀ r, |k0' r| ≤ kd) (hkd1 : ∀ r, |k1' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ k0 r) (hk1nn : ∀ r, 0 ≤ k1 r)
    (hk0le : ∀ r, k0 r ≤ kstar) (hk1le : ∀ r, k1 r ≤ kstar) :
    (∫ t in (0:ℝ)..1, S2norm k0 k1 k0' k1' θ₀ L t)
      ≤ dsup + (kd + kstar ^ 2) * ((3/2) * L * curvDist k0 k1 L) := by
  have hint : IntervalIntegrable (S2norm k0 k1 k0' k1' θ₀ L) volume 0 1 :=
    (continuous_S2norm hk0 hk1 hc0 hc1).intervalIntegrable _ _
  have hb : ∀ t ∈ Set.Icc (0:ℝ) 1, S2norm k0 k1 k0' k1' θ₀ L t
      ≤ dsup + (kd + kstar ^ 2) * ((3/2) * L * curvDist k0 k1 L) := fun t ht =>
    S2norm_le hk0 hk1 hper0 hper1 htot0 htot1 hL ht hd hkd0 hkd1 hk0nn hk1nn hk0le hk1le
  have := intervalIntegral.integral_mono_on (μ := volume) (a := (0:ℝ)) (b := 1)
    (f := S2norm k0 k1 k0' k1' θ₀ L)
    (g := fun _ => dsup + (kd + kstar ^ 2) * ((3/2) * L * curvDist k0 k1 L))
    zero_le_one hint (_root_.intervalIntegrable_const) hb
  simpa using this

/-! ## The hypotheses are not vacuous -/

/-- The arclength derivative of the curvature `1/2 + (cos s)/4`. -/
def kwave' : ℝ → ℝ := fun s => -Real.sin s / 4

theorem hasDerivAt_kcirc (r : ℝ) : HasDerivAt kcirc 0 r := hasDerivAt_const r (1/2 : ℝ)

theorem hasDerivAt_kwave (r : ℝ) : HasDerivAt kwave (kwave' r) r := by
  have h : HasDerivAt (fun s : ℝ => 1 / 2 + Real.cos s / 4) (-Real.sin r / 4) r := by
    simpa using ((Real.hasDerivAt_cos r).div_const 4).const_add (1/2 : ℝ)
  exact h

/-- **The second-order density on a genuine pair of curvatures.**  For the
circle of curvature `1/2` and the oval of curvature `1/2 + (cos s)/4` the
second-order functional of the interpolating path is bounded, so the
hypotheses of the bound are not vacuous. -/
theorem integral_S2norm_le_instance :
    (∫ t in (0:ℝ)..1, S2norm kcirc kwave (fun _ => 0) kwave' 0 (2 * Real.pi) t)
      ≤ 1/4 + (1/4 + (3/4 : ℝ) ^ 2)
        * ((3/2) * (2 * Real.pi) * curvDist kcirc kwave (2 * Real.pi)) := by
  refine integral_S2norm_le (kstar := 3/4) (dsup := 1/4) (kd := 1/4) (θ₀ := 0)
    continuous_kcirc continuous_kwave continuous_const (by unfold kwave'; fun_prop)
    kcirc_periodic kwave_periodic kcirc_total kwave_total (by positivity) (fun r => ?_)
    (fun r => by norm_num) (fun r => ?_) kcirc_nonneg kwave_nonneg kcirc_le kwave_le
  · have h1 := Real.neg_one_le_cos r
    have h2 := Real.cos_le_one r
    rw [abs_le]
    constructor <;> simp only [kcirc, kwave] <;> linarith
  · have h1 := Real.neg_one_le_sin r
    have h2 := Real.sin_le_one r
    rw [abs_le]
    constructor <;> simp only [kwave'] <;> linarith

end InterpolationSecondOrder
