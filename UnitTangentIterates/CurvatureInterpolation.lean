import Mathlib

/-!
# The explicit curvature interpolation of Lemma 6.2

This file formalizes the self-contained core of the "curvature interpolation"
lemma of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates*.

Given a (continuous) intrinsic curvature function `κ` on the line, a marked
tangent angle `θ₀` and a half-perimeter `L`, the paper builds the curve

`X(s) = ∫₀ˢ τ(θ(r)) dr - ½ ∫₀ᴸ τ(θ(r)) dr`,   `θ(s) = θ₀ + ∫₀ˢ κ`,

where `τ(θ) = e^{iθ}` is the unit tangent direction, and claims that this
formula "makes closure, central symmetry, centering, and the marked tangent
phase explicit", that the curve is unit-speed with curvature exactly `κ`, and
that the interpolation `κ_t = (1-t)κ⁰ + tκ¹` moves the curve by at most
`C(1+L)ε` where `ε = ‖κ¹ - κ⁰‖_{L¹(0,L)}`.

Main results:

* `hasDerivAt_tangentAngle`, `hasDerivAt_interpCurve` : the curve is unit speed
  with tangent angle `θ`, whose derivative is the prescribed curvature `κ`;
* `interpCurve_zero`, `interpCurve_half` : centering, `X(L) = -X(0)`;
* `interpCurve_add_halfPeriod` : **central symmetry** `X(s + L) = -X(s)`, valid
  as soon as `κ` is `L`-periodic with `∫₀ᴸ κ = π`;
* `interpCurve_periodic` : consequently `X` is `2L`-periodic (closure);
* `kappaInterp_pos`, `kappaInterp_le`, `integral_kappaInterp` : the linear
  interpolation of two admissible curvatures is admissible;
* `norm_tangentAngle_interp_sub`, `norm_interpCurve_interp_sub` : the
  quantitative estimate `‖X_t(s) - X_{t'}(s)‖ ≤ (3/2) L |t - t'| ε`.
-/

noncomputable section

open Real MeasureTheory intervalIntegral

namespace CurvatureInterpolation

/-- The unit tangent direction of angle `θ`, viewed as a complex number. -/
noncomputable def tau (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

@[simp] theorem norm_tau (θ : ℝ) : ‖tau θ‖ = 1 := by
  simp [tau, Complex.norm_exp]

theorem continuous_tau : Continuous tau := by
  unfold tau; fun_prop

theorem hasDerivAt_tau (θ : ℝ) : HasDerivAt tau (Complex.I * tau θ) θ := by
  have h0 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 θ := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := θ)
  have h : HasDerivAt (fun x : ℝ => (x : ℂ) * Complex.I) Complex.I θ := by
    simpa using h0.mul_const Complex.I
  unfold tau
  simpa [mul_comm] using h.cexp

theorem tau_add_pi (θ : ℝ) : tau (θ + Real.pi) = -tau θ := by
  simp only [tau, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- `‖τ a - τ b‖ ≤ |a - b|`. -/
theorem norm_tau_sub_tau (a b : ℝ) : ‖tau a - tau b‖ ≤ |a - b| := by
  have hd : ∀ x ∈ Set.uIcc b a, HasDerivAt tau (Complex.I * tau x) x := fun x _ =>
    hasDerivAt_tau x
  have hb : ∀ x ∈ Set.uIcc b a, ‖Complex.I * tau x‖ ≤ 1 := by
    intro x _
    simp
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := tau) (f' := fun x => Complex.I * tau x) (s := Set.uIcc b a) (C := 1)
    (fun x hx => (hd x hx).hasDerivWithinAt) hb (convex_uIcc b a)
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  simpa [Real.dist_eq, abs_sub_comm] using this

section Curve

variable (kappa : ℝ → ℝ) (θ₀ L : ℝ)

/-- The tangent angle `θ(s) = θ₀ + ∫₀ˢ κ`. -/
noncomputable def tangentAngle (s : ℝ) : ℝ := θ₀ + ∫ r in (0:ℝ)..s, kappa r

/-- The curve of the explicit curvature interpolation formula. -/
noncomputable def interpCurve (s : ℝ) : ℂ :=
  (∫ r in (0:ℝ)..s, tau (tangentAngle kappa θ₀ r))
    - (1/2 : ℂ) * ∫ r in (0:ℝ)..L, tau (tangentAngle kappa θ₀ r)

variable {kappa θ₀ L}

@[simp] theorem tangentAngle_zero : tangentAngle kappa θ₀ 0 = θ₀ := by
  simp [tangentAngle]

/-- The tangent angle has derivative the prescribed curvature. -/
theorem hasDerivAt_tangentAngle (hk : Continuous kappa) (s : ℝ) :
    HasDerivAt (tangentAngle kappa θ₀) (kappa s) s := by
  unfold tangentAngle
  exact ((hk.integral_hasStrictDerivAt (0:ℝ) s).hasDerivAt).const_add θ₀

theorem continuous_tangentAngle (hk : Continuous kappa) :
    Continuous (tangentAngle kappa θ₀) :=
  continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_tangentAngle (θ₀ := θ₀) hk s).continuousAt

theorem continuous_tau_tangentAngle (hk : Continuous kappa) :
    Continuous fun r => tau (tangentAngle kappa θ₀ r) :=
  continuous_tau.comp (continuous_tangentAngle hk)

/-- The curve is unit speed with tangent direction `τ(θ(s))`. -/
theorem hasDerivAt_interpCurve (hk : Continuous kappa) (s : ℝ) :
    HasDerivAt (interpCurve kappa θ₀ L) (tau (tangentAngle kappa θ₀ s)) s := by
  have hc := continuous_tau_tangentAngle hk (θ₀ := θ₀)
  unfold interpCurve
  exact ((hc.integral_hasStrictDerivAt (0:ℝ) s).hasDerivAt).sub_const
      ((1/2 : ℂ) * ∫ r in (0:ℝ)..L, tau (tangentAngle kappa θ₀ r))

/-- Unit speed. -/
theorem norm_deriv_interpCurve (hk : Continuous kappa) (s : ℝ) :
    ‖deriv (interpCurve kappa θ₀ L) s‖ = 1 := by
  rw [(hasDerivAt_interpCurve (L := L) hk s).deriv, norm_tau]

/-- Centering: the marked point sits at `-½∫₀ᴸ τ`, and `X(L) = -X(0)`. -/
@[simp] theorem interpCurve_zero :
    interpCurve kappa θ₀ L 0 = -(1/2 : ℂ) * ∫ r in (0:ℝ)..L, tau (tangentAngle kappa θ₀ r) := by
  simp [interpCurve]

theorem interpCurve_half :
    interpCurve kappa θ₀ L L = -interpCurve kappa θ₀ L 0 := by
  simp [interpCurve]
  ring

section Symmetry

variable (hk : Continuous kappa) (hper : Function.Periodic kappa L)
  (htotal : (∫ r in (0:ℝ)..L, kappa r) = Real.pi)

include hk hper htotal in
/-- The tangent angle advances by exactly `π` over a half period. -/
theorem tangentAngle_add_halfPeriod (s : ℝ) :
    tangentAngle kappa θ₀ (s + L) = tangentAngle kappa θ₀ s + Real.pi := by
  have hint : (∫ r in (0:ℝ)..(s + L), kappa r)
      = (∫ r in (0:ℝ)..s, kappa r) + ∫ r in s..(s + L), kappa r := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hk.intervalIntegrable _ _) (hk.intervalIntegrable _ _)]
  have hshift : (∫ r in s..(s + L), kappa r) = ∫ r in (0:ℝ)..L, kappa r := by
    simpa using hper.intervalIntegral_add_eq s 0
  simp only [tangentAngle, hint, hshift, htotal]
  ring

include hk hper htotal in
/-- The unit tangent reverses over a half period. -/
theorem tau_tangentAngle_add_halfPeriod (s : ℝ) :
    tau (tangentAngle kappa θ₀ (s + L)) = -tau (tangentAngle kappa θ₀ s) := by
  rw [tangentAngle_add_halfPeriod hk hper htotal s, tau_add_pi]

include hk hper htotal in
/-- **Central symmetry**: `X(s + L) = -X(s)`. -/
theorem interpCurve_add_halfPeriod (s : ℝ) :
    interpCurve kappa θ₀ L (s + L) = -interpCurve kappa θ₀ L s := by
  have hc := continuous_tau_tangentAngle hk (θ₀ := θ₀)
  have hsplit : (∫ r in (0:ℝ)..(s + L), tau (tangentAngle kappa θ₀ r))
      = (∫ r in (0:ℝ)..L, tau (tangentAngle kappa θ₀ r))
        + ∫ r in L..(s + L), tau (tangentAngle kappa θ₀ r) := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hshift : (∫ r in L..(s + L), tau (tangentAngle kappa θ₀ r))
      = -∫ r in (0:ℝ)..s, tau (tangentAngle kappa θ₀ r) := by
    have h := intervalIntegral.integral_comp_add_right
      (a := (0:ℝ)) (b := s) (fun r => tau (tangentAngle kappa θ₀ r)) L
    rw [zero_add] at h
    rw [← h, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun r _ => ?_)
    exact tau_tangentAngle_add_halfPeriod hk hper htotal r
  simp only [interpCurve, hsplit, hshift]
  ring

include hk hper htotal in
/-- Closure: the curve is `2L`-periodic. -/
theorem interpCurve_periodic : Function.Periodic (interpCurve kappa θ₀ L) (2 * L) := by
  intro s
  have h1 := interpCurve_add_halfPeriod (θ₀ := θ₀) hk hper htotal s
  have h2 := interpCurve_add_halfPeriod (θ₀ := θ₀) hk hper htotal (s + L)
  rw [show s + 2 * L = s + L + L from by ring, h2, h1, neg_neg]

end Symmetry

end Curve

section Interpolation

/-- The linear interpolation `κ_t = (1-t)κ⁰ + tκ¹`. -/
noncomputable def kappaInterp (k0 k1 : ℝ → ℝ) (t : ℝ) (r : ℝ) : ℝ :=
  (1 - t) * k0 r + t * k1 r

variable {k0 k1 : ℝ → ℝ} {t : ℝ}

theorem kappaInterp_pos (h0 : ∀ r, 0 < k0 r) (h1 : ∀ r, 0 < k1 r)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (r : ℝ) : 0 < kappaInterp k0 k1 t r := by
  rcases ht with ⟨ht0, ht1⟩
  rcases eq_or_lt_of_le ht1 with h | h
  · simp [kappaInterp, h, h1 r]
  · have : 0 < 1 - t := by linarith
    have := mul_pos this (h0 r)
    have h2 : 0 ≤ t * k1 r := mul_nonneg ht0 (h1 r).le
    simpa [kappaInterp] using by linarith

theorem kappaInterp_le {ks : ℝ} (h0 : ∀ r, k0 r ≤ ks) (h1 : ∀ r, k1 r ≤ ks)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (r : ℝ) : kappaInterp k0 k1 t r ≤ ks := by
  rcases ht with ⟨ht0, ht1⟩
  have hA : (1 - t) * k0 r ≤ (1 - t) * ks := by
    apply mul_le_mul_of_nonneg_left (h0 r); linarith
  have hB : t * k1 r ≤ t * ks := mul_le_mul_of_nonneg_left (h1 r) ht0
  simp only [kappaInterp]
  nlinarith

theorem continuous_kappaInterp (hk0 : Continuous k0) (hk1 : Continuous k1) :
    Continuous (kappaInterp k0 k1 t) := by
  unfold kappaInterp; fun_prop

/-- The half-turn condition `∫₀ᴸ κ = π` is preserved by the interpolation. -/
theorem integral_kappaInterp {L : ℝ} (hk0 : Continuous k0) (hk1 : Continuous k1)
    (h0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi) (h1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) :
    (∫ r in (0:ℝ)..L, kappaInterp k0 k1 t r) = Real.pi := by
  simp only [kappaInterp]
  rw [intervalIntegral.integral_add (f := fun r => (1 - t) * k0 r) (g := fun r => t * k1 r)
    ((continuous_const.mul hk0).intervalIntegrable _ _)
    ((continuous_const.mul hk1).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h0, h1]
  ring

/-- Periodicity is preserved by the interpolation. -/
theorem periodic_kappaInterp {L : ℝ} (h0 : Function.Periodic k0 L)
    (h1 : Function.Periodic k1 L) : Function.Periodic (kappaInterp k0 k1 t) L := by
  intro r
  simp [kappaInterp, h0 r, h1 r]

variable {θ₀ L : ℝ}

/-- The tangent angles of two interpolation parameters differ by at most
`|t - t'| ε`, where `ε = ∫₀ᴸ |κ¹ - κ⁰|`. -/
theorem norm_tangentAngle_interp_sub (hk0 : Continuous k0) (hk1 : Continuous k1)
    {t t' : ℝ} {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) L) :
    |tangentAngle (kappaInterp k0 k1 t) θ₀ s - tangentAngle (kappaInterp k0 k1 t') θ₀ s|
      ≤ |t - t'| * ∫ r in (0:ℝ)..L, |k1 r - k0 r| := by
  have hL : (0:ℝ) ≤ L := le_trans hs.1 hs.2
  have hdiff : ∀ r, kappaInterp k0 k1 t r - kappaInterp k0 k1 t' r = (t - t') * (k1 r - k0 r) := by
    intro r; simp only [kappaInterp]; ring
  have hcd : Continuous fun r => (t - t') * (k1 r - k0 r) := by fun_prop
  have hkey : tangentAngle (kappaInterp k0 k1 t) θ₀ s - tangentAngle (kappaInterp k0 k1 t') θ₀ s
      = ∫ r in (0:ℝ)..s, (t - t') * (k1 r - k0 r) := by
    simp only [tangentAngle]
    rw [show (θ₀ + ∫ r in (0:ℝ)..s, kappaInterp k0 k1 t r)
        - (θ₀ + ∫ r in (0:ℝ)..s, kappaInterp k0 k1 t' r)
        = (∫ r in (0:ℝ)..s, kappaInterp k0 k1 t r)
          - ∫ r in (0:ℝ)..s, kappaInterp k0 k1 t' r from by ring,
      ← intervalIntegral.integral_sub
        ((continuous_kappaInterp hk0 hk1).intervalIntegrable _ _)
        ((continuous_kappaInterp hk0 hk1).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr (fun r _ => hdiff r)
  rw [hkey]
  calc |∫ r in (0:ℝ)..s, (t - t') * (k1 r - k0 r)|
      ≤ ∫ r in (0:ℝ)..s, |(t - t') * (k1 r - k0 r)| :=
        intervalIntegral.abs_integral_le_integral_abs hs.1
    _ = |t - t'| * ∫ r in (0:ℝ)..s, |k1 r - k0 r| := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr (fun r _ => by rw [abs_mul])
    _ ≤ |t - t'| * ∫ r in (0:ℝ)..L, |k1 r - k0 r| := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hca : Continuous fun r => |k1 r - k0 r| := by fun_prop
        have hnn : ∀ r, (0:ℝ) ≤ |k1 r - k0 r| := fun r => abs_nonneg _
        have := intervalIntegral.integral_mono_on (μ := volume) (a := s) (b := L)
          (f := fun _ => (0:ℝ)) (g := fun r => |k1 r - k0 r|) hs.2
          (_root_.intervalIntegrable_const) (hca.intervalIntegrable _ _) (fun r _ => hnn r)
        simp only [intervalIntegral.integral_zero] at this
        have hadd : (∫ r in (0:ℝ)..s, |k1 r - k0 r|) + (∫ r in s..L, |k1 r - k0 r|)
            = ∫ r in (0:ℝ)..L, |k1 r - k0 r| :=
          intervalIntegral.integral_add_adjacent_intervals
            (hca.intervalIntegrable _ _) (hca.intervalIntegrable _ _)
        linarith

/-- **The quantitative interpolation estimate**: the curves move by at most
`(3/2) L |t - t'| ε` in the sup norm on `[0, L]`. -/
theorem norm_interpCurve_interp_sub (hk0 : Continuous k0) (hk1 : Continuous k1)
    {t t' : ℝ} {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) L) :
    ‖interpCurve (kappaInterp k0 k1 t) θ₀ L s
        - interpCurve (kappaInterp k0 k1 t') θ₀ L s‖
      ≤ (3/2) * L * (|t - t'| * ∫ r in (0:ℝ)..L, |k1 r - k0 r|) := by
  set ε : ℝ := |t - t'| * ∫ r in (0:ℝ)..L, |k1 r - k0 r| with hε
  have hL : (0:ℝ) ≤ L := le_trans hs.1 hs.2
  have hεnn : 0 ≤ ε := by
    refine mul_nonneg (abs_nonneg _) ?_
    have hca : Continuous fun r => |k1 r - k0 r| := by fun_prop
    have := intervalIntegral.integral_mono_on (μ := volume) (a := (0:ℝ)) (b := L)
      (f := fun _ => (0:ℝ)) (g := fun r => |k1 r - k0 r|) hL
      (_root_.intervalIntegrable_const) (hca.intervalIntegrable _ _) (fun r _ => abs_nonneg _)
    simpa using this
  -- pointwise bound on the tangent directions
  have hpt : ∀ r ∈ Set.Icc (0:ℝ) L,
      ‖tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r)
        - tau (tangentAngle (kappaInterp k0 k1 t') θ₀ r)‖ ≤ ε := by
    intro r hr
    exact (norm_tau_sub_tau _ _).trans (norm_tangentAngle_interp_sub hk0 hk1 hr)
  have hcT : ∀ u : ℝ, Continuous fun r => tau (tangentAngle (kappaInterp k0 k1 u) θ₀ r) :=
    fun u => continuous_tau_tangentAngle (continuous_kappaInterp hk0 hk1)
  -- bound on the running integral
  have hrun : ∀ b ∈ Set.Icc (0:ℝ) L,
      ‖(∫ r in (0:ℝ)..b, tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r))
        - ∫ r in (0:ℝ)..b, tau (tangentAngle (kappaInterp k0 k1 t') θ₀ r)‖ ≤ b * ε := by
    intro b hb
    rw [← intervalIntegral.integral_sub ((hcT t).intervalIntegrable _ _)
      ((hcT t').intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := b) (C := ε)
      (f := fun r => tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r)
        - tau (tangentAngle (kappaInterp k0 k1 t') θ₀ r))
      (fun r hr => hpt r ⟨le_of_lt (by
          rw [Set.uIoc_of_le hb.1] at hr; exact lt_of_lt_of_le (by
            simpa using hr.1) le_rfl),
        le_trans (by rw [Set.uIoc_of_le hb.1] at hr; exact hr.2) hb.2⟩)
    simpa [abs_of_nonneg hb.1, mul_comm] using this
  have h1 := hrun s hs
  have h2 := hrun L ⟨hL, le_rfl⟩
  have hexpand : interpCurve (kappaInterp k0 k1 t) θ₀ L s
      - interpCurve (kappaInterp k0 k1 t') θ₀ L s
      = ((∫ r in (0:ℝ)..s, tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r))
          - ∫ r in (0:ℝ)..s, tau (tangentAngle (kappaInterp k0 k1 t') θ₀ r))
        - (1/2 : ℂ) * ((∫ r in (0:ℝ)..L, tau (tangentAngle (kappaInterp k0 k1 t) θ₀ r))
          - ∫ r in (0:ℝ)..L, tau (tangentAngle (kappaInterp k0 k1 t') θ₀ r)) := by
    simp only [interpCurve]; ring
  rw [hexpand]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have hhalf : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
  rw [hhalf]
  nlinarith [hs.2, hs.1, hεnn, h1, h2]

end Interpolation

end CurvatureInterpolation
