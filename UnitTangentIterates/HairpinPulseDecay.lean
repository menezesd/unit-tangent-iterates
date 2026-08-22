import Mathlib
import UnitTangentIterates.HairpinRelativeDerivatives

/-!
# Exponential decay of all derivatives of the hairpin curvature and of the pulse

The lemma **Hairpin pulse estimates** of the paper *A Noncircular Oval with
Convex Unit-Tangent Iterates* asserts that the steering pulse `y` and *all* its
derivatives decay exponentially at both ends, and likewise for the curvature
`K_*` of the hairpin.  `HairpinTails.lean` proves the decay of `K_*` itself,
`HairpinRelativeDerivatives.lean` proves the relative bounds
`|K_*^{(j)}| ≤ C_j K_*` and `|y^{(j)}| ≤ D_j y`; this file combines them and
transports the decay from the rear arclength `u` to the front arclength `s`.

The transport rests on the elementary observation that the front arclength
`σ(u) = ∫₀^u √(1 + K_*²)` differs from `u` by at most

```
  σ(u) - u = ∫₀^u (√(1+K_*²) - 1) ≤ ½∫₀^u K_*²,
```

which is bounded because `K_*` decays exponentially; hence `|x(s)| ≥ |s| - B`
for the inverse `x` of `σ`, and the decay in `u` becomes decay in `s`.

Main results:

* `HairpinRelative.abs_iteratedDeriv_curv_decay` : `|K_*^{(j)}(u)| ≤ C_j e^{-|u|/M}`;
* `HairpinRelative.frontArclength_le`, `HairpinRelative.le_frontArclength` : the
  two-sided bound `|σ(u) - u| ≤ B` for an exponentially decaying curvature;
* `HairpinRelative.abs_pulseState_ge` : `|x(s)| ≥ |s| - B`;
* `HairpinRelative.pulse_decay` : `y(s) ≤ A e^{B/M} e^{-|s|/M}`;
* `HairpinRelative.abs_iteratedDeriv_pulse_decay` : `|y^{(j)}(s)| ≤ D_j e^{-|s|/M}`;
* `HairpinRelative.hairpin_pulse_exponential_decay` : both families of bounds
  for the hairpin of `HairpinArclength.exists_angle`.
-/

noncomputable section

open Real Set MeasureTheory

open scoped ContDiff

namespace HairpinRelative

variable {f : ℝ → ℝ} {A M : ℝ}

/-! ### Two elementary inequalities -/

theorem sqrt_one_add_sq_sub_one_le (z : ℝ) : Real.sqrt (1 + z ^ 2) - 1 ≤ z ^ 2 / 2 := by
  have h1 : (1 : ℝ) + z ^ 2 ≤ (1 + z ^ 2 / 2) ^ 2 := by nlinarith [sq_nonneg (z ^ 2)]
  have h2 : (0 : ℝ) ≤ 1 + z ^ 2 / 2 := by positivity
  have := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq h2] at this
  linarith

/-- `∫₀^u e^{-t/M} dt ≤ M` for `u ≥ 0`. -/
theorem integral_exp_neg_le (hM : 0 < M) (u : ℝ) :
    (∫ t in (0:ℝ)..u, Real.exp (-t / M)) ≤ M := by
  have hderiv : ∀ t ∈ uIcc (0:ℝ) u, HasDerivAt (fun t => -M * Real.exp (-t / M))
      (Real.exp (-t / M)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => -t / M) (-1 / M) t := by
      simpa using ((hasDerivAt_neg t).div_const M)
    have h2 := (h1.exp).const_mul (-M)
    have : -M * (Real.exp (-t / M) * (-1 / M)) = Real.exp (-t / M) := by
      field_simp
    simpa [this] using h2
  have hcont : IntervalIntegrable (fun t : ℝ => Real.exp (-t / M)) volume 0 u :=
    (Real.continuous_exp.comp (by continuity)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
  have hpos : 0 < Real.exp (-u / M) := Real.exp_pos _
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one]
  nlinarith

/-! ### Decay of the derivatives of the curvature -/

/-- **Exponential decay of every derivative of the hairpin curvature.**  From
the decay of `K_*` itself and the relative bounds `|K_*^{(j)}| ≤ C_j K_*`. -/
theorem abs_iteratedDeriv_curv_decay (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u,
      |iteratedDeriv j (fun u => curvField f (theta u)) u| ≤ C * Real.exp (-|u| / M) := by
  obtain ⟨C, hC0, hC⟩ := abs_iteratedDeriv_curv_le hf hfpos hmem hderiv j
  refine ⟨C * A, ?_, fun u => ?_⟩
  · have hA : 0 ≤ A := by
      have h0 := le_trans (curvField_nonneg hfpos (hmem 0)) (hdecay 0)
      by_contra hneg
      push_neg at hneg
      nlinarith [Real.exp_pos (-|(0:ℝ)| / M)]
    positivity
  · calc |iteratedDeriv j (fun u => curvField f (theta u)) u|
        ≤ C * curvField f (theta u) := hC u
      _ ≤ C * (A * Real.exp (-|u| / M)) := by
          exact mul_le_mul_of_nonneg_left (hdecay u) hC0
      _ = C * A * Real.exp (-|u| / M) := by ring

/-! ### The front arclength differs from the rear arclength by a bounded amount -/

theorem frontArclength_zero (f : ℝ → ℝ) (theta : ℝ → ℝ) : frontArclength f theta 0 = 0 := by
  simp [frontArclength]

/-- The pointwise bound on the integrand of the front arclength. -/
theorem sqrt_integrand_le (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (1 + curvField f (theta t) ^ 2) - 1 ≤ A ^ 2 / 2 * Real.exp (-t / M) := by
  have h0 : 0 ≤ curvField f (theta t) := curvField_nonneg hfpos (hmem t)
  have h1 : curvField f (theta t) ≤ A * Real.exp (-t / M) := by
    have := hdecay t
    rwa [abs_of_nonneg ht] at this
  have h2 : curvField f (theta t) ^ 2 ≤ (A * Real.exp (-t / M)) ^ 2 := by
    exact pow_le_pow_left₀ h0 h1 2
  have h3 : Real.exp (-t / M) ^ 2 ≤ Real.exp (-t / M) := by
    rw [← Real.exp_nat_mul]
    have : (2 : ℕ) * (-t / M) ≤ -t / M := by
      have : -t / M ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hM.le
      push_cast
      linarith
    exact Real.exp_le_exp.2 (by push_cast at this ⊢; linarith)
  have h4 : curvField f (theta t) ^ 2 ≤ A ^ 2 * Real.exp (-t / M) := by
    calc curvField f (theta t) ^ 2 ≤ (A * Real.exp (-t / M)) ^ 2 := h2
      _ = A ^ 2 * Real.exp (-t / M) ^ 2 := by ring
      _ ≤ A ^ 2 * Real.exp (-t / M) := by
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 := sqrt_one_add_sq_sub_one_le (curvField f (theta t))
  linarith

/-- The symmetric pointwise bound for `t ≤ 0`. -/
theorem sqrt_integrand_le' (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M)
    {t : ℝ} (ht : t ≤ 0) :
    Real.sqrt (1 + curvField f (theta t) ^ 2) - 1 ≤ A ^ 2 / 2 * Real.exp (t / M) := by
  have h0 : 0 ≤ curvField f (theta t) := curvField_nonneg hfpos (hmem t)
  have h1 : curvField f (theta t) ≤ A * Real.exp (t / M) := by
    have := hdecay t
    rwa [abs_of_nonpos ht, neg_neg] at this
  have h2 : curvField f (theta t) ^ 2 ≤ (A * Real.exp (t / M)) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : Real.exp (t / M) ^ 2 ≤ Real.exp (t / M) := by
    rw [← Real.exp_nat_mul]
    have ht' : t / M ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht hM.le
    exact Real.exp_le_exp.2 (by push_cast; linarith)
  have h4 : curvField f (theta t) ^ 2 ≤ A ^ 2 * Real.exp (t / M) := by
    calc curvField f (theta t) ^ 2 ≤ (A * Real.exp (t / M)) ^ 2 := h2
      _ = A ^ 2 * Real.exp (t / M) ^ 2 := by ring
      _ ≤ A ^ 2 * Real.exp (t / M) := mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 := sqrt_one_add_sq_sub_one_le (curvField f (theta t))
  linarith

/-- `∫_u^0 e^{t/M} dt ≤ M` for `u ≤ 0`. -/
theorem integral_exp_le (hM : 0 < M) (u : ℝ) :
    (∫ t in u..(0:ℝ), Real.exp (t / M)) ≤ M := by
  have hderiv : ∀ t ∈ uIcc u (0:ℝ), HasDerivAt (fun t => M * Real.exp (t / M))
      (Real.exp (t / M)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t / M) (1 / M) t := by
      simpa using (hasDerivAt_id t).div_const M
    have h2 := (h1.exp).const_mul M
    have hval : M * (Real.exp (t / M) * M⁻¹) = Real.exp (t / M) := by field_simp
    simpa [hval] using h2
  have hcont : IntervalIntegrable (fun t : ℝ => Real.exp (t / M)) volume u 0 :=
    (Real.continuous_exp.comp (by continuity)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
  have hpos : 0 < Real.exp (u / M) := Real.exp_pos _
  simp only [zero_div, Real.exp_zero, mul_one]
  nlinarith

/-- For `u ≥ 0`: `σ(u) ≤ u + A²M/2`. -/

theorem frontArclength_le (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hthetac : Continuous theta) (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M)
    {u : ℝ} (hu : 0 ≤ u) :
    frontArclength f theta u ≤ u + A ^ 2 * M / 2 := by
  have hGc : Continuous (curvField f) := (contDiff_curvField hf hfpos).continuous
  have hkc : Continuous fun t => curvField f (theta t) := hGc.comp hthetac
  have hg : Continuous fun t => Real.sqrt (1 + curvField f (theta t) ^ 2) :=
    (continuous_const.add (hkc.pow 2)).sqrt
  have hbnd : Continuous fun t : ℝ => A ^ 2 / 2 * Real.exp (-t / M) :=
    continuous_const.mul (Real.continuous_exp.comp (by continuity))
  have hsplit : frontArclength f theta u - u
      = ∫ t in (0:ℝ)..u, (Real.sqrt (1 + curvField f (theta t) ^ 2) - 1) := by
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) intervalIntegrable_const]
    simp [frontArclength]
  have hmono : (∫ t in (0:ℝ)..u, (Real.sqrt (1 + curvField f (theta t) ^ 2) - 1))
      ≤ ∫ t in (0:ℝ)..u, A ^ 2 / 2 * Real.exp (-t / M) := by
    refine intervalIntegral.integral_mono_on hu
      ((hg.sub continuous_const).intervalIntegrable _ _) (hbnd.intervalIntegrable _ _) ?_
    intro t ht
    exact sqrt_integrand_le hfpos hmem hdecay hM ht.1
  have hlast : (∫ t in (0:ℝ)..u, A ^ 2 / 2 * Real.exp (-t / M)) ≤ A ^ 2 / 2 * M := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_exp_neg_le hM u) (by positivity)
  have : frontArclength f theta u - u ≤ A ^ 2 / 2 * M := by
    rw [hsplit]; exact le_trans hmono hlast
  linarith

/-- For `u ≤ 0`: `σ(u) ≥ u - A²M/2`. -/
theorem le_frontArclength (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hthetac : Continuous theta) (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M)
    {u : ℝ} (hu : u ≤ 0) :
    u - A ^ 2 * M / 2 ≤ frontArclength f theta u := by
  have hGc : Continuous (curvField f) := (contDiff_curvField hf hfpos).continuous
  have hkc : Continuous fun t => curvField f (theta t) := hGc.comp hthetac
  have hg : Continuous fun t => Real.sqrt (1 + curvField f (theta t) ^ 2) :=
    (continuous_const.add (hkc.pow 2)).sqrt
  have hbnd : Continuous fun t : ℝ => A ^ 2 / 2 * Real.exp (t / M) :=
    continuous_const.mul (Real.continuous_exp.comp (by continuity))
  have hsplit : frontArclength f theta u - u
      = -∫ t in u..(0:ℝ), (Real.sqrt (1 + curvField f (theta t) ^ 2) - 1) := by
    rw [← intervalIntegral.integral_symm, intervalIntegral.integral_sub
      (hg.intervalIntegrable _ _) intervalIntegrable_const]
    simp [frontArclength]
  have hmono : (∫ t in u..(0:ℝ), (Real.sqrt (1 + curvField f (theta t) ^ 2) - 1))
      ≤ ∫ t in u..(0:ℝ), A ^ 2 / 2 * Real.exp (t / M) := by
    refine intervalIntegral.integral_mono_on hu
      ((hg.sub continuous_const).intervalIntegrable _ _) (hbnd.intervalIntegrable _ _) ?_
    intro t ht
    exact sqrt_integrand_le' hfpos hmem hdecay hM ht.2
  have hlast : (∫ t in u..(0:ℝ), A ^ 2 / 2 * Real.exp (t / M)) ≤ A ^ 2 / 2 * M := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_exp_le hM u) (by positivity)
  have : -(A ^ 2 / 2 * M) ≤ frontArclength f theta u - u := by
    rw [hsplit]
    linarith [le_trans hmono hlast]
  linarith

/-! ### From the rear arclength to the front arclength -/

theorem hasDerivAt_frontArclength (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hthetac : Continuous theta) (u : ℝ) :
    HasDerivAt (frontArclength f theta) (Real.sqrt (1 + curvField f (theta u) ^ 2)) u := by
  have hGc : Continuous (curvField f) := (contDiff_curvField hf hfpos).continuous
  have hg : Continuous fun t => Real.sqrt (1 + curvField f (theta t) ^ 2) :=
    (continuous_const.add ((hGc.comp hthetac).pow 2)).sqrt
  exact intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt

/-- The front arclength differs from the rear arclength by at most `B = A²M/2`,
in absolute value. -/
theorem abs_frontArclength_le (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hthetac : Continuous theta) (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M)
    (u : ℝ) : |frontArclength f theta u| ≤ |u| + A ^ 2 * M / 2 := by
  have hderiv := hasDerivAt_frontArclength hf hfpos hthetac
  have hge : ∀ t, (1:ℝ) ≤ Real.sqrt (1 + curvField f (theta t) ^ 2) := by
    intro t
    have h1 : (1:ℝ) ≤ 1 + curvField f (theta t) ^ 2 := by
      nlinarith [sq_nonneg (curvField f (theta t))]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ _ := Real.sqrt_le_sqrt h1
  rcases le_or_gt 0 u with hu | hu
  · have h1 : u ≤ frontArclength f theta u := by
      have := ArclengthInverse.le_of_deriv_ge (c := 1) hderiv hge hu
      rw [frontArclength_zero] at this
      linarith
    have h2 := frontArclength_le hf hfpos hthetac hmem hdecay hM hu
    rw [abs_of_nonneg (le_trans hu h1), abs_of_nonneg hu]
    linarith
  · have h1 : frontArclength f theta u ≤ u := by
      have := ArclengthInverse.ge_of_deriv_ge (c := 1) hderiv hge hu.le
      rw [frontArclength_zero] at this
      linarith
    have h2 := le_frontArclength hf hfpos hthetac hmem hdecay hM hu.le
    rw [abs_of_nonpos (le_trans h1 hu.le), abs_of_nonpos hu.le]
    linarith

/-- **The pulse state stays far out.**  For the inverse `x` of the front
arclength, `|x(s)| ≥ |s| - B`. -/
theorem abs_pulseState_ge (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hthetac : Continuous theta) (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hM : 0 < M)
    {x : ℝ → ℝ} (hxinv : ∀ s, frontArclength f theta (x s) = s) (s : ℝ) :
    |s| - A ^ 2 * M / 2 ≤ |x s| := by
  have := abs_frontArclength_le hf hfpos hthetac hmem hdecay hM (x s)
  rw [hxinv s] at this
  linarith

/-! ### Decay of the pulse and of its derivatives -/

theorem pulseField_le_curvField (hfpos : ∀ t, 0 < f t) {t : ℝ} (ht : t ∈ Icc 0 π) :
    pulseField f t ≤ curvField f t := by
  have h0 : 0 ≤ curvField f t := curvField_nonneg hfpos ht
  have h1 : (1:ℝ) ≤ Real.sqrt (1 + curvField f t ^ 2) := by
    have h : (1:ℝ) ≤ 1 + curvField f t ^ 2 := by nlinarith [sq_nonneg (curvField f t)]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ _ := Real.sqrt_le_sqrt h
  rw [pulseField]
  exact div_le_self h0 h1

/-- **Exponential decay of the steering pulse in the front arclength.** -/
theorem pulse_decay (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {theta : ℝ → ℝ} (hthetac : Continuous theta) (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) (hA : 0 ≤ A) (hM : 0 < M)
    {x : ℝ → ℝ} (hxinv : ∀ s, frontArclength f theta (x s) = s) (s : ℝ) :
    pulseField f (theta (x s)) ≤ A * Real.exp (A ^ 2 / 2) * Real.exp (-|s| / M) := by
  have h1 : pulseField f (theta (x s)) ≤ curvField f (theta (x s)) :=
    pulseField_le_curvField hfpos (hmem _)
  have h2 : curvField f (theta (x s)) ≤ A * Real.exp (-|x s| / M) := hdecay _
  have h3 : |s| - A ^ 2 * M / 2 ≤ |x s| :=
    abs_pulseState_ge hf hfpos hthetac hmem hdecay hM hxinv s
  have h4 : -|x s| / M ≤ -|s| / M + A ^ 2 / 2 := by
    rw [div_add' _ _ _ hM.ne', div_le_div_iff_of_pos_right hM]
    nlinarith
  have h5 : Real.exp (-|x s| / M) ≤ Real.exp (-|s| / M) * Real.exp (A ^ 2 / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  calc pulseField f (theta (x s)) ≤ A * Real.exp (-|x s| / M) := le_trans h1 h2
    _ ≤ A * (Real.exp (-|s| / M) * Real.exp (A ^ 2 / 2)) := mul_le_mul_of_nonneg_left h5 hA
    _ = A * Real.exp (A ^ 2 / 2) * Real.exp (-|s| / M) := by ring

/-- A relative bound together with an exponential bound on the quantity gives an
exponential bound. -/
theorem decay_of_relative {q F : ℝ → ℝ} {A' C : ℝ}
    (hq : ∀ s, q s ≤ A' * Real.exp (-|s| / M)) (hC0 : 0 ≤ C)
    (hF : ∀ s, |F s| ≤ C * q s) (s : ℝ) :
    |F s| ≤ C * A' * Real.exp (-|s| / M) := by
  calc |F s| ≤ C * q s := hF s
    _ ≤ C * (A' * Real.exp (-|s| / M)) := mul_le_mul_of_nonneg_left (hq s) hC0
    _ = C * A' * Real.exp (-|s| / M) := by ring

/-- **Exponential decay of every derivative of the steering pulse.** -/
theorem abs_iteratedDeriv_pulse_decay (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    {w : ℝ → ℝ} (hmem : ∀ s, w s ∈ Icc 0 π)
    (hderiv : ∀ s, HasDerivAt w (pulseField f (w s)) s) {A' : ℝ}
    (hdecay : ∀ s, pulseField f (w s) ≤ A' * Real.exp (-|s| / M)) (j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s,
      |iteratedDeriv j (fun s => pulseField f (w s)) s| ≤ D * Real.exp (-|s| / M) := by
  obtain ⟨D, hD0, hD⟩ := abs_iteratedDeriv_pulse_le hf hfpos hmem hderiv j
  have hA' : 0 ≤ A' := by
    have h0 := le_trans (pulseField_nonneg hfpos (hmem 0)) (hdecay 0)
    by_contra hneg
    push_neg at hneg
    nlinarith [Real.exp_pos (-|(0:ℝ)| / M)]
  exact ⟨D * A', by positivity, decay_of_relative hdecay hD0 hD⟩

/-! ### The exponential decay statement of the lemma *Hairpin pulse estimates* -/

/-- **All derivatives of the curvature and of the steering pulse decay
exponentially at both ends.**  For a profile `f` smooth and positive on the
line, with `M` an upper bound for `f` on `[0, π]`, the hairpin has an arclength
parametrization `θ` with curvature `K_* = G ∘ θ`, and a front-arclength
parametrization `x` with pulse `y = G₂ ∘ θ ∘ x = sin δ`, such that for every
order `j`

```
  |K_*^{(j)}(u)| ≤ C_j e^{-|u|/M},        |y^{(j)}(s)| ≤ D_j e^{-|s|/M}.
```
-/
theorem hairpin_pulse_exponential_decay (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ (M : ℝ) (theta x : ℝ → ℝ), 0 < M ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π/2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u,
        |iteratedDeriv j (fun u => curvField f (theta u)) u| ≤ C * Real.exp (-|u| / M)) ∧
      (∀ j : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ s,
        |iteratedDeriv j (fun s => pulseField f (theta (x s))) s| ≤ D * Real.exp (-|s| / M)) := by
  have hcontf : Continuous f := hf.continuous
  have hne : (Icc (0:ℝ) π).Nonempty := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩⟩
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  obtain ⟨t₁, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Icc (0:ℝ) π) hne hcontf.continuousOn
  have hm : 0 < f t₀ := hfpos t₀
  have hM : 0 < f t₁ := hfpos t₁
  have hlow : ∀ t ∈ Ioo (0:ℝ) π, f t₀ ≤ f t := fun t ht => hmin ⟨ht.1.le, ht.2.le⟩
  have hup : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ f t₁ := fun t ht => hmax ⟨ht.1.le, ht.2.le⟩
  obtain ⟨theta, hmem, hval, -, -, hthetac, hderiv⟩ :=
    HairpinArclength.exists_angle hcontf.continuousOn hm hlow
  have hmem' : ∀ u, theta u ∈ Icc (0:ℝ) π := fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩
  have hderiv' : ∀ u, HasDerivAt theta (curvField f (theta u)) u := hderiv
  have hA : (0:ℝ) ≤ 2 / f t₀ := by positivity
  have hdecay : ∀ u, curvField f (theta u) ≤ (2 / f t₀) * Real.exp (-|u| / f t₁) := fun u =>
    HairpinArclength.curvature_decay_arclength hcontf.continuousOn hm hlow hup hmem hval u
  obtain ⟨x, hxinv, hxmem, hxderiv⟩ := exists_pulseState hf hfpos hmem' hderiv'
  have hpulse : ∀ s, pulseField f (theta (x s))
      ≤ (2 / f t₀) * Real.exp ((2 / f t₀) ^ 2 / 2) * Real.exp (-|s| / f t₁) :=
    fun s => pulse_decay hf hfpos hthetac hmem' hdecay hA hM hxinv s
  refine ⟨f t₁, theta, x, hM, hmem, hval, hderiv', hxinv, hxderiv, fun j => ?_, fun j => ?_⟩
  · exact abs_iteratedDeriv_curv_decay hf hfpos hmem' hderiv' hdecay j
  · exact abs_iteratedDeriv_pulse_decay hf hfpos hxmem hxderiv hpulse j

/-! ### A worked instance

The hypotheses are consistent: the constant profile `f ≡ 2` is smooth and
positive on the line. -/

example : ∃ M : ℝ, 0 < M := by
  obtain ⟨M, -, -, hM, -⟩ :=
    hairpin_pulse_exponential_decay (f := fun _ => 2) contDiff_const (fun _ => two_pos)
  exact ⟨M, hM⟩

end HairpinRelative
