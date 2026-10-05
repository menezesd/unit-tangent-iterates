module

public import Mathlib

/-!
# The periodic resolvent of `1 + d/dx`

For `L > 0` and an `L`-periodic continuous function `f`,
`(ℛ_L f)(x) = (1 - e^{-L})⁻¹ ∫_{x-L}^x e^{-(x-t)} f(t) dt`
is the unique periodic solution `u` of `u' + u = f`.  Its kernel is positive with
integral one.
-/

@[expose] public section

namespace Ovals

open Real intervalIntegral MeasureTheory

/-- The periodic resolvent `ℛ_L` of `1 + d/dx` on `ℝ/Lℤ`. -/
noncomputable def periodicResolvent (L : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - Real.exp (-L))⁻¹ * ∫ t in (x - L)..x, Real.exp (t - x) * f t

variable {L : ℝ}

theorem one_sub_exp_neg_pos (hL : 0 < L) : 0 < 1 - Real.exp (-L) := by
  have : Real.exp (-L) < 1 := by simpa using Real.exp_lt_exp.2 (show -L < 0 by linarith)
  linarith

theorem integral_exp_kernel (x : ℝ) :
    ∫ t in (x - L)..x, Real.exp (t - x) = 1 - Real.exp (-L) := by
  have : ∀ t, Real.exp (t - x) = Real.exp (-x) * Real.exp t := fun t => by
    rw [← Real.exp_add]; ring_nf
  simp_rw [this, intervalIntegral.integral_const_mul, integral_exp, mul_sub, ← Real.exp_add]
  ring_nf; simp

theorem periodicResolvent_const (hL : 0 < L) (c x : ℝ) :
    periodicResolvent L (fun _ => c) x = c := by
  unfold periodicResolvent
  simp_rw [intervalIntegral.integral_mul_const, integral_exp_kernel]
  field_simp [(one_sub_exp_neg_pos hL).ne']

/-- The resolvent is order preserving. -/
theorem periodicResolvent_mono (hL : 0 < L) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfg : ∀ t, f t ≤ g t) (x : ℝ) :
    periodicResolvent L f x ≤ periodicResolvent L g x := by
  unfold periodicResolvent
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (one_sub_exp_neg_pos hL).le)
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact ((Real.continuous_exp.comp (continuous_id.sub continuous_const)).mul hf).intervalIntegrable _ _
  · exact ((Real.continuous_exp.comp (continuous_id.sub continuous_const)).mul hg).intervalIntegrable _ _
  · intro t _
    exact mul_le_mul_of_nonneg_left (hfg t) (Real.exp_pos _).le

theorem periodicResolvent_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (x : ℝ) :
    periodicResolvent L f x - periodicResolvent L g x = periodicResolvent L (f - g) x := by
  unfold periodicResolvent
  rw [← mul_sub, ← intervalIntegral.integral_sub]
  · simp [mul_sub]
  · exact ((Real.continuous_exp.comp (continuous_id.sub continuous_const)).mul hf).intervalIntegrable _ _
  · exact ((Real.continuous_exp.comp (continuous_id.sub continuous_const)).mul hg).intervalIntegrable _ _

/-- Bounds are preserved by the resolvent (positive kernel of integral one). -/
theorem periodicResolvent_mem_Icc (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hab : ∀ t, f t ∈ Set.Icc a b) (x : ℝ) : periodicResolvent L f x ∈ Set.Icc a b := by
  constructor
  · rw [← periodicResolvent_const hL a x]
    exact periodicResolvent_mono hL continuous_const hf (fun t => (hab t).1) x
  · rw [← periodicResolvent_const hL b x]
    exact periodicResolvent_mono hL hf continuous_const (fun t => (hab t).2) x

/-- `ℛ_L` is `1`-Lipschitz in the sup norm. -/
theorem abs_periodicResolvent_sub_le (hL : 0 < L) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) {D : ℝ} (hD : ∀ t, |f t - g t| ≤ D) (x : ℝ) :
    |periodicResolvent L f x - periodicResolvent L g x| ≤ D := by
  rw [periodicResolvent_sub hf hg]
  have := periodicResolvent_mem_Icc hL (hf.sub hg) (a := -D) (b := D)
    (fun t => abs_le.1 (hD t)) x
  exact abs_le.2 this

theorem periodicResolvent_periodic {f : ℝ → ℝ} (hfp : Function.Periodic f L) :
    Function.Periodic (periodicResolvent L f) L := by
  intro x
  unfold periodicResolvent
  congr 1
  have := intervalIntegral.integral_comp_add_right (fun t => Real.exp (t - (x + L)) * f t)
    (a := x - L) (b := x) L
  simp only [sub_add_cancel] at this
  rw [add_sub_cancel_right, ← this]
  congr 1; ext t
  rw [hfp t]; ring_nf

/-- `ℛ_L f` solves `u' = f - u`. -/
theorem hasDerivAt_periodicResolvent (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f)
    (hfp : Function.Periodic f L) (x : ℝ) :
    HasDerivAt (periodicResolvent L f) (f x - periodicResolvent L f x) x := by
  set c := (1 - Real.exp (-L))⁻¹
  have hc : c * (1 - Real.exp (-L)) = 1 := inv_mul_cancel₀ (one_sub_exp_neg_pos hL).ne'
  have hcont : Continuous (fun t => Real.exp t * f t) := Real.continuous_exp.mul hf
  have hG : HasDerivAt (fun y => ∫ t in (0:ℝ)..y, Real.exp t * f t) (Real.exp x * f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have hG2 : HasDerivAt (fun y => ∫ t in (0:ℝ)..(y - L), Real.exp t * f t)
      (Real.exp (x - L) * f (x - L)) x := by
    have h := intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 (x - L))
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
    have := h.comp x ((hasDerivAt_id x).sub_const L)
    simpa using this
  have hfun : periodicResolvent L f = fun y => c * (Real.exp (-y) *
      ((∫ t in (0:ℝ)..y, Real.exp t * f t) - ∫ t in (0:ℝ)..(y - L), Real.exp t * f t)) := by
    funext y
    unfold periodicResolvent
    rw [intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _), ← intervalIntegral.integral_const_mul (rexp (-y))]
    congr 2; funext t; rw [show t - y = -y + t by ring, Real.exp_add]; ring
  rw [hfun]
  have := (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).mul (hG.sub hG2)).const_mul c
  convert this using 1
  simp only [Function.comp_apply, Pi.sub_apply]
  rw [hfp.sub_eq x]
  have e1 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have e2 : Real.exp (-x) * Real.exp (x - L) = Real.exp (-L) := by
    rw [← Real.exp_add]; ring_nf
  linear_combination (-(f x)) * hc - c * f x * e1 + c * f x * e2

theorem continuous_periodicResolvent (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f)
    (hfp : Function.Periodic f L) : Continuous (periodicResolvent L f) :=
  continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_periodicResolvent hL hf hfp x).continuousAt

/-- Positivity: `ℛ_L f ≥ e^{-L}(1-e^{-L})⁻¹ ∫₀ᴸ f` for nonnegative periodic `f`. -/
theorem periodicResolvent_ge (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f)
    (hfp : Function.Periodic f L) (hf0 : ∀ t, 0 ≤ f t) (x : ℝ) :
    (1 - Real.exp (-L))⁻¹ * (Real.exp (-L) * ∫ t in (0 : ℝ)..L, f t)
      ≤ periodicResolvent L f x := by
  unfold periodicResolvent
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (one_sub_exp_neg_pos hL).le)
  have hshift : ∫ t in (x - L)..x, f t = ∫ t in (0:ℝ)..L, f t := by
    have := hfp.intervalIntegral_add_eq (x - L) 0
    simpa using this
  rw [← hshift, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact (continuous_const.mul hf).intervalIntegrable _ _
  · exact ((Real.continuous_exp.comp (continuous_id.sub continuous_const)).mul
      hf).intervalIntegrable _ _
  · intro t ht
    apply mul_le_mul_of_nonneg_right _ (hf0 t)
    exact Real.exp_le_exp.2 (by linarith [ht.1])

/-- Uniqueness: a periodic solution of `u' = f - u` equals `ℛ_L f`. -/
theorem eq_periodicResolvent_of_hasDerivAt (hL : 0 < L) {f u : ℝ → ℝ} (hf : Continuous f)
    (hfp : Function.Periodic f L) (hup : Function.Periodic u L)
    (hu : ∀ x, HasDerivAt u (f x - u x) x) : u = periodicResolvent L f := by
  set w := fun x => u x - periodicResolvent L f x with hw_def
  have hw : ∀ x, HasDerivAt (fun x => w x * Real.exp x) 0 x := by
    intro x
    have := ((hu x).sub (hasDerivAt_periodicResolvent hL hf hfp x)).mul (Real.hasDerivAt_exp x)
    convert this using 1
    simp only [Pi.sub_apply]
    ring
  have hconst : ∀ x, w x * Real.exp x = w 0 * Real.exp 0 := fun x =>
    is_const_of_deriv_eq_zero (fun x => (hw x).differentiableAt) (fun x => (hw x).deriv) x 0
  have hwp : Function.Periodic w L := fun x => by
    simp only [w]; rw [hup x, periodicResolvent_periodic hfp x]
  have h0 : w 0 = 0 := by
    have h1 := hconst L
    rw [hwp.eq, Real.exp_zero] at h1
    have hne : Real.exp L ≠ 1 := by
      have := Real.exp_lt_exp.2 hL; rw [Real.exp_zero] at this; exact this.ne'
    by_contra hc
    exact hne (mul_left_cancel₀ hc h1)
  funext x
  have := hconst x
  rw [h0, zero_mul] at this
  have hx : w x = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (Real.exp_pos x).ne'
  simp only [w] at hx
  linarith

end Ovals

end
