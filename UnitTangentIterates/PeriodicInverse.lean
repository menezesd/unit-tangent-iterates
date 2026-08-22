import Mathlib

/-!
# The periodic inverse of `1 + ∂ₓ`

This file formalizes the explicit operator appearing in the proof of the
inverse Jacobi estimates (Lemma 6.4) of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*: on a rear circle of
length `ℓ`, the periodic inverse of `1 + ∂ₓ` is

`(ℛ_ℓ f)(x) = (1 - e^{-ℓ})⁻¹ ∫_{x-ℓ}^{x} e^{-(x-t)} f(t) dt`.

Main results:

* `periodicInverse_kernel_integral` : the kernel is a probability kernel,
  `(1 - e^{-ℓ})⁻¹ ∫_{x-ℓ}^{x} e^{-(x-t)} dt = 1`;
* `periodicInverse_hasDerivAt` : `ℛ_ℓ f` solves `u' + u = f`;
* `periodicInverse_periodic` : `ℛ_ℓ f` is `ℓ`-periodic;
* `periodicInverse_abs_le` : the `L¹ → L^∞` bound.
-/

noncomputable section

open Real MeasureTheory intervalIntegral

namespace PeriodicInverse

/-- The periodic inverse of `1 + ∂ₓ` on a circle of length `ℓ`. -/
noncomputable def periodicInverse (l : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - Real.exp (-l))⁻¹ * ∫ t in (x - l)..x, Real.exp (-(x - t)) * f t

/-- The kernel of `ℛ_ℓ` is positive with total mass one. -/
theorem periodicInverse_kernel_integral {l : ℝ} (hl : 0 < l) (x : ℝ) :
    (1 - Real.exp (-l))⁻¹ * ∫ t in (x - l)..x, Real.exp (-(x - t)) = 1 := by
  have hint : (∫ t in (x - l)..x, Real.exp (-(x - t))) = 1 - Real.exp (-l) := by
    have h : (fun t : ℝ => Real.exp (-(x - t))) = fun t : ℝ => Real.exp (-x) * Real.exp t := by
      funext t
      rw [← Real.exp_add]
      ring_nf
    rw [h, intervalIntegral.integral_const_mul, integral_exp]
    have : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]; simp
    have h2 : Real.exp (-x) * Real.exp (x - l) = Real.exp (-l) := by
      rw [← Real.exp_add]; ring_nf
    rw [mul_sub, this, h2]
  rw [hint]
  have hne : 1 - Real.exp (-l) ≠ 0 := by
    have : Real.exp (-l) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  field_simp

section Solve

variable {l : ℝ} {f : ℝ → ℝ}

/-- `ℛ_ℓ f` in terms of a primitive of `t ↦ e^t f(t)`. -/
lemma periodicInverse_eq (hf : Continuous f) (l : ℝ) (x : ℝ) :
    periodicInverse l f x
      = (1 - Real.exp (-l))⁻¹ * Real.exp (-x) *
          ((∫ t in (0:ℝ)..x, Real.exp t * f t) - ∫ t in (0:ℝ)..(x - l), Real.exp t * f t) := by
  have hcont : Continuous (fun t : ℝ => Real.exp t * f t) := by fun_prop
  have hsplit : (∫ t in (x - l)..x, Real.exp t * f t)
      = (∫ t in (0:ℝ)..x, Real.exp t * f t) - ∫ t in (0:ℝ)..(x - l), Real.exp t * f t := by
    rw [← intervalIntegral.integral_interval_sub_left
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hrw : (∫ t in (x - l)..x, Real.exp (-(x - t)) * f t)
      = Real.exp (-x) * ∫ t in (x - l)..x, Real.exp t * f t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  rw [periodicInverse, hrw, hsplit]
  ring

/-- **`ℛ_ℓ f` solves `u' + u = f`** when `f` is continuous and `ℓ`-periodic. -/
theorem periodicInverse_hasDerivAt (hl : 0 < l) (hf : Continuous f)
    (hper : Function.Periodic f l) (x : ℝ) :
    HasDerivAt (periodicInverse l f) (f x - periodicInverse l f x) x := by
  have hcont : Continuous (fun t : ℝ => Real.exp t * f t) := by fun_prop
  set c : ℝ := (1 - Real.exp (-l))⁻¹ with hc
  set A : ℝ → ℝ := fun y => ∫ t in (0:ℝ)..y, Real.exp t * f t with hA
  have hAderiv : ∀ y : ℝ, HasDerivAt A (Real.exp y * f y) y := fun y =>
    (hcont.integral_hasStrictDerivAt (0:ℝ) y).hasDerivAt
  have hu : periodicInverse l f = fun y => c * (Real.exp (-y) * (A y - A (y - l))) := by
    funext y
    rw [periodicInverse_eq hf l y, hA]
    ring
  have hBderiv : HasDerivAt (fun y => A y - A (y - l))
      (Real.exp x * f x - Real.exp (x - l) * f (x - l)) x := by
    have h1 := hAderiv x
    have h2 : HasDerivAt (fun y => A (y - l)) (Real.exp (x - l) * f (x - l)) x := by
      simpa using (hAderiv (x - l)).comp x ((hasDerivAt_id x).sub_const l)
    exact h1.sub h2
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa using (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hprod := (hexp.mul hBderiv).const_mul c
  rw [hu]
  convert hprod using 1
  -- identify the derivative
  have hfx : f (x - l) = f x := by
    have := hper.sub_eq x
    simpa using this
  have hne : 1 - Real.exp (-l) ≠ 0 := by
    have : Real.exp (-l) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hexpl : Real.exp (-x) * Real.exp (x - l) = Real.exp (-l) := by
    rw [← Real.exp_add]; ring_nf
  have hexpx : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]; simp
  have hcinv : c * (1 - Real.exp (-l)) = 1 := by
    rw [hc]; field_simp
  simp only [hfx]
  linear_combination (-(f x)) * hcinv - (c * f x) * hexpx + (c * f x) * hexpl

/-- `ℛ_ℓ f` is `ℓ`-periodic. -/
theorem periodicInverse_periodic (hper : Function.Periodic f l) :
    Function.Periodic (periodicInverse l f) l := by
  intro x
  simp only [periodicInverse]
  congr 1
  have h := intervalIntegral.integral_comp_add_right
    (a := x - l) (b := x) (fun t => Real.exp (-(x + l - t)) * f t) l
  rw [show x - l + l = x from by ring] at h
  rw [show x + l - l = x from by ring, ← h]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [show x + l - (t + l) = x - t from by ring, hper t]

/-- The `L¹ → L^∞` bound for `ℛ_ℓ`. -/
theorem periodicInverse_abs_le (hl : 0 < l) (hf : Continuous f) (x : ℝ) :
    |periodicInverse l f x| ≤ (1 - Real.exp (-l))⁻¹ * ∫ t in (x - l)..x, |f t| := by
  have hle : x - l ≤ x := by linarith
  have hpos : (0:ℝ) < 1 - Real.exp (-l) := by
    have : Real.exp (-l) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hcpos : (0:ℝ) < (1 - Real.exp (-l))⁻¹ := inv_pos.mpr hpos
  have h1 : |∫ t in (x - l)..x, Real.exp (-(x - t)) * f t|
      ≤ ∫ t in (x - l)..x, |Real.exp (-(x - t)) * f t| :=
    intervalIntegral.abs_integral_le_integral_abs hle
  have hc1 : Continuous fun t : ℝ => |Real.exp (-(x - t)) * f t| := by fun_prop
  have hc2 : Continuous fun t : ℝ => |f t| := by fun_prop
  have h2 : (∫ t in (x - l)..x, |Real.exp (-(x - t)) * f t|) ≤ ∫ t in (x - l)..x, |f t| := by
    refine intervalIntegral.integral_mono_on hle (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _) (fun t ht => ?_)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(x - t)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := ht.2; linarith)
    nlinarith [abs_nonneg (f t)]
  rw [periodicInverse, abs_mul, abs_of_pos hcpos]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) hcpos.le

end Solve

end PeriodicInverse
