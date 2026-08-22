import Mathlib

/-!
# The periodic Green operator of `∂ₓ + a`

This file formalizes the variable-coefficient periodic inverse appearing in the
lemma *Smooth dependence of the selected rear* of the paper *A Noncircular Oval
with Convex Unit-Tangent Iterates*: the periodic linearization of the steering
equation is

```
  w_φ + q(φ) cos δ · w = f ,
```

whose zeroth-order coefficient is bounded below by `κ̂^{-1}√(1-κ̂²) > 0` on the
selected strip.  For such a positive periodic coefficient `a`, the periodic
linear operator is invertible with a positive Green kernel and uniform bounds;
the explicit inverse is

```
  (𝒢 f)(x) = (1 - e^{-A(ℓ)})⁻¹ ∫_{x-ℓ}^{x} e^{-(A(x) - A(t))} f(t) dt ,
  A(x) = ∫₀ˣ a .
```

Main results:

* `periodicGreen_kernel_mass` : the kernel is positive and has total mass one
  for the weight `a(t) dt`;
* `periodicGreen_hasDerivAt` : `𝒢 f` solves `w' + a w = f`;
* `periodicGreen_periodic` : `𝒢 f` is `ℓ`-periodic;
* `periodicGreen_abs_le` : the uniform `L¹ → L^∞` bound.

For `a ≡ 1` this is the operator `ℛ_ℓ` of `UnitTangentIterates.PeriodicInverse`.
-/

noncomputable section

open Real MeasureTheory intervalIntegral

namespace PeriodicGreen

variable {a f : ℝ → ℝ} {l : ℝ}

/-! ### The primitive of the coefficient -/

/-- The primitive `A(x) = ∫₀ˣ a` of the coefficient. -/
def prim (a : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, a t

lemma hasDerivAt_prim (ha : Continuous a) (x : ℝ) : HasDerivAt (prim a) (a x) x :=
  (ha.integral_hasStrictDerivAt (0:ℝ) x).hasDerivAt

lemma continuous_prim (ha : Continuous a) : Continuous (prim a) := by
  have hdiff : Differentiable ℝ (prim a) := fun x => (hasDerivAt_prim ha x).differentiableAt
  exact hdiff.continuous

lemma prim_sub_eq (ha : Continuous a) (x y : ℝ) :
    prim a x - prim a y = ∫ t in y..x, a t :=
  intervalIntegral.integral_interval_sub_left (ha.intervalIntegrable _ _)
    (ha.intervalIntegrable _ _)

/-- The primitive of a nonnegative coefficient is monotone. -/
lemma prim_sub_nonneg (ha : Continuous a) (ha0 : ∀ t, 0 ≤ a t) {x y : ℝ} (h : y ≤ x) :
    0 ≤ prim a x - prim a y := by
  rw [prim_sub_eq ha]
  exact intervalIntegral.integral_nonneg h (fun t _ => ha0 t)

/-- The primitive of an `ℓ`-periodic coefficient increases by exactly `A(ℓ)`
over one period. -/
lemma prim_sub_prim (ha : Continuous a) (hper : Function.Periodic a l) (x : ℝ) :
    prim a x - prim a (x - l) = prim a l := by
  rw [prim_sub_eq ha]
  have hshift : (∫ t in (x - l)..x, a t) = ∫ t in (0:ℝ)..l, a t := by
    simpa using hper.intervalIntegral_add_eq (x - l) 0
  rw [hshift, prim]

lemma prim_add (ha : Continuous a) (hper : Function.Periodic a l) (x : ℝ) :
    prim a (x + l) = prim a x + prim a l := by
  have := prim_sub_prim ha hper (x + l)
  simp only [add_sub_cancel_right] at this
  linarith

/-! ### The Green operator -/

/-- The periodic Green operator of `∂ₓ + a` on a circle of length `ℓ`. -/
def periodicGreen (a : ℝ → ℝ) (l : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 - Real.exp (-prim a l))⁻¹ * ∫ t in (x - l)..x, Real.exp (-(prim a x - prim a t)) * f t

/-- The normalizing constant is positive as soon as `A(ℓ) > 0`. -/
lemma one_sub_exp_pos (hA : 0 < prim a l) : (0:ℝ) < 1 - Real.exp (-prim a l) := by
  have : Real.exp (-prim a l) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

/-- The primitive of `t ↦ e^{A(t)} f(t)`. -/
private def bigB (a f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t in (0:ℝ)..y, Real.exp (prim a t) * f t

private lemma hasDerivAt_bigB (ha : Continuous a) (hf : Continuous f) (y : ℝ) :
    HasDerivAt (bigB a f) (Real.exp (prim a y) * f y) y := by
  have hcont : Continuous fun t : ℝ => Real.exp (prim a t) * f t :=
    ((Real.continuous_exp.comp (continuous_prim ha)).mul hf)
  exact (hcont.integral_hasStrictDerivAt (0:ℝ) y).hasDerivAt

private lemma periodicGreen_eq (ha : Continuous a) (hf : Continuous f) (x : ℝ) :
    periodicGreen a l f x
      = (1 - Real.exp (-prim a l))⁻¹ * Real.exp (-prim a x) *
          (bigB a f x - bigB a f (x - l)) := by
  have hcont : Continuous fun t : ℝ => Real.exp (prim a t) * f t :=
    ((Real.continuous_exp.comp (continuous_prim ha)).mul hf)
  have hsplit : (∫ t in (x - l)..x, Real.exp (prim a t) * f t)
      = bigB a f x - bigB a f (x - l) := by
    simp only [bigB]
    rw [← intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
  have hrw : (∫ t in (x - l)..x, Real.exp (-(prim a x - prim a t)) * f t)
      = Real.exp (-prim a x) * ∫ t in (x - l)..x, Real.exp (prim a t) * f t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  rw [periodicGreen, hrw, hsplit]
  ring

/-- **The Green kernel is a probability kernel** for the weight `a(t) dt`. -/
theorem periodicGreen_kernel_mass (ha : Continuous a) (hper : Function.Periodic a l)
    (hA : 0 < prim a l) (x : ℝ) :
    (1 - Real.exp (-prim a l))⁻¹ *
        ∫ t in (x - l)..x, Real.exp (-(prim a x - prim a t)) * a t = 1 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun y => Real.exp (prim a y))
      (Real.exp (prim a t) * a t) t := by
    intro t
    simpa [mul_comm] using (Real.hasDerivAt_exp (prim a t)).comp t (hasDerivAt_prim ha t)
  have hcont : Continuous fun t : ℝ => Real.exp (prim a t) * a t :=
    ((Real.continuous_exp.comp (continuous_prim ha)).mul ha)
  have hFTC : (∫ t in (x - l)..x, Real.exp (prim a t) * a t)
      = Real.exp (prim a x) - Real.exp (prim a (x - l)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable _ _)
  have hrw : (∫ t in (x - l)..x, Real.exp (-(prim a x - prim a t)) * a t)
      = Real.exp (-prim a x) * ∫ t in (x - l)..x, Real.exp (prim a t) * a t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  have hsub := prim_sub_prim ha hper x
  have hexp1 : Real.exp (-prim a x) * Real.exp (prim a x) = 1 := by
    rw [← Real.exp_add]; simp
  have hexp2 : Real.exp (-prim a x) * Real.exp (prim a (x - l)) = Real.exp (-prim a l) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have hne : (1 - Real.exp (-prim a l)) ≠ 0 := ne_of_gt (one_sub_exp_pos hA)
  rw [hrw, hFTC, mul_sub, hexp1, hexp2]
  field_simp

/-- **`𝒢 f` solves `w' + a w = f`** for a continuous `ℓ`-periodic right-hand
side. -/
theorem periodicGreen_hasDerivAt (ha : Continuous a) (haper : Function.Periodic a l)
    (hA : 0 < prim a l) (hf : Continuous f) (hfper : Function.Periodic f l) (x : ℝ) :
    HasDerivAt (periodicGreen a l f) (f x - a x * periodicGreen a l f x) x := by
  have hu : periodicGreen a l f
      = fun y => (1 - Real.exp (-prim a l))⁻¹ *
          (Real.exp (-prim a y) * (bigB a f y - bigB a f (y - l))) := by
    funext y
    rw [periodicGreen_eq ha hf y]
    ring
  have hexp : HasDerivAt (fun y => Real.exp (-prim a y))
      (-(a x) * Real.exp (-prim a x)) x := by
    have h1 : HasDerivAt (fun y => -prim a y) (-(a x)) x := (hasDerivAt_prim ha x).neg
    simpa [mul_comm] using (Real.hasDerivAt_exp (-prim a x)).comp x h1
  have hBderiv : HasDerivAt (fun y => bigB a f y - bigB a f (y - l))
      (Real.exp (prim a x) * f x - Real.exp (prim a (x - l)) * f (x - l)) x := by
    have h1 := hasDerivAt_bigB ha hf x
    have h2 : HasDerivAt (fun y => bigB a f (y - l))
        (Real.exp (prim a (x - l)) * f (x - l)) x := by
      simpa using (hasDerivAt_bigB ha hf (x - l)).comp x ((hasDerivAt_id x).sub_const l)
    exact h1.sub h2
  have hprod := (hexp.mul hBderiv).const_mul (1 - Real.exp (-prim a l))⁻¹
  rw [hu]
  refine hprod.congr_deriv ?_
  -- identify the two expressions for the derivative
  have hfx : f (x - l) = f x := by simpa using hfper.sub_eq x
  have hsub := prim_sub_prim ha haper x
  have hexp1 : Real.exp (-prim a x) * Real.exp (prim a x) = 1 := by
    rw [← Real.exp_add]; simp
  have hexp2 : Real.exp (-prim a x) * Real.exp (prim a (x - l)) = Real.exp (-prim a l) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have hne : (1 - Real.exp (-prim a l)) ≠ 0 := ne_of_gt (one_sub_exp_pos hA)
  have hcinv : (1 - Real.exp (-prim a l))⁻¹ * (1 - Real.exp (-prim a l)) = 1 := by
    field_simp
  simp only [hfx]
  linear_combination ((1 - Real.exp (-prim a l))⁻¹ * f x) * hexp1 -
    ((1 - Real.exp (-prim a l))⁻¹ * f x) * hexp2 + (f x) * hcinv

/-- **`𝒢 f` is `ℓ`-periodic.** -/
theorem periodicGreen_periodic (ha : Continuous a) (haper : Function.Periodic a l)
    (hfper : Function.Periodic f l) : Function.Periodic (periodicGreen a l f) l := by
  intro x
  simp only [periodicGreen]
  congr 1
  have h := intervalIntegral.integral_comp_add_right
    (a := x - l) (b := x) (fun t => Real.exp (-(prim a (x + l) - prim a t)) * f t) l
  rw [show x - l + l = x from by ring] at h
  rw [show x + l - l = x from by ring, ← h]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [prim_add ha haper x, prim_add ha haper t, hfper t]
  congr 2
  ring

/-- **The uniform `L¹ → L^∞` bound** for the Green operator of a nonnegative
coefficient. -/
theorem periodicGreen_abs_le (ha : Continuous a) (ha0 : ∀ t, 0 ≤ a t)
    (hA : 0 < prim a l) (hf : Continuous f) (hl : 0 < l) (x : ℝ) :
    |periodicGreen a l f x| ≤ (1 - Real.exp (-prim a l))⁻¹ * ∫ t in (x - l)..x, |f t| := by
  have hle : x - l ≤ x := by linarith
  have hcpos : (0:ℝ) < (1 - Real.exp (-prim a l))⁻¹ := inv_pos.mpr (one_sub_exp_pos hA)
  have h1 : |∫ t in (x - l)..x, Real.exp (-(prim a x - prim a t)) * f t|
      ≤ ∫ t in (x - l)..x, |Real.exp (-(prim a x - prim a t)) * f t| :=
    intervalIntegral.abs_integral_le_integral_abs hle
  have hcont1 : Continuous fun t : ℝ => |Real.exp (-(prim a x - prim a t)) * f t| := by
    have : Continuous fun t : ℝ => Real.exp (-(prim a x - prim a t)) * f t :=
      ((Real.continuous_exp.comp (continuous_const.sub (continuous_prim ha)).neg).mul hf)
    exact this.abs
  have hcont2 : Continuous fun t : ℝ => |f t| := hf.abs
  have h2 : (∫ t in (x - l)..x, |Real.exp (-(prim a x - prim a t)) * f t|)
      ≤ ∫ t in (x - l)..x, |f t| := by
    refine intervalIntegral.integral_mono_on hle (hcont1.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _) (fun t ht => ?_)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(prim a x - prim a t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have := prim_sub_nonneg ha ha0 ht.2
        linarith)
    nlinarith [abs_nonneg (f t)]
  rw [periodicGreen, abs_mul, abs_of_pos hcpos]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) hcpos.le

end PeriodicGreen
