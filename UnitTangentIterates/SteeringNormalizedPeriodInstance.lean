import Mathlib
import UnitTangentIterates.SteeringNormalizedPeriod
import UnitTangentIterates.SecondOrderBounds

/-!
# A worked instance of the normalized-period steering theory

`SteeringNormalizedPeriod.lean` proves the joint regularity of the selected
steering angle for a path of fronts whose arclength period moves, working in the
normalized parameter `σ = s / P(a)`, in which every datum is `1`-periodic.  The
point of that parametrization is that it removes the restriction identified in
`SteeringPeriodRigidity.lean`: read in the arclength of each slice, a moving
period together with a periodic parameter derivative of the curvature forces
`P'(a) ∂_sK = 0`, so only circles are allowed.

This file checks that the hypotheses of the normalized theory are consistent and
that they really do allow the excluded configuration: a **moving** period
together with a curvature that is **not** constant along the front.  The data is

```
  P(a) = 2 + sin a ,        δ(a, σ) = π/12 + ε sin a + (α / 2π) sin (2π σ) ,
  K(a, σ) = α cos (2π σ) / P(a) + sin δ(a, σ) ,
```

with `α = 1/10` and `ε = 1/100`.  The steering equation
`∂_σ δ = P(a)(K − sin δ)` holds by construction, `δ` stays in the selected strip
of `κ̂ = 1/2`, and all the Lipschitz and quadratic Taylor bounds hold with
explicit constants.

Main result: `steering_normalized_period_instance`.
-/

noncomputable section

open Function Set Real

namespace SteeringNormalizedPeriodInstance

/-- The amplitude of the curvature wave along the front. -/
def amp : ℝ := 1 / 10

/-- The amplitude of the motion of the mean steering angle. -/
def eps : ℝ := 1 / 100

/-! ### The period -/

/-- The arclength period of the instance, `P(a) = 2 + sin a`. -/
def Pf (a : ℝ) : ℝ := 2 + Real.sin a

/-- Its derivative. -/
def Pd (a : ℝ) : ℝ := Real.cos a

/-- Its second derivative. -/
def Pdd (a : ℝ) : ℝ := -Real.sin a

theorem Pf_ge (a : ℝ) : (1 : ℝ) ≤ Pf a := by
  have := Real.neg_one_le_sin a; simp only [Pf]; linarith

theorem Pf_le (a : ℝ) : Pf a ≤ 3 := by
  have := Real.sin_le_one a; simp only [Pf]; linarith

theorem Pf_pos (a : ℝ) : 0 < Pf a := lt_of_lt_of_le one_pos (Pf_ge a)

theorem Pf_ne (a : ℝ) : Pf a ≠ 0 := (Pf_pos a).ne'

theorem hasDerivAt_Pf (a : ℝ) : HasDerivAt Pf (Pd a) a :=
  (Real.hasDerivAt_sin a).const_add 2

theorem hasDerivAt_Pd (a : ℝ) : HasDerivAt Pd (Pdd a) a := Real.hasDerivAt_cos a

theorem abs_Pd_le (a : ℝ) : |Pd a| ≤ 1 := Real.abs_cos_le_one a

theorem abs_Pdd_le (a : ℝ) : |Pdd a| ≤ 1 := by
  simpa [Pdd, abs_neg] using Real.abs_sin_le_one a

theorem abs_Pf_sub_le (a b : ℝ) : |Pf a - Pf b| ≤ 1 * |a - b| :=
  SecondOrderBounds.abs_sub_le_of_deriv_bound hasDerivAt_Pf abs_Pd_le a b

theorem abs_Pf_taylor (a b : ℝ) : |Pf a - Pf b - (a - b) * Pd b| ≤ 1 * (a - b) ^ 2 :=
  SecondOrderBounds.abs_taylor_quadratic hasDerivAt_Pf hasDerivAt_Pd abs_Pdd_le a b

/-! ### The reciprocal of the period -/

/-- The reciprocal of the period. -/
def gg (a : ℝ) : ℝ := (2 + Real.sin a)⁻¹

/-- Its derivative. -/
def gd (a : ℝ) : ℝ := -Real.cos a / (2 + Real.sin a) ^ 2

/-- Its second derivative. -/
def gdd (a : ℝ) : ℝ :=
  (Real.sin a * (2 + Real.sin a) + 2 * Real.cos a ^ 2) / (2 + Real.sin a) ^ 3

theorem Pf_mul_gg (a : ℝ) : Pf a * gg a = 1 := mul_inv_cancel₀ (Pf_ne a)

theorem gg_pos (a : ℝ) : 0 < gg a := inv_pos.2 (Pf_pos a)

theorem abs_gg_le (a : ℝ) : |gg a| ≤ 1 := by
  rw [abs_of_pos (gg_pos a), gg]
  have h : (1 : ℝ) ≤ 2 + Real.sin a := Pf_ge a
  simpa using inv_le_one_of_one_le₀ h

theorem hasDerivAt_gg (a : ℝ) : HasDerivAt gg (gd a) a := by
  have h : HasDerivAt (fun x : ℝ => 2 + Real.sin x) (Real.cos a) a :=
    (Real.hasDerivAt_sin a).const_add 2
  simpa [gg, gd] using h.inv (Pf_ne a)

theorem hasDerivAt_gd (a : ℝ) : HasDerivAt gd (gdd a) a := by
  have hu : HasDerivAt (fun x : ℝ => -Real.cos x) (Real.sin a) a := by
    simpa using (Real.hasDerivAt_cos a).neg
  have hv : HasDerivAt (fun x : ℝ => (2 + Real.sin x) ^ 2)
      (2 * (2 + Real.sin a) * Real.cos a) a := by
    have h : HasDerivAt (fun x : ℝ => 2 + Real.sin x) (Real.cos a) a :=
      (Real.hasDerivAt_sin a).const_add 2
    simpa [mul_comm, mul_assoc, mul_left_comm] using h.pow 2
  have hne : ((2 : ℝ) + Real.sin a) ^ 2 ≠ 0 := pow_ne_zero _ (Pf_ne a)
  have h := hu.div hv hne
  have hgd : gd = fun x : ℝ => -Real.cos x / (2 + Real.sin x) ^ 2 := rfl
  rw [hgd]
  convert h using 1
  rw [gdd]
  have hne' : ((2 : ℝ) + Real.sin a) ≠ 0 := Pf_ne a
  field_simp
  ring

theorem abs_gd_le (a : ℝ) : |gd a| ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (2 + Real.sin a) ^ 2 := by nlinarith [Real.neg_one_le_sin a]
  have h2 : (0 : ℝ) < (2 + Real.sin a) ^ 2 := lt_of_lt_of_le one_pos h1
  rw [gd, abs_div, abs_of_pos h2, div_le_iff₀ h2]
  have := Real.abs_cos_le_one a
  rw [abs_neg]
  nlinarith

theorem abs_gdd_le (a : ℝ) : |gdd a| ≤ 5 := by
  have hs := Real.neg_one_le_sin a
  have hs' := Real.sin_le_one a
  have hc : Real.cos a ^ 2 ≤ 1 := by
    have := Real.abs_cos_le_one a
    nlinarith [abs_nonneg (Real.cos a), sq_abs (Real.cos a)]
  have h1 : (1 : ℝ) ≤ (2 + Real.sin a) ^ 3 := one_le_pow₀ (by linarith)
  have h2 : (0 : ℝ) < (2 + Real.sin a) ^ 3 := lt_of_lt_of_le one_pos h1
  rw [gdd, abs_div, abs_of_pos h2, div_le_iff₀ h2]
  have hnum : |Real.sin a * (2 + Real.sin a) + 2 * Real.cos a ^ 2| ≤ 5 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Real.cos a)]
  nlinarith

theorem abs_gg_sub_le (a b : ℝ) : |gg a - gg b| ≤ 1 * |a - b| :=
  SecondOrderBounds.abs_sub_le_of_deriv_bound hasDerivAt_gg abs_gd_le a b

theorem abs_gg_taylor (a b : ℝ) : |gg a - gg b - (a - b) * gd b| ≤ 5 * (a - b) ^ 2 :=
  SecondOrderBounds.abs_taylor_quadratic hasDerivAt_gg hasDerivAt_gd abs_gdd_le a b

/-! ### The steering angle -/

/-- The mean steering angle of the slice at parameter `a`. -/
def Amean (a : ℝ) : ℝ := π / 12 + eps * Real.sin a

/-- Its derivative. -/
def Ad (a : ℝ) : ℝ := eps * Real.cos a

/-- Its second derivative. -/
def Add (a : ℝ) : ℝ := -(eps * Real.sin a)

/-- The wave of the steering angle along the front. -/
def wave (σ : ℝ) : ℝ := amp / (2 * π) * Real.sin (2 * π * σ)

/-- The steering angle of the instance. -/
def delta (a σ : ℝ) : ℝ := Amean a + wave σ

theorem amp_pos : (0 : ℝ) < amp := by norm_num [amp]

theorem eps_pos : (0 : ℝ) < eps := by norm_num [eps]

/-- A product of two bounded factors is bounded by the product of the bounds. -/
theorem abs_mul_bound {x y c d : ℝ} (hx : |x| ≤ c) (hy : |y| ≤ d) : |x * y| ≤ c * d := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)

theorem hasDerivAt_Amean (a : ℝ) : HasDerivAt Amean (Ad a) a :=
  ((Real.hasDerivAt_sin a).const_mul eps).const_add (π / 12)

theorem hasDerivAt_Ad (a : ℝ) : HasDerivAt Ad (Add a) a := by
  have h : HasDerivAt (fun x : ℝ => eps * Real.cos x) (eps * -Real.sin a) a :=
    (Real.hasDerivAt_cos a).const_mul eps
  have hAdd : Add a = eps * -Real.sin a := by rw [Add]; ring
  rw [hAdd]
  exact h

theorem abs_Ad_le (a : ℝ) : |Ad a| ≤ eps := by
  have h : |eps * Real.cos a| ≤ eps * 1 :=
    abs_mul_bound (le_of_eq (abs_of_nonneg (le_of_lt eps_pos))) (Real.abs_cos_le_one a)
  rw [Ad]; simpa using h

theorem abs_Add_le (a : ℝ) : |Add a| ≤ eps := by
  have h : |eps * Real.sin a| ≤ eps * 1 :=
    abs_mul_bound (le_of_eq (abs_of_nonneg (le_of_lt eps_pos))) (Real.abs_sin_le_one a)
  rw [Add, abs_neg]; simpa using h

theorem hasDerivAt_wave (σ : ℝ) : HasDerivAt wave (amp * Real.cos (2 * π * σ)) σ := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * π * x) (2 * π) σ := by
    simpa using (hasDerivAt_id σ).const_mul (2 * π)
  have h3 := h1.sin.const_mul (amp / (2 * π))
  have hw : wave = fun y : ℝ => amp / (2 * π) * Real.sin (2 * π * y) := rfl
  rw [hw]
  convert h3 using 1
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

theorem abs_wave_le (σ : ℝ) : |wave σ| ≤ 1 / 60 := by
  have hpi := Real.pi_gt_three
  have hpos : (0 : ℝ) < 2 * π := by linarith
  have h1 : amp / (2 * π) ≤ 1 / 60 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    simp only [amp]; nlinarith
  have h2 : (0 : ℝ) ≤ amp / (2 * π) := by
    have : (0:ℝ) ≤ amp := by norm_num [amp]
    positivity
  have h3 := Real.abs_sin_le_one (2 * π * σ)
  rw [wave, abs_mul, abs_of_nonneg h2]
  nlinarith [abs_nonneg (Real.sin (2 * π * σ))]

theorem hasDerivAt_delta_arc (a σ : ℝ) :
    HasDerivAt (delta a) (amp * Real.cos (2 * π * σ)) σ :=
  (hasDerivAt_wave σ).const_add (Amean a)

theorem periodic_wave : Function.Periodic wave 1 := by
  intro σ
  have h : 2 * π * (σ + 1) = 2 * π * σ + 2 * π := by ring
  simp only [wave, h, Real.sin_add_two_pi]

theorem periodic_delta (a : ℝ) : Function.Periodic (delta a) 1 := by
  intro σ; simp only [delta, periodic_wave σ]

theorem delta_bounds (a σ : ℝ) :
    π / 12 - eps - 1 / 60 ≤ delta a σ ∧ delta a σ ≤ π / 12 + eps + 1 / 60 := by
  have h1 : |eps * Real.sin a| ≤ eps := by
    have h : |eps * Real.sin a| ≤ eps * 1 :=
      abs_mul_bound (le_of_eq (abs_of_nonneg (le_of_lt eps_pos))) (Real.abs_sin_le_one a)
    simpa using h
  have h2 := abs_wave_le σ
  rw [abs_le] at h1 h2
  simp only [delta, Amean]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem arcsin_half : Real.arcsin (1 / 2) = π / 6 := by
  rw [show (1:ℝ)/2 = Real.sin (π/6) by rw [Real.sin_pi_div_six], Real.arcsin_sin] <;>
    nlinarith [Real.pi_pos]

theorem delta_mem_strip (a σ : ℝ) : delta a σ ∈ Icc (0 : ℝ) (Real.arcsin (1 / 2)) := by
  have hpi := Real.pi_gt_three
  obtain ⟨hl, hu⟩ := delta_bounds a σ
  rw [arcsin_half]
  constructor
  · simp only [eps] at hl; linarith
  · simp only [eps] at hu; linarith

theorem delta_nonneg (a σ : ℝ) : 0 ≤ delta a σ := (delta_mem_strip a σ).1

theorem delta_le_pi (a σ : ℝ) : delta a σ ≤ π := by
  have hpi := Real.pi_gt_three
  have := (delta_bounds a σ).2
  simp only [eps] at this; linarith

/-! ### The curvature -/

/-- The curvature of the front, in the normalized parameter. -/
def K (a σ : ℝ) : ℝ := amp * Real.cos (2 * π * σ) * gg a + Real.sin (delta a σ)

/-- Its derivative in the path parameter. -/
def Kd (a σ : ℝ) : ℝ := amp * Real.cos (2 * π * σ) * gd a + Real.cos (delta a σ) * Ad a

theorem steering_equation (a σ : ℝ) :
    HasDerivAt (delta a) (Pf a * (K a σ - Real.sin (delta a σ))) σ := by
  have h : Pf a * (K a σ - Real.sin (delta a σ)) = amp * Real.cos (2 * π * σ) := by
    simp only [K]
    have : Pf a * (amp * Real.cos (2 * π * σ) * gg a)
        = amp * Real.cos (2 * π * σ) * (Pf a * gg a) := by ring
    rw [add_sub_cancel_right, this, Pf_mul_gg, mul_one]
  rw [h]
  exact hasDerivAt_delta_arc a σ

theorem periodic_K (a : ℝ) : Function.Periodic (K a) 1 := by
  intro σ
  have h : 2 * π * (σ + 1) = 2 * π * σ + 2 * π := by ring
  simp only [K, h, Real.cos_add_two_pi, periodic_delta a σ]

theorem periodic_Kd (a : ℝ) : Function.Periodic (Kd a) 1 := by
  intro σ
  have h : 2 * π * (σ + 1) = 2 * π * σ + 2 * π := by ring
  simp only [Kd, h, Real.cos_add_two_pi, periodic_delta a σ]

/-- The wave factor of the curvature is bounded by the amplitude. -/
theorem abs_amp_cos_le (σ : ℝ) : |amp * Real.cos (2 * π * σ)| ≤ amp := by
  have h : |amp * Real.cos (2 * π * σ)| ≤ amp * 1 :=
    abs_mul_bound (le_of_eq (abs_of_nonneg (le_of_lt amp_pos))) (Real.abs_cos_le_one _)
  simpa using h

theorem abs_amp_cos_mul_le {x c : ℝ} (σ : ℝ) (hx : |x| ≤ c) :
    |amp * Real.cos (2 * π * σ) * x| ≤ amp * c :=
  abs_mul_bound (abs_amp_cos_le σ) hx

theorem abs_cos_delta_mul_Ad_le (a σ : ℝ) : |Real.cos (delta a σ) * Ad a| ≤ eps := by
  have h : |Real.cos (delta a σ) * Ad a| ≤ 1 * eps :=
    abs_mul_bound (Real.abs_cos_le_one _) (abs_Ad_le a)
  simpa using h

theorem abs_K_le (a σ : ℝ) : |K a σ| ≤ 1 / 2 := by
  have hpi := Real.pi_le_four
  have hpi3 := Real.pi_gt_three
  have h1 : |amp * Real.cos (2 * π * σ) * gg a| ≤ amp := by
    simpa using abs_amp_cos_mul_le σ (abs_gg_le a)
  have h2 : 0 ≤ Real.sin (delta a σ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (delta_nonneg a σ) (delta_le_pi a σ)
  have h3 : Real.sin (delta a σ) ≤ delta a σ := Real.sin_le (delta_nonneg a σ)
  have h4 := (delta_bounds a σ).2
  have hK : K a σ = amp * Real.cos (2 * π * σ) * gg a + Real.sin (delta a σ) := rfl
  rw [abs_le] at h1
  rw [abs_le, hK]
  simp only [amp, eps] at h1 h4 ⊢
  constructor <;> [linarith [h1.1]; linarith [h1.2]]

theorem abs_Kd_le (a σ : ℝ) : |Kd a σ| ≤ 11 / 100 := by
  have h1 : |amp * Real.cos (2 * π * σ) * gd a| ≤ amp := by
    simpa using abs_amp_cos_mul_le σ (abs_gd_le a)
  have h2 : |Real.cos (delta a σ) * Ad a| ≤ eps := abs_cos_delta_mul_Ad_le a σ
  calc |Kd a σ| ≤ |amp * Real.cos (2 * π * σ) * gd a| + |Real.cos (delta a σ) * Ad a| :=
        abs_add_le _ _
    _ ≤ amp + eps := add_le_add h1 h2
    _ = 11 / 100 := by norm_num [amp, eps]

/-! ### The Lipschitz and Taylor bounds in the path parameter -/

theorem hasDerivAt_sin_delta (σ a : ℝ) :
    HasDerivAt (fun b => Real.sin (delta b σ)) (Real.cos (delta a σ) * Ad a) a := by
  have h : HasDerivAt (fun b => Amean b + wave σ) (Ad a) a :=
    (hasDerivAt_Amean a).add_const (wave σ)
  simpa [delta] using h.sin

theorem hasDerivAt_cos_delta_mul (σ a : ℝ) :
    HasDerivAt (fun b => Real.cos (delta b σ) * Ad b)
      (-Real.sin (delta a σ) * Ad a * Ad a + Real.cos (delta a σ) * Add a) a := by
  have h : HasDerivAt (fun b => Amean b + wave σ) (Ad a) a :=
    (hasDerivAt_Amean a).add_const (wave σ)
  have hc : HasDerivAt (fun b => Real.cos (delta b σ)) (-Real.sin (delta a σ) * Ad a) a := by
    simpa [delta] using h.cos
  simpa using hc.mul (hasDerivAt_Ad a)

theorem abs_second_sin_delta (σ a : ℝ) :
    |-Real.sin (delta a σ) * Ad a * Ad a + Real.cos (delta a σ) * Add a| ≤ 1 / 50 := by
  have hfirst : |-Real.sin (delta a σ) * Ad a| ≤ eps := by
    have h : |-Real.sin (delta a σ) * Ad a| ≤ 1 * eps :=
      abs_mul_bound (by rw [abs_neg]; exact Real.abs_sin_le_one _) (abs_Ad_le a)
    simpa using h
  have h1 : |-Real.sin (delta a σ) * Ad a * Ad a| ≤ eps * eps :=
    abs_mul_bound hfirst (abs_Ad_le a)
  have h2 : |Real.cos (delta a σ) * Add a| ≤ eps := by
    have h : |Real.cos (delta a σ) * Add a| ≤ 1 * eps :=
      abs_mul_bound (Real.abs_cos_le_one _) (abs_Add_le a)
    simpa using h
  calc |-Real.sin (delta a σ) * Ad a * Ad a + Real.cos (delta a σ) * Add a|
      ≤ |-Real.sin (delta a σ) * Ad a * Ad a| + |Real.cos (delta a σ) * Add a| := abs_add_le _ _
    _ ≤ eps * eps + eps := add_le_add h1 h2
    _ ≤ 1 / 50 := by norm_num [eps]

theorem abs_sin_delta_sub (a b σ : ℝ) :
    |Real.sin (delta a σ) - Real.sin (delta b σ)| ≤ eps * |a - b| :=
  SecondOrderBounds.abs_sub_le_of_deriv_bound (g := fun c => Real.sin (delta c σ))
    (g' := fun c => Real.cos (delta c σ) * Ad c) (hasDerivAt_sin_delta σ)
    (fun c => abs_cos_delta_mul_Ad_le c σ) a b

theorem abs_sin_delta_taylor (a b σ : ℝ) :
    |Real.sin (delta a σ) - Real.sin (delta b σ) - (a - b) * (Real.cos (delta b σ) * Ad b)|
      ≤ 1 / 50 * (a - b) ^ 2 :=
  SecondOrderBounds.abs_taylor_quadratic (g := fun c => Real.sin (delta c σ))
    (g' := fun c => Real.cos (delta c σ) * Ad c)
    (g'' := fun c => -Real.sin (delta c σ) * Ad c * Ad c + Real.cos (delta c σ) * Add c)
    (hasDerivAt_sin_delta σ) (hasDerivAt_cos_delta_mul σ) (abs_second_sin_delta σ) a b

theorem abs_K_sub_le (a b σ : ℝ) : |K a σ - K b σ| ≤ 11 / 100 * |a - b| := by
  have hsplit : K a σ - K b σ
      = amp * Real.cos (2 * π * σ) * (gg a - gg b)
        + (Real.sin (delta a σ) - Real.sin (delta b σ)) := by
    simp only [K]; ring
  have hg : |gg a - gg b| ≤ |a - b| := by simpa using abs_gg_sub_le a b
  have h1 : |amp * Real.cos (2 * π * σ) * (gg a - gg b)| ≤ amp * |a - b| :=
    abs_amp_cos_mul_le σ hg
  have h2 := abs_sin_delta_sub a b σ
  calc |K a σ - K b σ|
      ≤ |amp * Real.cos (2 * π * σ) * (gg a - gg b)|
        + |Real.sin (delta a σ) - Real.sin (delta b σ)| := by rw [hsplit]; exact abs_add_le _ _
    _ ≤ amp * |a - b| + eps * |a - b| := add_le_add h1 h2
    _ = 11 / 100 * |a - b| := by rw [amp, eps]; ring

theorem abs_K_taylor (a b σ : ℝ) :
    |K a σ - K b σ - (a - b) * Kd b σ| ≤ 13 / 25 * (a - b) ^ 2 := by
  have hsplit : K a σ - K b σ - (a - b) * Kd b σ
      = amp * Real.cos (2 * π * σ) * (gg a - gg b - (a - b) * gd b)
        + (Real.sin (delta a σ) - Real.sin (delta b σ)
            - (a - b) * (Real.cos (delta b σ) * Ad b)) := by
    simp only [K, Kd]; ring
  have h1 : |amp * Real.cos (2 * π * σ) * (gg a - gg b - (a - b) * gd b)|
      ≤ amp * (5 * (a - b) ^ 2) :=
    abs_amp_cos_mul_le σ (abs_gg_taylor a b)
  have h2 := abs_sin_delta_taylor a b σ
  calc |K a σ - K b σ - (a - b) * Kd b σ|
      ≤ |amp * Real.cos (2 * π * σ) * (gg a - gg b - (a - b) * gd b)|
        + |Real.sin (delta a σ) - Real.sin (delta b σ)
            - (a - b) * (Real.cos (delta b σ) * Ad b)| := by
        rw [hsplit]; exact abs_add_le _ _
    _ ≤ amp * (5 * (a - b) ^ 2) + 1 / 50 * (a - b) ^ 2 := add_le_add h1 h2
    _ = 13 / 25 * (a - b) ^ 2 := by rw [amp]; ring

/-! ### Regularity of the data -/

theorem contDiff_Pf (n : ℕ) : ContDiff ℝ n Pf := contDiff_const.add Real.contDiff_sin

theorem contDiff_Pd (n : ℕ) : ContDiff ℝ n Pd := Real.contDiff_cos

theorem contDiff_gg (n : ℕ) : ContDiff ℝ n gg :=
  (contDiff_const.add Real.contDiff_sin).inv (fun a => Pf_ne a)

theorem contDiff_gd (n : ℕ) : ContDiff ℝ n gd :=
  (Real.contDiff_cos.neg).div ((contDiff_const.add Real.contDiff_sin).pow 2)
    (fun a => pow_ne_zero _ (Pf_ne a))

theorem contDiff_Amean (n : ℕ) : ContDiff ℝ n Amean :=
  contDiff_const.add (contDiff_const.mul Real.contDiff_sin)

theorem contDiff_Ad (n : ℕ) : ContDiff ℝ n Ad := contDiff_const.mul Real.contDiff_cos

theorem contDiff_wave (n : ℕ) : ContDiff ℝ n wave :=
  contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))

theorem contDiff_uncurry_delta (n : ℕ) : ContDiff ℝ n (uncurry delta) :=
  ((contDiff_Amean n).comp contDiff_fst).add ((contDiff_wave n).comp contDiff_snd)

theorem contDiff_cos_arc (n : ℕ) :
    ContDiff ℝ n (fun p : ℝ × ℝ => Real.cos (2 * π * p.2)) :=
  Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd)

theorem contDiff_uncurry_K (n : ℕ) : ContDiff ℝ n (uncurry K) :=
  ((contDiff_const.mul (contDiff_cos_arc n)).mul ((contDiff_gg n).comp contDiff_fst)).add
    (Real.contDiff_sin.comp (contDiff_uncurry_delta n))

theorem contDiff_uncurry_Kd (n : ℕ) : ContDiff ℝ n (uncurry Kd) :=
  ((contDiff_const.mul (contDiff_cos_arc n)).mul ((contDiff_gd n).comp contDiff_fst)).add
    ((Real.contDiff_cos.comp (contDiff_uncurry_delta n)).mul ((contDiff_Ad n).comp contDiff_fst))

/-! ### The instance -/

/-- **The hypotheses of the normalized-period steering theory are consistent, and
they allow a genuinely moving period together with a curvature that varies along
the front.**  For the data

```
  P(a) = 2 + sin a ,  δ(a, σ) = π/12 + sin a / 100 + sin (2π σ) / (20 π) ,
  K(a, σ) = cos (2π σ) / (10 P(a)) + sin δ(a, σ) ,
```

every hypothesis of `SteeringNormalizedPeriod.contDiff_four_uncurry_delta` and of
`SteeringNormalizedPeriod.hasDerivAt_param` holds, with `κ̂ = 1/2`, `P₀ = 1`,
`P₁ = 3`, `M_d = 11/100`, `M_P = 1`, `K_lip = 11/100`, `P_lip = 1`, `C_K = 13/25`
and `C_P = 1`.  Consequently the selected steering angle is jointly `C⁴` and its
derivative in the path parameter is the periodic solution of the linearized
equation.  The period really moves (`P'(0) = 1 ≠ 0`), the curvature really
varies along the front, and the steering angle really depends on the path
parameter — the configuration that `SteeringPeriodRigidity` excludes in the
arclength parametrization. -/
theorem steering_normalized_period_instance :
    ContDiff ℝ 4 (uncurry delta) ∧
      (∀ a σ, HasDerivAt (fun b => delta b σ)
        (SteeringNormalizedPeriod.variation K Kd delta Pf Pd a σ) a) ∧
      HasDerivAt Pf (Pd 0) 0 ∧ Pd 0 ≠ 0 ∧
      K 0 0 ≠ K 0 (1 / 2) ∧ delta 0 0 ≠ delta (π / 2) 0 := by
  have hP0 : (0 : ℝ) < 1 := one_pos
  have hkap0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hkap1 : (1 : ℝ) / 2 < 1 := by norm_num
  have hKC : ∀ n : ℕ, ContDiff ℝ n (uncurry K) := contDiff_uncurry_K
  have hKdC : ∀ n : ℕ, ContDiff ℝ n (uncurry Kd) := contDiff_uncurry_Kd
  refine ⟨?_, ?_, hasDerivAt_Pf 0, ?_, ?_, ?_⟩
  · exact SteeringNormalizedPeriod.contDiff_four_uncurry_delta (P0 := 1) (P1 := 3)
      (kap := 1/2) (Md := 11/100) (MP := 1) (Klip := 11/100) (Plip := 1)
      (CK := 13/25) (CP := 1) hP0 hkap0 hkap1 (fun a => Pf_ge a) (fun a => Pf_le a)
      steering_equation delta_mem_strip periodic_delta periodic_K periodic_Kd
      abs_K_le abs_Kd_le abs_Pd_le (fun a b σ => abs_K_sub_le a b σ) abs_Pf_sub_le
      (fun a b σ => abs_K_taylor a b σ) abs_Pf_taylor (by norm_num) (by norm_num)
      (contDiff_Pf 3) (contDiff_Pd 3) (hKC 3) (hKdC 3)
  · intro a σ
    exact SteeringNormalizedPeriod.hasDerivAt_param (P0 := 1) (P1 := 3)
      (kap := 1/2) (Md := 11/100) (MP := 1) (Klip := 11/100) (Plip := 1)
      (CK := 13/25) (CP := 1) hP0 hkap0 hkap1 (fun a => Pf_ge a) (fun a => Pf_le a)
      (hKC 0).continuous (hKdC 0).continuous
      steering_equation delta_mem_strip periodic_delta periodic_K periodic_Kd
      abs_K_le abs_Kd_le abs_Pd_le (fun a b σ => abs_K_sub_le a b σ) abs_Pf_sub_le
      (fun a b σ => abs_K_taylor a b σ) abs_Pf_taylor (by norm_num) (by norm_num) a σ
  · simp [Pd]
  · have h0 : K 0 0 = amp * (1 / 2) + Real.sin (delta 0 0) := by
      simp only [K, gg, Real.sin_zero, mul_zero, Real.cos_zero, mul_one]
      norm_num
    have h1 : K 0 (1 / 2) = -(amp * (1 / 2)) + Real.sin (delta 0 (1 / 2)) := by
      have harg : 2 * π * (1 / 2 : ℝ) = π := by ring
      simp only [K, gg, harg, Real.cos_pi, Real.sin_zero]
      norm_num
    have hd : delta 0 (1 / 2) = delta 0 0 := by
      have harg : 2 * π * (1 / 2 : ℝ) = π := by ring
      simp only [delta, wave, harg, Real.sin_pi, Real.sin_zero, mul_zero]
    rw [h0, h1, hd]
    have : (0:ℝ) < amp := by norm_num [amp]
    intro hcon
    nlinarith [hcon]
  · simp only [delta, Amean, Real.sin_zero, Real.sin_pi_div_two, mul_zero, mul_one]
    have : (0:ℝ) < eps := by norm_num [eps]
    intro hcon
    nlinarith [hcon]

end SteeringNormalizedPeriodInstance
