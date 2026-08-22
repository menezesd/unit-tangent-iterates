import Mathlib
import UnitTangentIterates.SelectedRear

/-!
# Differentiability of a periodic solution in a parameter

This file proves the analytic core of the paper's lemma *Smooth dependence of
the selected rear*: for a *dissipative* scalar ODE

```
  ∂_x y(a, x) = f(a, x, y(a, x)) ,
```

whose solutions `y(a, ·)` are `P`-periodic, the periodic solution depends
differentiably on the parameter `a`, and its derivative is the periodic
solution `w` of the linearized equation

```
  w' = f_y(a₀, x, y(a₀,x)) w + f_a(a₀, x, y(a₀,x)) .
```

Dissipativity — the state derivative of `f` is at most `-c < 0` along the
solutions — replaces the implicit function theorem of the paper's proof: the
maximum principle for periodic solutions (`SelectedRear.periodic_linear_le`,
the "positive Green kernel with uniform bounds" of the paper) bounds a periodic
solution of `u' + a u = g` with `a ≥ c` by `‖g‖_∞ / c`.  Applying it twice —
once to the increment `Δ = y(a,·) - y(a₀,·)`, which is `O(|a-a₀|)`, and once to
the error `e = Δ - (a-a₀) w`, whose source term is the quadratic Taylor
remainder, hence `O((a-a₀)²)` — gives the differentiability, with the explicit
quadratic error bound.

Main results:

* `abs_param_diff_le_periodic` — `‖y(a,·) - y(a₀,·)‖_∞ ≤ (A/c)|a - a₀|`;
* `abs_error_le_periodic` — `‖y(a,·) - y(a₀,·) - (a-a₀)w‖_∞ ≤ K (a-a₀)²`;
* `hasDerivAt_param_periodic` — hence `a ↦ y(a,x)` is differentiable at `a₀`
  with derivative `w x`, for every `x`.

All the hypotheses are required only along the solutions, so the results apply
to an equation which is dissipative only on the strip the solutions live in —
as is the case for the steering equation of the paper.
-/

noncomputable section

open Set Real Asymptotics Filter Topology

namespace PeriodicParameterDeriv

variable {f fa fy : ℝ → ℝ → ℝ → ℝ} {y : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {a0 P c C A : ℝ}

/-- **The periodic solution moves at most linearly in the parameter.**  If the
equation is dissipative with rate `c > 0` along the solutions and the vector
field moves by at most `A|a - a₀|`, then `‖y(a,·) - y(a₀,·)‖_∞ ≤ (A/c)|a-a₀|`. -/
theorem abs_param_diff_le_periodic (hP : 0 < P) (hc : 0 < c)
    (hsol : ∀ a x, HasDerivAt (y a) (f a x (y a x)) x)
    (hper : ∀ a, Function.Periodic (y a) P)
    (hdiss : ∀ a x, (f a x (y a x) - f a x (y a0 x)) * (y a x - y a0 x)
      ≤ -c * (y a x - y a0 x) ^ 2)
    (hpar : ∀ a x, |f a x (y a0 x) - f a0 x (y a0 x)| ≤ A * |a - a0|)
    (a x : ℝ) :
    |y a x - y a0 x| ≤ A * |a - a0| / c := by
  set Δ : ℝ → ℝ := fun s => y a s - y a0 s with hΔ
  -- the effective zeroth-order coefficient
  set g : ℝ → ℝ := fun s =>
    if Δ s = 0 then c else -(f a s (y a s) - f a s (y a0 s)) / Δ s with hg
  have hgc : ∀ s, c ≤ g s := by
    intro s
    by_cases h : Δ s = 0
    · simp [hg, h]
    · have hsq : 0 < Δ s ^ 2 := by positivity
      have hd' : (f a s (y a s) - f a s (y a0 s)) * Δ s ≤ -c * Δ s ^ 2 := hdiss a s
      have hnum : 0 ≤ -((f a s (y a s) - f a s (y a0 s)) * Δ s) - c * Δ s ^ 2 := by linarith
      have key : -(f a s (y a s) - f a s (y a0 s)) / Δ s
          = c + (-((f a s (y a s) - f a s (y a0 s)) * Δ s) - c * Δ s ^ 2) / Δ s ^ 2 := by
        field_simp
        ring
      simp only [hg, if_neg h]
      rw [key]
      have hnn := div_nonneg hnum hsq.le
      linarith
  -- the source term
  set r : ℝ → ℝ := fun s => f a s (y a0 s) - f a0 s (y a0 s) with hr
  have hderiv : ∀ s, HasDerivAt Δ (r s - g s * Δ s) s := by
    intro s
    have h := (hsol a s).sub (hsol a0 s)
    refine h.congr_deriv ?_
    by_cases hz : Δ s = 0
    · have hy : y a s = y a0 s := by
        have : y a s - y a0 s = 0 := hz
        linarith
      simp [hr, hg, hz, hy]
    · simp only [hr, hg, if_neg hz]
      field_simp
      ring
  have hΔper : Function.Periodic Δ P := by
    intro s
    simp only [hΔ, hper a s, hper a0 s]
  exact SelectedRear.periodic_linear_sup_bound hP hderiv hΔper hc hgc
    (fun s => hpar a s) x

/-- **The quadratic error bound.**  With the Taylor hypothesis, the error
`e = Δ - (a-a₀)w` between the increment and the linearized prediction is
`O((a-a₀)²)`, with the explicit constant `C (1 + (A/c)²)/c`. -/
theorem abs_error_le_periodic (hP : 0 < P) (hc : 0 < c) (hC : 0 ≤ C)
    (hsol : ∀ a x, HasDerivAt (y a) (f a x (y a x)) x)
    (hper : ∀ a, Function.Periodic (y a) P)
    (hdiss : ∀ a x, (f a x (y a x) - f a x (y a0 x)) * (y a x - y a0 x)
      ≤ -c * (y a x - y a0 x) ^ 2)
    (hpar : ∀ a x, |f a x (y a0 x) - f a0 x (y a0 x)| ≤ A * |a - a0|)
    (hfy : ∀ x, c ≤ -fy a0 x (y a0 x))
    (htaylor : ∀ a x, |f a x (y a x) - f a0 x (y a0 x) - fa a0 x (y a0 x) * (a - a0)
      - fy a0 x (y a0 x) * (y a x - y a0 x)| ≤ C * ((a - a0) ^ 2 + (y a x - y a0 x) ^ 2))
    (hw : ∀ x, HasDerivAt w (fy a0 x (y a0 x) * w x + fa a0 x (y a0 x)) x)
    (hwper : Function.Periodic w P)
    (a x : ℝ) :
    |y a x - y a0 x - (a - a0) * w x| ≤ C * (1 + (A / c) ^ 2) / c * (a - a0) ^ 2 := by
  set h : ℝ := a - a0 with hh
  set e : ℝ → ℝ := fun s => y a s - y a0 s - h * w s with he
  -- the source term of the error equation is the Taylor remainder
  set R : ℝ → ℝ := fun s => f a s (y a s) - f a0 s (y a0 s) - fa a0 s (y a0 s) * h
    - fy a0 s (y a0 s) * (y a s - y a0 s) with hR
  have hderiv : ∀ s, HasDerivAt e (R s - (-fy a0 s (y a0 s)) * e s) s := by
    intro s
    have h1 := ((hsol a s).sub (hsol a0 s)).sub ((hw s).const_mul h)
    refine h1.congr_deriv ?_
    simp only [hR, he]
    ring
  have heper : Function.Periodic e P := by
    intro s
    simp only [he, hper a s, hper a0 s, hwper s]
  -- the remainder is quadratic in the parameter increment
  have hΔ : ∀ s, |y a s - y a0 s| ≤ A * |a - a0| / c :=
    fun s => abs_param_diff_le_periodic hP hc hsol hper hdiss hpar a s
  have hRbd : ∀ s, |R s| ≤ C * (1 + (A / c) ^ 2) * h ^ 2 := by
    intro s
    refine (htaylor a s).trans ?_
    have h1 : (y a s - y a0 s) ^ 2 ≤ (A / c) ^ 2 * h ^ 2 := by
      have h2 : |y a s - y a0 s| ≤ (A / c) * |h| := by
        have := hΔ s
        rw [hh]
        calc |y a s - y a0 s| ≤ A * |a - a0| / c := this
          _ = (A / c) * |a - a0| := by ring
      have h3 : |y a s - y a0 s| ^ 2 ≤ ((A / c) * |h|) ^ 2 := by
        have h4 : 0 ≤ |y a s - y a0 s| := abs_nonneg _
        nlinarith [h2, abs_nonneg h]
      calc (y a s - y a0 s) ^ 2 = |y a s - y a0 s| ^ 2 := (sq_abs _).symm
        _ ≤ ((A / c) * |h|) ^ 2 := h3
        _ = (A / c) ^ 2 * h ^ 2 := by rw [mul_pow, sq_abs]
    have hCnn : (0:ℝ) ≤ C := hC
    nlinarith [sq_nonneg h, sq_nonneg (A / c)]
  have hbound := SelectedRear.periodic_linear_sup_bound hP hderiv heper hc hfy hRbd x
  calc |y a x - y a0 x - (a - a0) * w x| = |e x| := by simp [he, hh]
    _ ≤ C * (1 + (A / c) ^ 2) * h ^ 2 / c := hbound
    _ = C * (1 + (A / c) ^ 2) / c * (a - a0) ^ 2 := by rw [hh]; ring

/-- **Differentiability of the periodic solution in the parameter.**  Under the
hypotheses of `abs_error_le_periodic`, the map `a ↦ y(a,x)` is differentiable
at `a₀` for every `x`, with derivative the periodic solution `w x` of the
linearized equation.  This is the paper's lemma *Smooth dependence of the
selected rear*, at the level of the steering angle. -/
theorem hasDerivAt_param_periodic (hP : 0 < P) (hc : 0 < c) (hC : 0 ≤ C)
    (hsol : ∀ a x, HasDerivAt (y a) (f a x (y a x)) x)
    (hper : ∀ a, Function.Periodic (y a) P)
    (hdiss : ∀ a x, (f a x (y a x) - f a x (y a0 x)) * (y a x - y a0 x)
      ≤ -c * (y a x - y a0 x) ^ 2)
    (hpar : ∀ a x, |f a x (y a0 x) - f a0 x (y a0 x)| ≤ A * |a - a0|)
    (hfy : ∀ x, c ≤ -fy a0 x (y a0 x))
    (htaylor : ∀ a x, |f a x (y a x) - f a0 x (y a0 x) - fa a0 x (y a0 x) * (a - a0)
      - fy a0 x (y a0 x) * (y a x - y a0 x)| ≤ C * ((a - a0) ^ 2 + (y a x - y a0 x) ^ 2))
    (hw : ∀ x, HasDerivAt w (fy a0 x (y a0 x) * w x + fa a0 x (y a0 x)) x)
    (hwper : Function.Periodic w P)
    (x : ℝ) :
    HasDerivAt (fun a => y a x) (w x) a0 := by
  set K : ℝ := C * (1 + (A / c) ^ 2) / c with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    have : 0 ≤ C * (1 + (A / c) ^ 2) := by positivity
    positivity
  have hquad : ∀ a, |y a x - y a0 x - (a - a0) * w x| ≤ K * (a - a0) ^ 2 :=
    fun a => abs_error_le_periodic hP hc hC hsol hper hdiss hpar hfy htaylor hw hwper a x
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro eps heps
  have hsmall : ∀ᶠ a in 𝓝 a0, |a - a0| ≤ eps / (K + 1) := by
    have hpos : 0 < eps / (K + 1) := by positivity
    have hball := Metric.ball_mem_nhds a0 hpos
    filter_upwards [hball] with a ha
    have : dist a a0 < eps / (K + 1) := ha
    rw [Real.dist_eq] at this
    exact this.le
  filter_upwards [hsmall] with a ha
  have habs : ‖(fun a => y a x) a - (fun a => y a x) a0 - (a - a0) • w x‖
      = |y a x - y a0 x - (a - a0) * w x| := by simp [smul_eq_mul]
  rw [habs]
  have hq : (a - a0) ^ 2 = |a - a0| * |a - a0| := by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg (a - a0))]
    ring
  have hfac : K * |a - a0| ≤ eps := by
    have h1 : K * |a - a0| ≤ K * (eps / (K + 1)) := mul_le_mul_of_nonneg_left ha hKnn
    have h2 : K * (eps / (K + 1)) = (K / (K + 1)) * eps := by
      field_simp
    have h3 : K / (K + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    calc K * |a - a0| ≤ K * (eps / (K + 1)) := h1
      _ = (K / (K + 1)) * eps := h2
      _ ≤ 1 * eps := mul_le_mul_of_nonneg_right h3 heps.le
      _ = eps := one_mul _
  calc |y a x - y a0 x - (a - a0) * w x| ≤ K * (a - a0) ^ 2 := hquad a
    _ = (K * |a - a0|) * |a - a0| := by rw [hq]; ring
    _ ≤ eps * |a - a0| := mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
    _ = eps * ‖a - a0‖ := by rw [Real.norm_eq_abs]

/-- A worked instance confirming that the hypotheses of
`hasDerivAt_param_periodic` are not contradictory: for the dissipative equation
`y' = a - y` the periodic solution is the constant `y(a, ·) = a`, the linearized
periodic solution is `w = 1`, and the conclusion is the (correct) derivative of
`a ↦ a`. -/
example (a0 x : ℝ) : HasDerivAt (fun a : ℝ => a) 1 a0 :=
  hasDerivAt_param_periodic
    (f := fun a _ u => a - u) (fa := fun _ _ _ => 1) (fy := fun _ _ _ => -1)
    (y := fun a _ => a) (w := fun _ => 1) (a0 := a0) (P := 1) (c := 1) (C := 0) (A := 1)
    one_pos one_pos le_rfl
    (fun a s => by simpa using hasDerivAt_const s a)
    (fun _ _ => rfl)
    (fun a _ => by ring_nf; nlinarith [sq_nonneg (a - a0)])
    (fun _ _ => by simp)
    (fun _ => by norm_num)
    (fun _ _ => by simp)
    (fun s => by simpa using hasDerivAt_const s (1:ℝ))
    (fun _ => rfl) x

end PeriodicParameterDeriv
