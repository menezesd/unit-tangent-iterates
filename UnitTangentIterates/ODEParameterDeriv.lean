import Mathlib

/-!
# Differentiability of the solution of a scalar ODE in a parameter

The paper *A Noncircular Oval with Convex Unit-Tangent Iterates* uses, in its
lemma *Smooth dependence of the selected rear*, that the selected steering
angle of a path of fronts depends differentiably on the path parameter, the
derivative solving the linearized (variational) equation.  This file proves the
underlying analytic fact for a scalar ODE:

```
  ∂_x y(a, x) = f(a, x, y(a, x)) ,      y(a, x₀) = c(a) ,
```

if `f` is Lipschitz in the state, Lipschitz in the parameter, and has a
first-order expansion in `(a, y)` with quadratic remainder, and if `z` solves
the variational equation

```
  z' = f_y(a₀, x, y(a₀,x)) z + f_a(a₀, x, y(a₀,x)) ,   z(x₀) = c'(a₀) ,
```

then `a ↦ y(a, x)` is differentiable at `a₀` with derivative `z(x)`, for every
`x` of the interval.

The proof is the classical two-step Grönwall argument: the parameter increment
`Δ_h = y(a₀+h, ·) - y(a₀, ·)` is `O(h)` uniformly on the interval, and then the
error `e_h = Δ_h - h z` satisfies `e_h' = f_y e_h + O(h²)` with `e_h(x₀) = o(h)`,
so `e_h = o(h)`.

Main results:

* `abs_le_gronwallBound` — Grönwall's inequality for a real function;
* `abs_param_diff_le` — the increment `Δ_h` is `O(h)` on the interval;
* `hasDerivAt_param` — the differentiability of the solution in the parameter.

Auxiliary: `gronwallBound_linear` (`gronwallBound` is linear in the pair
`(δ, ε)`) and `gronwallBound_mono_x` (it is monotone in the time).
-/

noncomputable section

open Set Real Asymptotics Filter Topology

namespace ODEParameterDeriv

/-! ### Elementary properties of the Grönwall bound -/

/-- `gronwallBound` is linear in the pair `(δ, ε)`. -/
theorem gronwallBound_linear (d K e s : ℝ) :
    gronwallBound d K e s = d * gronwallBound 1 K 0 s + e * gronwallBound 0 K 1 s := by
  unfold gronwallBound
  by_cases hK : K = 0
  · simp [hK]
  · simp only [if_neg hK]
    field_simp
    ring

/-- `gronwallBound` scales. -/
theorem gronwallBound_smul (t d K e s : ℝ) :
    gronwallBound (t * d) K (t * e) s = t * gronwallBound d K e s := by
  unfold gronwallBound
  by_cases hK : K = 0
  · simp [hK]; ring
  · simp only [if_neg hK]; field_simp

theorem gronwallBound_nonneg {d K e s : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e) (hK : 0 ≤ K)
    (hs : 0 ≤ s) : 0 ≤ gronwallBound d K e s := by
  unfold gronwallBound
  by_cases hK0 : K = 0
  · simp [hK0]; positivity
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    simp only [if_neg hK0]
    have h1 : (1:ℝ) ≤ Real.exp (K * s) := Real.one_le_exp (by positivity)
    have h2 : 0 ≤ e / K := div_nonneg he hKpos.le
    nlinarith [Real.exp_pos (K * s)]

/-- `gronwallBound` is monotone in the time variable. -/
theorem gronwallBound_mono_x {d K e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e) (hK : 0 ≤ K)
    {s t : ℝ} (hst : s ≤ t) :
    gronwallBound d K e s ≤ gronwallBound d K e t := by
  unfold gronwallBound
  by_cases hK0 : K = 0
  · simp only [if_pos hK0]
    nlinarith
  · simp only [if_neg hK0]
    have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    have h1 : Real.exp (K * s) ≤ Real.exp (K * t) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : 0 ≤ e / K := div_nonneg he hKpos.le
    nlinarith

/-! ### Grönwall's inequality for a real function -/

/-- **Grönwall's inequality.**  If `|u(x₀)| ≤ d` and `|u'| ≤ K|u| + e` on
`[x₀, x₁)`, then `|u|` is bounded by the Grönwall bound on `[x₀, x₁]`. -/
theorem abs_le_gronwallBound {u u' : ℝ → ℝ} {x0 x1 d K e : ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hd : |u x0| ≤ d)
    (hb : ∀ x ∈ Ico x0 x1, |u' x| ≤ K * |u x| + e) :
    ∀ x ∈ Icc x0 x1, |u x| ≤ gronwallBound d K e (x - x0) := by
  have hdiff : Differentiable ℝ u := fun x => (hu x).differentiableAt
  have hcont : ContinuousOn u (Icc x0 x1) := hdiff.continuous.continuousOn
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := u) (f' := u') (δ := d) (K := K)
    (ε := e) (a := x0) (b := x1) hcont (fun x _ => (hu x).hasDerivWithinAt)
    (by simpa using hd) (by intro x hx; simpa using hb x hx)
  simpa using h

/-! ### The increment of the solution in the parameter -/

/-- **The solution moves at most linearly in the parameter.**  If the vector
field is `L`-Lipschitz in the state and moves at most `A|h|` when the parameter
moves by `h`, the two solutions stay within the Grönwall bound. -/
theorem abs_param_diff_le {f : ℝ → ℝ → ℝ → ℝ} {y : ℝ → ℝ → ℝ} {a b x0 x1 L A d : ℝ}
    (hsol : ∀ a x, HasDerivAt (y a) (f a x (y a x)) x)
    (hlip : ∀ a x u v, |f a x u - f a x v| ≤ L * |u - v|)
    (hpar : ∀ x u, |f b x u - f a x u| ≤ A)
    (hinit : |y b x0 - y a x0| ≤ d) :
    ∀ x ∈ Icc x0 x1, |y b x - y a x| ≤ gronwallBound d L A (x - x0) := by
  refine abs_le_gronwallBound (u := fun x => y b x - y a x)
    (u' := fun x => f b x (y b x) - f a x (y a x)) (fun x => (hsol b x).sub (hsol a x)) hinit
    (fun x _ => ?_)
  have h1 : |f b x (y b x) - f b x (y a x)| ≤ L * |y b x - y a x| := hlip b x _ _
  have h2 : |f b x (y a x) - f a x (y a x)| ≤ A := hpar x (y a x)
  calc |f b x (y b x) - f a x (y a x)|
      ≤ |f b x (y b x) - f b x (y a x)| + |f b x (y a x) - f a x (y a x)| := by
        have := abs_add_le (f b x (y b x) - f b x (y a x)) (f b x (y a x) - f a x (y a x))
        simpa using this
    _ ≤ L * |y b x - y a x| + A := add_le_add h1 h2

/-! ### Differentiability in the parameter -/

/-- **Differentiability of the solution of a scalar ODE in a parameter.**
Let `y a` solve `y' = f(a, x, y)` with initial value `y(a, x₀) = c(a)` at `x₀`,
let `f` be `L`-Lipschitz in the state and `A`-Lipschitz in the parameter, and
suppose `f` has at `a₀` the first-order expansion

```
  f(a₀+h, x, y(a₀,x)+k) = f(a₀,x,y(a₀,x)) + f_a h + f_y k + O(h² + k²)
```

uniformly in `x`.  If `c` is differentiable at `a₀` and `z` solves the
variational equation with `z(x₀) = c'(a₀)`, then for every `x ∈ [x₀, x₁]` the
map `a ↦ y(a, x)` is differentiable at `a₀` with derivative `z(x)`. -/
theorem hasDerivAt_param {f fa fy : ℝ → ℝ → ℝ → ℝ} {y : ℝ → ℝ → ℝ} {z c : ℝ → ℝ}
    {a0 x0 x1 L C A : ℝ}
    (hx01 : x0 ≤ x1) (hL : 0 ≤ L) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hsol : ∀ a x, HasDerivAt (y a) (f a x (y a x)) x)
    (hinit : ∀ a, y a x0 = c a)
    (hcd : HasDerivAt c (z x0) a0)
    (hz : ∀ x, HasDerivAt z (fy a0 x (y a0 x) * z x + fa a0 x (y a0 x)) x)
    (hlip : ∀ a x u v, |f a x u - f a x v| ≤ L * |u - v|)
    (hfy : ∀ x, |fy a0 x (y a0 x)| ≤ L)
    (hpar : ∀ a x u, |f a x u - f a0 x u| ≤ A * |a - a0|)
    (htaylor : ∀ a k x, |f a x (y a0 x + k) - f a0 x (y a0 x)
        - fa a0 x (y a0 x) * (a - a0) - fy a0 x (y a0 x) * k| ≤ C * ((a - a0) ^ 2 + k ^ 2))
    (x : ℝ) (hx : x ∈ Icc x0 x1) :
    HasDerivAt (fun a => y a x) (z x) a0 := by
  set T : ℝ := x1 - x0 with hT
  have hTnn : 0 ≤ T := by simp [hT]; linarith
  set B : ℝ := |z x0| + 1 with hB
  have hBnn : 0 ≤ B := by positivity
  set M : ℝ := gronwallBound B L A T with hM
  have hMnn : 0 ≤ M := gronwallBound_nonneg hBnn hA hL hTnn
  set alpha : ℝ := gronwallBound 1 L 0 T with halpha
  set beta : ℝ := gronwallBound 0 L 1 T with hbeta
  have halphann : 0 ≤ alpha := gronwallBound_nonneg zero_le_one le_rfl hL hTnn
  have hbetann : 0 ≤ beta := gronwallBound_nonneg le_rfl zero_le_one hL hTnn
  -- the little-o of the initial condition
  have hcdo : (fun a => c a - c a0 - (a - a0) * z x0) =o[𝓝 a0] fun a => a - a0 := by
    have := (hasDerivAt_iff_isLittleO.mp hcd)
    simpa [smul_eq_mul, mul_comm] using this
  -- the initial condition is Lipschitz near `a₀`
  have hclip : ∀ᶠ a in 𝓝 a0, |c a - c a0| ≤ B * |a - a0| := by
    have h1 := (isLittleO_iff.mp hcdo) (c := (1:ℝ)) one_pos
    filter_upwards [h1] with a ha
    have h2 : |c a - c a0 - (a - a0) * z x0| ≤ |a - a0| := by simpa using ha
    have h3 : |c a - c a0| ≤ |c a - c a0 - (a - a0) * z x0| + |(a - a0) * z x0| := by
      have := abs_add_le (c a - c a0 - (a - a0) * z x0) ((a - a0) * z x0)
      simpa using this
    have h4 : |(a - a0) * z x0| = |a - a0| * |z x0| := abs_mul _ _
    rw [hB]
    nlinarith [abs_nonneg (a - a0), abs_nonneg (z x0)]
  -- the increment of the solution is `O(h)` on the interval
  have hDelta : ∀ᶠ a in 𝓝 a0, ∀ w ∈ Icc x0 x1, |y a w - y a0 w| ≤ M * |a - a0| := by
    filter_upwards [hclip] with a ha
    intro w hw
    have hinit' : |y a x0 - y a0 x0| ≤ |a - a0| * B := by
      rw [hinit a, hinit a0]
      rw [mul_comm]; exact ha
    have hpar' : ∀ s u, |f a s u - f a0 s u| ≤ |a - a0| * A := by
      intro s u
      have := hpar a s u
      linarith [this, mul_comm A |a - a0|]
    have hgron := abs_param_diff_le (f := f) (y := y) (a := a0) (b := a) (x0 := x0) (x1 := x1)
      (L := L) (A := |a - a0| * A) (d := |a - a0| * B) hsol hlip hpar' hinit' w hw
    have hmono : gronwallBound (|a - a0| * B) L (|a - a0| * A) (w - x0)
        ≤ gronwallBound (|a - a0| * B) L (|a - a0| * A) T := by
      refine gronwallBound_mono_x (by positivity) (by positivity) hL ?_
      rw [hT]; exact sub_le_sub_right hw.2 x0
    have hscale : gronwallBound (|a - a0| * B) L (|a - a0| * A) T = |a - a0| * M := by
      rw [hM, gronwallBound_smul]
    calc |y a w - y a0 w| ≤ gronwallBound (|a - a0| * B) L (|a - a0| * A) (w - x0) := hgron
      _ ≤ gronwallBound (|a - a0| * B) L (|a - a0| * A) T := hmono
      _ = |a - a0| * M := hscale
      _ = M * |a - a0| := by ring
  -- the error estimate
  have herr : ∀ᶠ a in 𝓝 a0, |y a x - y a0 x - (a - a0) * z x|
      ≤ alpha * |c a - c a0 - (a - a0) * z x0| + beta * (C * (1 + M ^ 2)) * (a - a0) ^ 2 := by
    filter_upwards [hDelta] with a ha
    set e : ℝ → ℝ := fun w => y a w - y a0 w - (a - a0) * z w with he
    have hderiv : ∀ w, HasDerivAt e (f a w (y a w) - f a0 w (y a0 w)
        - (a - a0) * (fy a0 w (y a0 w) * z w + fa a0 w (y a0 w))) w := by
      intro w
      exact ((hsol a w).sub (hsol a0 w)).sub ((hz w).const_mul (a - a0))
    have hbound : ∀ w ∈ Ico x0 x1, |f a w (y a w) - f a0 w (y a0 w)
        - (a - a0) * (fy a0 w (y a0 w) * z w + fa a0 w (y a0 w))|
        ≤ L * |e w| + C * (1 + M ^ 2) * (a - a0) ^ 2 := by
      intro w hw
      have hwIcc : w ∈ Icc x0 x1 := ⟨hw.1, le_of_lt hw.2⟩
      set k : ℝ := y a w - y a0 w with hk
      have hyk : y a w = y a0 w + k := by rw [hk]; ring
      have htay := htaylor a k w
      rw [← hyk] at htay
      -- the remainder
      set R : ℝ := f a w (y a w) - f a0 w (y a0 w) - fa a0 w (y a0 w) * (a - a0)
        - fy a0 w (y a0 w) * k with hR
      have hRbd : |R| ≤ C * ((a - a0) ^ 2 + k ^ 2) := htay
      have hkbd : |k| ≤ M * |a - a0| := ha w hwIcc
      have hksq : k ^ 2 ≤ M ^ 2 * (a - a0) ^ 2 := by
        have h1 : |k| ^ 2 ≤ (M * |a - a0|) ^ 2 := by
          have := abs_nonneg k
          nlinarith [hkbd, abs_nonneg k]
        calc k ^ 2 = |k| ^ 2 := (sq_abs k).symm
          _ ≤ (M * |a - a0|) ^ 2 := h1
          _ = M ^ 2 * (a - a0) ^ 2 := by rw [mul_pow, sq_abs]
      have hRbd' : |R| ≤ C * (1 + M ^ 2) * (a - a0) ^ 2 := by
        refine hRbd.trans ?_
        nlinarith [sq_nonneg (a - a0)]
      have hsplit : f a w (y a w) - f a0 w (y a0 w)
          - (a - a0) * (fy a0 w (y a0 w) * z w + fa a0 w (y a0 w))
          = fy a0 w (y a0 w) * e w + R := by
        rw [hR, he, hk]; ring
      rw [hsplit]
      have h1 : |fy a0 w (y a0 w) * e w| ≤ L * |e w| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hfy w) (abs_nonneg _)
      calc |fy a0 w (y a0 w) * e w + R| ≤ |fy a0 w (y a0 w) * e w| + |R| := abs_add_le _ _
        _ ≤ L * |e w| + C * (1 + M ^ 2) * (a - a0) ^ 2 := add_le_add h1 hRbd'
    have hstart : |e x0| ≤ |c a - c a0 - (a - a0) * z x0| := by
      rw [he]
      simp only [hinit a, hinit a0]
      exact le_rfl
    have hgron := abs_le_gronwallBound (u := e) hderiv hstart hbound x hx
    have hmono : gronwallBound (|c a - c a0 - (a - a0) * z x0|) L
          (C * (1 + M ^ 2) * (a - a0) ^ 2) (x - x0)
        ≤ gronwallBound (|c a - c a0 - (a - a0) * z x0|) L
          (C * (1 + M ^ 2) * (a - a0) ^ 2) T := by
      refine gronwallBound_mono_x (abs_nonneg _) (by positivity) hL ?_
      rw [hT]; exact sub_le_sub_right hx.2 x0
    have hlin := gronwallBound_linear (|c a - c a0 - (a - a0) * z x0|) L
      (C * (1 + M ^ 2) * (a - a0) ^ 2) T
    calc |e x| ≤ gronwallBound (|c a - c a0 - (a - a0) * z x0|) L
          (C * (1 + M ^ 2) * (a - a0) ^ 2) (x - x0) := hgron
      _ ≤ gronwallBound (|c a - c a0 - (a - a0) * z x0|) L
          (C * (1 + M ^ 2) * (a - a0) ^ 2) T := hmono
      _ = |c a - c a0 - (a - a0) * z x0| * alpha
          + C * (1 + M ^ 2) * (a - a0) ^ 2 * beta := by rw [hlin, halpha, hbeta]
      _ = alpha * |c a - c a0 - (a - a0) * z x0| + beta * (C * (1 + M ^ 2)) * (a - a0) ^ 2 := by
          ring
  -- conclude
  rw [hasDerivAt_iff_isLittleO]
  rw [isLittleO_iff]
  intro eps heps
  set D : ℝ := beta * (C * (1 + M ^ 2)) with hD
  have hDnn : 0 ≤ D := by rw [hD]; positivity
  -- the initial term
  have h1 : ∀ᶠ a in 𝓝 a0, |c a - c a0 - (a - a0) * z x0| ≤ (eps / (2 * (alpha + 1))) * |a - a0| := by
    have hpos : 0 < eps / (2 * (alpha + 1)) := by positivity
    have := (isLittleO_iff.mp hcdo) hpos
    filter_upwards [this] with a ha
    simpa using ha
  -- the quadratic term
  have h2 : ∀ᶠ a in 𝓝 a0, |a - a0| ≤ eps / (2 * (D + 1)) := by
    have hpos : 0 < eps / (2 * (D + 1)) := by positivity
    have : ∀ᶠ a in 𝓝 a0, |a - a0| < eps / (2 * (D + 1)) := by
      have := Metric.ball_mem_nhds a0 hpos
      filter_upwards [this] with a ha
      simpa [Real.dist_eq] using ha
    filter_upwards [this] with a ha using ha.le
  filter_upwards [herr, h1, h2] with a hea h1a h2a
  have habs : ‖(fun a => y a x) a - (fun a => y a x) a0 - (a - a0) • z x‖
      = |y a x - y a0 x - (a - a0) * z x| := by
    simp [smul_eq_mul]
  rw [habs]
  have hq : (a - a0) ^ 2 = |a - a0| * |a - a0| := by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg (a - a0))]
    ring
  have hstep1 : alpha * |c a - c a0 - (a - a0) * z x0|
      ≤ alpha * ((eps / (2 * (alpha + 1))) * |a - a0|) :=
    mul_le_mul_of_nonneg_left h1a halphann
  have hstep1' : alpha * ((eps / (2 * (alpha + 1))) * |a - a0|) ≤ (eps / 2) * |a - a0| := by
    have hfac : alpha * (eps / (2 * (alpha + 1))) ≤ eps / 2 := by
      have hrw : alpha * (eps / (2 * (alpha + 1))) = (alpha / (alpha + 1)) * (eps / 2) := by
        field_simp
      have hle : alpha / (alpha + 1) ≤ 1 :=
        (div_le_one (by linarith)).mpr (by linarith)
      rw [hrw]
      calc (alpha / (alpha + 1)) * (eps / 2) ≤ 1 * (eps / 2) :=
            mul_le_mul_of_nonneg_right hle (by linarith)
        _ = eps / 2 := one_mul _
    calc alpha * ((eps / (2 * (alpha + 1))) * |a - a0|)
        = (alpha * (eps / (2 * (alpha + 1)))) * |a - a0| := by ring
      _ ≤ (eps / 2) * |a - a0| := mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
  have hstep2 : D * (a - a0) ^ 2 ≤ (eps / 2) * |a - a0| := by
    rw [hq]
    have hfac : D * |a - a0| ≤ eps / 2 := by
      have hrw : D * (eps / (2 * (D + 1))) = (D / (D + 1)) * (eps / 2) := by
        field_simp
      have hle : D / (D + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      calc D * |a - a0| ≤ D * (eps / (2 * (D + 1))) := mul_le_mul_of_nonneg_left h2a hDnn
        _ = (D / (D + 1)) * (eps / 2) := hrw
        _ ≤ 1 * (eps / 2) := mul_le_mul_of_nonneg_right hle (by linarith)
        _ = eps / 2 := one_mul _
    calc D * (|a - a0| * |a - a0|) = (D * |a - a0|) * |a - a0| := by ring
      _ ≤ (eps / 2) * |a - a0| := mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
  have hfinal : |y a x - y a0 x - (a - a0) * z x| ≤ eps * |a - a0| := by
    have := hea
    rw [hD] at hstep2
    linarith [hstep1, hstep1', hstep2]
  simpa using hfinal

/-- A worked instance confirming that the hypotheses of `hasDerivAt_param` are
not contradictory: for `y' = a` with initial value `y(a, 0) = a²`, the solution
is `y(a,x) = a² + a x` and the variational solution at `a₀ = 1` is `z(x) = 2 + x`. -/
example (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : HasDerivAt (fun a : ℝ => a ^ 2 + a * x) (2 + x) 1 := by
  refine hasDerivAt_param (f := fun a _ _ => a) (fa := fun _ _ _ => 1)
    (fy := fun _ _ _ => 0) (y := fun a x => a ^ 2 + a * x) (z := fun x => 2 + x)
    (c := fun a => a ^ 2) (a0 := 1) (x0 := 0) (x1 := 1) (L := 0) (C := 0) (A := 1)
    zero_le_one le_rfl le_rfl zero_le_one ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ x hx
  · intro a w
    simpa using ((hasDerivAt_id w).const_mul a).const_add (a ^ 2)
  · intro a; simp
  · simpa using (hasDerivAt_pow 2 (1:ℝ))
  · intro w
    simpa using (hasDerivAt_id w).const_add 2
  · intro _ _ _ _; simp
  · intro _; simp
  · intro _ _ _; simp
  · intro _ _ _; simp

end ODEParameterDeriv
