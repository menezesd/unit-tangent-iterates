import Mathlib
import UnitTangentIterates.Shadowing

/-!
# Contraction and smooth dependence for the selected rear

This file formalizes the remaining quantitative core of the lemma *Smooth
dependence of the selected rear* of the paper *A Noncircular Oval with Convex
Unit-Tangent Iterates*.

Parametrizing a strictly convex front by its tangent angle `φ` and writing
`q = 1/K` for its radius of curvature, the selected steering angle solves

```
  δ_φ = 1 - q(φ) sin δ ,
```

and the linearization along a solution is `w_φ + q cos δ · w = f`.  On the
selected strip `0 ≤ δ ≤ arcsin κ̂` the zeroth-order coefficient is bounded
below by `κ̂^{-1}√(1-κ̂²) > 0` (`Shadowing.zeroth_order_coeff_ge`).  Two
consequences are formalized here.

* The flow of the steering equation contracts exponentially inside the strip:
  any two solutions satisfy `|δ¹ - δ²|(x) ≤ e^{-c(x-x₀)}|δ¹ - δ²|(x₀)` with
  `c = κ̂^{-1}√(1-κ̂²)`.  Hence the fixed point of the Poincaré map is
  hyperbolic (attracting), and the periodic solution inside the strip is
  unique.
* The periodic linearized equation obeys the uniform maximum-principle bound
  `‖w‖_∞ ≤ ‖f‖_∞ / c`, which is the uniform bound making the fixed point
  depend smoothly on the path parameter.

Main results:

* `sin_sub_sin_ge_of_strip`, `sin_sub_mul_self_ge` : the uniform slope bound
  for `sin` on the selected strip;
* `steering_diff_decay` : the exponential contraction of the steering flow;
* `steering_periodic_unique_of_strip` : uniqueness of the periodic steering
  solution inside the strip;
* `periodic_linear_sup_bound` : the maximum-principle bound `‖w‖_∞ ≤ M / c`
  for `w_φ + a w = f` with `a ≥ c > 0`;
* `selected_steering_variation_bound` : the resulting bound for the variation
  of the selected steering angle along a path of fronts;
* `steering_sup_dist_le` : the continuous dependence of the selected steering
  angle on the front curvature, `‖δ¹ - δ²‖_∞ ≤ ‖K¹ - K²‖_∞/√(1-κ̂²)`, which is
  the continuous-dependence clause of the lemma *Selected inverse on the
  closed strip*.
-/

noncomputable section

open Real Set

namespace SelectedRear

/-! ### A uniform slope bound for `sin` on the selected strip -/

/-- On the selected strip `[0, arcsin κ̂]` the sine function has slope at least
`√(1 - κ̂²)`: for `b ≤ a` in the strip, `√(1-κ̂²)(a - b) ≤ sin a - sin b`. -/
theorem sin_sub_sin_ge_of_strip {kap a b : ℝ}
    (ha : a ∈ Icc (0:ℝ) (arcsin kap)) (hb : b ∈ Icc (0:ℝ) (arcsin kap)) (hab : b ≤ a) :
    Real.sqrt (1 - kap ^ 2) * (a - b) ≤ Real.sin a - Real.sin b := by
  set m : ℝ := Real.sqrt (1 - kap ^ 2) with hm
  set g : ℝ → ℝ := fun x => Real.sin x - m * x with hg
  have hderiv : ∀ x, HasDerivAt g (Real.cos x - m) x := by
    intro x
    simpa [hg] using (Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).const_mul m)
  have hmono : MonotoneOn g (Icc (0:ℝ) (arcsin kap)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact (Differentiable.continuous (fun x => (hderiv x).differentiableAt)).continuousOn
    · intro x hx
      exact ((hderiv x).differentiableAt).differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Icc (0:ℝ) (arcsin kap) := Ioo_subset_Icc_self (by simpa using hx)
      have hcos : m ≤ Real.cos x := Shadowing.cos_ge_of_mem_strip hx'.1 hx'.2
      have : deriv g x = Real.cos x - m := (hderiv x).deriv
      rw [this]
      linarith
  have := hmono hb ha hab
  simp only [hg] at this
  nlinarith [this]

/-- The symmetric form of the slope bound: `(sin a - sin b)(a - b) ≥
√(1-κ̂²)(a-b)²` for `a, b` in the selected strip. -/
theorem sin_sub_mul_self_ge {kap a b : ℝ}
    (ha : a ∈ Icc (0:ℝ) (arcsin kap)) (hb : b ∈ Icc (0:ℝ) (arcsin kap)) :
    Real.sqrt (1 - kap ^ 2) * (a - b) ^ 2 ≤ (Real.sin a - Real.sin b) * (a - b) := by
  rcases le_total b a with hab | hab
  · have := sin_sub_sin_ge_of_strip ha hb hab
    nlinarith [sub_nonneg.mpr hab]
  · have := sin_sub_sin_ge_of_strip hb ha hab
    nlinarith [sub_nonneg.mpr hab]

/-! ### Exponential contraction of the steering flow -/

section Contraction

variable {q d1 d2 : ℝ → ℝ} {kap : ℝ}

/-- **The steering flow contracts exponentially inside the selected strip.**
If `δ¹, δ²` both solve `δ_φ = 1 - q sin δ` and both stay inside
`[0, arcsin κ̂]`, and if the radius of curvature satisfies `q ≥ 1/κ̂`, then
`|δ¹ - δ²|` decays at the exponential rate `c = κ̂^{-1}√(1-κ̂²)`. -/
theorem steering_diff_decay (hkap : 0 < kap)
    (hq : ∀ x, kap⁻¹ ≤ q x)
    (h1 : ∀ x, HasDerivAt d1 (1 - q x * Real.sin (d1 x)) x)
    (h2 : ∀ x, HasDerivAt d2 (1 - q x * Real.sin (d2 x)) x)
    (hs1 : ∀ x, d1 x ∈ Icc (0:ℝ) (arcsin kap)) (hs2 : ∀ x, d2 x ∈ Icc (0:ℝ) (arcsin kap))
    {x0 x : ℝ} (hx : x0 ≤ x) :
    |d1 x - d2 x| ≤ Real.exp (-(Real.sqrt (1 - kap ^ 2) / kap * (x - x0))) * |d1 x0 - d2 x0| := by
  set m : ℝ := Real.sqrt (1 - kap ^ 2) with hm
  set c : ℝ := m / kap with hc
  set W : ℝ → ℝ := fun y => d1 y - d2 y with hW
  have hWd : ∀ y, HasDerivAt W (q y * Real.sin (d2 y) - q y * Real.sin (d1 y)) y := by
    intro y
    simpa [hW] using ((h1 y).sub (h2 y)).congr_deriv (by ring)
  set G : ℝ → ℝ := fun y => W y ^ 2 * Real.exp (2 * c * y) with hG
  have hGd : ∀ y, HasDerivAt G
      (2 * W y * (q y * Real.sin (d2 y) - q y * Real.sin (d1 y)) * Real.exp (2 * c * y)
        + W y ^ 2 * (Real.exp (2 * c * y) * (2 * c))) y := by
    intro y
    have h1' : HasDerivAt (fun z => W z ^ 2)
        (2 * W y * (q y * Real.sin (d2 y) - q y * Real.sin (d1 y))) y := by
      simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using (hWd y).pow 2
    have h2' : HasDerivAt (fun z => Real.exp (2 * c * z)) (Real.exp (2 * c * y) * (2 * c)) y := by
      simpa using ((hasDerivAt_id y).const_mul (2 * c)).exp
    simpa [hG] using h1'.mul h2'
  have hnonpos : ∀ y, deriv G y ≤ 0 := by
    intro y
    rw [(hGd y).deriv]
    have hslope : m * (d1 y - d2 y) ^ 2 ≤ (Real.sin (d1 y) - Real.sin (d2 y)) * (d1 y - d2 y) :=
      sin_sub_mul_self_ge (hs1 y) (hs2 y)
    have hXnonneg : 0 ≤ (Real.sin (d1 y) - Real.sin (d2 y)) * (d1 y - d2 y) := by
      have : 0 ≤ m * (d1 y - d2 y) ^ 2 :=
        mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
      linarith
    have hqge : kap⁻¹ * ((Real.sin (d1 y) - Real.sin (d2 y)) * (d1 y - d2 y))
        ≤ q y * ((Real.sin (d1 y) - Real.sin (d2 y)) * (d1 y - d2 y)) :=
      mul_le_mul_of_nonneg_right (hq y) hXnonneg
    have hkinv : (0:ℝ) < kap⁻¹ := by positivity
    have hcw : c * (d1 y - d2 y) ^ 2
        ≤ q y * ((Real.sin (d1 y) - Real.sin (d2 y)) * (d1 y - d2 y)) := by
      have : kap⁻¹ * (m * (d1 y - d2 y) ^ 2)
          ≤ kap⁻¹ * ((Real.sin (d1 y) - Real.sin (d2 y)) * (d1 y - d2 y)) :=
        mul_le_mul_of_nonneg_left hslope hkinv.le
      have hceq : c * (d1 y - d2 y) ^ 2 = kap⁻¹ * (m * (d1 y - d2 y) ^ 2) := by
        rw [hc]
        field_simp
      rw [hceq]
      linarith
    have hexp : 0 < Real.exp (2 * c * y) := Real.exp_pos _
    have hexpand : 2 * W y * (q y * Real.sin (d2 y) - q y * Real.sin (d1 y))
        = -2 * (q y * ((Real.sin (d1 y) - Real.sin (d2 y)) * (d1 y - d2 y))) := by
      simp only [hW]; ring
    have hWsq : W y ^ 2 = (d1 y - d2 y) ^ 2 := by simp [hW]
    rw [hexpand, hWsq]
    nlinarith [hexp, hcw]
  have hdiff : Differentiable ℝ G := fun y => (hGd y).differentiableAt
  have hanti : Antitone G := antitone_of_deriv_nonpos hdiff hnonpos
  have hGle : G x ≤ G x0 := hanti hx
  -- convert the inequality for squares into one for absolute values
  have hsq : ∀ y : ℝ, Real.exp (c * y) ^ 2 = Real.exp (2 * c * y) := by
    intro y
    rw [pow_two, ← Real.exp_add]
    ring_nf
  have hx1 : (|W x| * Real.exp (c * x)) ^ 2 ≤ (|W x0| * Real.exp (c * x0)) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs, sq_abs, hsq, hsq]
    exact hGle
  have hbase : |W x| * Real.exp (c * x) ≤ |W x0| * Real.exp (c * x0) := by
    have h0 : 0 ≤ |W x| * Real.exp (c * x) := by positivity
    have h1'' : 0 ≤ |W x0| * Real.exp (c * x0) := by positivity
    nlinarith [hx1, h0, h1'']
  have hfinal : |W x| ≤ Real.exp (-(c * (x - x0))) * |W x0| := by
    have hpos : 0 < Real.exp (c * x) := Real.exp_pos _
    refine le_of_mul_le_mul_right ?_ hpos
    calc |W x| * Real.exp (c * x) ≤ |W x0| * Real.exp (c * x0) := hbase
      _ = Real.exp (-(c * (x - x0))) * |W x0| * Real.exp (c * x) := by
          rw [mul_comm (Real.exp (-(c * (x - x0)))) |W x0|, mul_assoc, ← Real.exp_add,
            show -(c * (x - x0)) + c * x = c * x0 by ring]
  simpa [hW] using hfinal

/-- **Uniqueness of the periodic steering solution inside the selected
strip**, as a consequence of the exponential contraction. -/
theorem steering_periodic_unique_of_strip {P : ℝ} (hP : 0 < P) (hkap : 0 < kap) (hkap1 : kap < 1)
    (hq : ∀ x, kap⁻¹ ≤ q x)
    (h1 : ∀ x, HasDerivAt d1 (1 - q x * Real.sin (d1 x)) x)
    (h2 : ∀ x, HasDerivAt d2 (1 - q x * Real.sin (d2 x)) x)
    (hs1 : ∀ x, d1 x ∈ Icc (0:ℝ) (arcsin kap)) (hs2 : ∀ x, d2 x ∈ Icc (0:ℝ) (arcsin kap))
    (hp1 : Function.Periodic d1 P) (hp2 : Function.Periodic d2 P) :
    d1 = d2 := by
  have hmpos : 0 < Real.sqrt (1 - kap ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) / kap := div_pos hmpos hkap
  funext x
  have hdecay := steering_diff_decay hkap hq h1 h2 hs1 hs2 (x0 := x - P) (x := x) (by linarith)
  have hper : d1 (x - P) - d2 (x - P) = d1 x - d2 x := by
    have e1 : d1 x = d1 (x - P) := by simpa using hp1 (x - P)
    have e2 : d2 x = d2 (x - P) := by simpa using hp2 (x - P)
    rw [e1, e2]
  rw [hper, show x - (x - P) = P by ring] at hdecay
  have hlt : Real.exp (-(Real.sqrt (1 - kap ^ 2) / kap * P)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  have habs : |d1 x - d2 x| = 0 := by
    nlinarith [abs_nonneg (d1 x - d2 x), hdecay, hlt]
  have := abs_eq_zero.mp habs
  linarith

end Contraction

/-! ### The maximum-principle bound for the periodic linearization -/

/-- One half of the maximum principle: a periodic solution of `w' + a w = f`
with `a ≥ c > 0` and `f ≤ M` satisfies `w ≤ M / c`. -/
theorem periodic_linear_le {w a f : ℝ → ℝ} {P c M : ℝ} (hP : 0 < P)
    (hw : ∀ x, HasDerivAt w (f x - a x * w x) x) (hper : Function.Periodic w P)
    (hc : 0 < c) (ha : ∀ x, c ≤ a x) (hM : 0 ≤ M) (hf : ∀ x, f x ≤ M) :
    ∀ x, w x ≤ M / c := by
  have hdiff : Differentiable ℝ w := fun x => (hw x).differentiableAt
  have hcont : Continuous w := hdiff.continuous
  obtain ⟨t0, ht0mem, ht0⟩ := isCompact_Icc.exists_isMaxOn (s := Icc (0:ℝ) P)
    (Set.nonempty_Icc.mpr hP.le) hcont.continuousOn
  have hglobal : ∀ x, w x ≤ w t0 := by
    intro x
    obtain ⟨y, hy, hys⟩ := hper.exists_mem_Ico₀ hP x
    rw [hys]
    exact ht0 ⟨hy.1, hy.2.le⟩
  have hmax : IsLocalMax w t0 := Filter.Eventually.of_forall hglobal
  have hzero : f t0 - a t0 * w t0 = 0 := hmax.hasDerivAt_eq_zero (hw t0)
  have hle : w t0 ≤ M / c := by
    rcases le_or_gt (w t0) 0 with h | h
    · exact le_trans h (by positivity)
    · have h1 : c * w t0 ≤ a t0 * w t0 := mul_le_mul_of_nonneg_right (ha t0) h.le
      rw [le_div_iff₀ hc]
      linarith [hf t0]
  exact fun x => le_trans (hglobal x) hle

/-- **The uniform bound for the periodic linearized equation.**  If `w` is
`P`-periodic and solves `w' + a w = f` with `a ≥ c > 0` and `|f| ≤ M`, then
`|w| ≤ M / c` everywhere.  This is the uniform bound behind the invertibility
of the periodic linearization in the lemma *Smooth dependence of the selected
rear*. -/
theorem periodic_linear_sup_bound {w a f : ℝ → ℝ} {P c M : ℝ} (hP : 0 < P)
    (hw : ∀ x, HasDerivAt w (f x - a x * w x) x) (hper : Function.Periodic w P)
    (hc : 0 < c) (ha : ∀ x, c ≤ a x) (hf : ∀ x, |f x| ≤ M) :
    ∀ x, |w x| ≤ M / c := by
  have hM : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hf 0)
  have hupper := periodic_linear_le hP hw hper hc ha hM (fun x => (abs_le.mp (hf x)).2)
  have hlower := periodic_linear_le (w := fun x => -w x) (f := fun x => -f x) hP
    (fun x => ((hw x).neg).congr_deriv (by ring)) (fun x => by simp [hper x]) hc ha hM
    (fun x => by linarith [(abs_le.mp (hf x)).1])
  intro x
  rw [abs_le]
  constructor
  · have := hlower x
    simp only at this
    linarith
  · exact hupper x

/-- **The variation of the selected steering angle is uniformly bounded.**
Along a path of fronts with radius of curvature `q`, the derivative `w` of the
selected steering angle with respect to the path parameter solves
`w_φ + q cos δ · w = -q̇ sin δ`; on the selected strip the zeroth-order
coefficient is at least `κ̂^{-1}√(1-κ̂²)`, so `w` is bounded by
`κ̂ ‖q̇‖_∞ / √(1-κ̂²)`. -/
theorem selected_steering_variation_bound {w q qdot delta : ℝ → ℝ} {P kap M : ℝ}
    (hP : 0 < P) (hkap : 0 < kap) (hkap1 : kap < 1)
    (hq : ∀ x, kap⁻¹ ≤ q x)
    (hs : ∀ x, delta x ∈ Icc (0:ℝ) (arcsin kap))
    (hqdot : ∀ x, |qdot x| ≤ M)
    (hw : ∀ x, HasDerivAt w (-(qdot x * Real.sin (delta x)) - q x * Real.cos (delta x) * w x) x)
    (hper : Function.Periodic w P) :
    ∀ x, |w x| ≤ kap * M / Real.sqrt (1 - kap ^ 2) := by
  have hmpos : 0 < Real.sqrt (1 - kap ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) / kap := div_pos hmpos hkap
  have hcoeff : ∀ x, Real.sqrt (1 - kap ^ 2) / kap ≤ q x * Real.cos (delta x) := by
    intro x
    have hcos : Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta x) :=
      Shadowing.cos_ge_of_mem_strip (hs x).1 (hs x).2
    have hkinv : kap⁻¹ ≤ q x := hq x
    have h1 : kap⁻¹ * Real.sqrt (1 - kap ^ 2) ≤ q x * Real.cos (delta x) := by
      apply mul_le_mul hkinv hcos hmpos.le
      exact le_trans (by positivity) hkinv
    calc Real.sqrt (1 - kap ^ 2) / kap = kap⁻¹ * Real.sqrt (1 - kap ^ 2) := by
          field_simp
      _ ≤ q x * Real.cos (delta x) := h1
  have hfbd : ∀ x, |(-(qdot x * Real.sin (delta x)))| ≤ M := by
    intro x
    rw [abs_neg, abs_mul]
    calc |qdot x| * |Real.sin (delta x)| ≤ M * 1 := by
          apply mul_le_mul (hqdot x) (Real.abs_sin_le_one _) (abs_nonneg _)
          exact le_trans (abs_nonneg _) (hqdot 0)
      _ = M := by ring
  have hbound := periodic_linear_sup_bound (w := w) (a := fun x => q x * Real.cos (delta x))
    (f := fun x => -(qdot x * Real.sin (delta x))) hP
    (fun x => by simpa using hw x) hper hcpos hcoeff hfbd
  intro x
  have := hbound x
  rw [div_div_eq_mul_div] at this
  calc |w x| ≤ M * kap / Real.sqrt (1 - kap ^ 2) := this
    _ = kap * M / Real.sqrt (1 - kap ^ 2) := by ring_nf

/-! ### Continuous dependence of the selected rear on the front curvature -/

section Dependence

variable {d1 d2 K1 K2 : ℝ → ℝ} {P kap M : ℝ}

/-- One half of the continuous dependence: at the maximum of `δ¹ - δ²` the
steering equation gives `sin δ¹ - sin δ² = K¹ - K²`, and the uniform slope
bound for `sin` on the selected strip converts this into a bound for
`δ¹ - δ²`. -/
theorem steering_sub_le (hP : 0 < P) (hkap1 : kap < 1) (hkap0 : 0 ≤ kap)
    (h1 : ∀ s, HasDerivAt d1 (K1 s - Real.sin (d1 s)) s)
    (h2 : ∀ s, HasDerivAt d2 (K2 s - Real.sin (d2 s)) s)
    (hp1 : Function.Periodic d1 P) (hp2 : Function.Periodic d2 P)
    (hs1 : ∀ s, d1 s ∈ Icc (0:ℝ) (arcsin kap)) (hs2 : ∀ s, d2 s ∈ Icc (0:ℝ) (arcsin kap))
    (hM : ∀ s, K1 s - K2 s ≤ M) (hM0 : 0 ≤ M) :
    ∀ s, d1 s - d2 s ≤ M / Real.sqrt (1 - kap ^ 2) := by
  have hmpos : 0 < Real.sqrt (1 - kap ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  set w : ℝ → ℝ := fun s => d1 s - d2 s with hw
  have hwd : ∀ s, HasDerivAt w ((K1 s - K2 s) - (Real.sin (d1 s) - Real.sin (d2 s))) s := by
    intro s
    simpa [hw] using ((h1 s).sub (h2 s)).congr_deriv (by ring)
  have hdiff : Differentiable ℝ w := fun s => (hwd s).differentiableAt
  have hwper : Function.Periodic w P := fun s => by simp [hw, hp1 s, hp2 s]
  obtain ⟨t0, ht0mem, ht0⟩ := isCompact_Icc.exists_isMaxOn (s := Icc (0:ℝ) P)
    (Set.nonempty_Icc.mpr hP.le) hdiff.continuous.continuousOn
  have hglobal : ∀ s, w s ≤ w t0 := by
    intro s
    obtain ⟨y, hy, hys⟩ := hwper.exists_mem_Ico₀ hP s
    rw [hys]
    exact ht0 ⟨hy.1, hy.2.le⟩
  have hmax : IsLocalMax w t0 := Filter.Eventually.of_forall hglobal
  have hzero : (K1 t0 - K2 t0) - (Real.sin (d1 t0) - Real.sin (d2 t0)) = 0 :=
    hmax.hasDerivAt_eq_zero (hwd t0)
  have hle : w t0 ≤ M / Real.sqrt (1 - kap ^ 2) := by
    rcases le_or_gt (w t0) 0 with h | h
    · exact le_trans h (by positivity)
    · have hslope : Real.sqrt (1 - kap ^ 2) * (d1 t0 - d2 t0)
          ≤ Real.sin (d1 t0) - Real.sin (d2 t0) :=
        sin_sub_sin_ge_of_strip (hs1 t0) (hs2 t0) (by simpa [hw, sub_nonneg] using h.le)
      rw [le_div_iff₀ hmpos]
      have := hM t0
      simp only [hw] at h ⊢
      nlinarith
  exact fun s => le_trans (hglobal s) hle

/-- **Continuous dependence of the selected steering angle on the front
curvature.**  Two periodic steering solutions inside the selected strip, for
front curvatures `K¹` and `K²`, satisfy
`‖δ¹ - δ²‖_∞ ≤ ‖K¹ - K²‖_∞ / √(1 - κ̂²)`.  This is the quantitative form of
the continuous-dependence clause of the lemma *Selected inverse on the closed
strip*. -/
theorem steering_sup_dist_le (hP : 0 < P) (hkap1 : kap < 1) (hkap0 : 0 ≤ kap)
    (h1 : ∀ s, HasDerivAt d1 (K1 s - Real.sin (d1 s)) s)
    (h2 : ∀ s, HasDerivAt d2 (K2 s - Real.sin (d2 s)) s)
    (hp1 : Function.Periodic d1 P) (hp2 : Function.Periodic d2 P)
    (hs1 : ∀ s, d1 s ∈ Icc (0:ℝ) (arcsin kap)) (hs2 : ∀ s, d2 s ∈ Icc (0:ℝ) (arcsin kap))
    (hM : ∀ s, |K1 s - K2 s| ≤ M) :
    ∀ s, |d1 s - d2 s| ≤ M / Real.sqrt (1 - kap ^ 2) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hup := steering_sub_le hP hkap1 hkap0 h1 h2 hp1 hp2 hs1 hs2
    (fun s => (abs_le.mp (hM s)).2) hM0
  have hlo := steering_sub_le hP hkap1 hkap0 h2 h1 hp2 hp1 hs2 hs1
    (fun s => by linarith [(abs_le.mp (hM s)).1]) hM0
  intro s
  rw [abs_le]
  exact ⟨by linarith [hlo s], hup s⟩

end Dependence

end SelectedRear
