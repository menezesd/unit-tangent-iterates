import Mathlib
import UnitTangentIterates.PeriodicGreen

/-!
# A maximum principle for bounded solutions of a dissipative linear equation

`SelectedRear.periodic_linear_sup_bound` bounds a **periodic** solution of

```
  u' + a u = f ,     a ≥ c > 0 ,   |f| ≤ M
```

by `M / c`, by looking at the maximum of `u` over one period.  Along a path of
fronts whose perimeter changes, the objects to be bounded — the difference of
two steering angles, and the error of its linear prediction — are periodic with
*different* periods, so no such maximum is available; but they are still
bounded.

This file replaces periodicity by boundedness.  Integrating the equation gives,
for `x ≤ x₀`,

```
  u(x₀) = u(x) e^{-(A(x₀)-A(x))} + ∫_x^{x₀} f(t) e^{-(A(x₀)-A(t))} dt ,
```

with `A` the primitive of `a`; the first term is at most `B e^{-c(x₀-x)}` and
the second at most `M/c`, uniformly in `x`, so letting `x → -∞` gives
`|u(x₀)| ≤ M/c`.

Main result: `abs_le_of_bounded_dissipative`.
-/

noncomputable section

open Set MeasureTheory

namespace BoundedLinearBound

open PeriodicGreen

variable {u a f : ℝ → ℝ} {c M B : ℝ}

/-- The primitive of the coefficient grows at least linearly. -/
theorem prim_sub_ge (hacont : Continuous a) (ha : ∀ x, c ≤ a x) {x y : ℝ} (hxy : x ≤ y) :
    c * (y - x) ≤ prim a y - prim a x := by
  rw [prim_sub_eq hacont]
  have h : (∫ _ in x..y, c) ≤ ∫ t in x..y, a t :=
    intervalIntegral.integral_mono_on hxy intervalIntegrable_const
      (hacont.intervalIntegrable _ _) (fun t _ => ha t)
  simpa [mul_comm] using h

/-- **The variation-of-constants formula.**  For a solution of `u' = f - a u`
and `x ≤ x₀`, the value at `x₀` is the decayed value at `x` plus the decayed
integral of the source. -/
theorem repr_of_hasDerivAt (hacont : Continuous a) (hfcont : Continuous f)
    (hu : ∀ x, HasDerivAt u (f x - a x * u x) x) (x x₀ : ℝ) :
    u x₀ = u x * Real.exp (-(prim a x₀ - prim a x))
      + ∫ t in x..x₀, f t * Real.exp (-(prim a x₀ - prim a t)) := by
  set G : ℝ → ℝ := fun t => u t * Real.exp (prim a t) with hG
  have hGderiv : ∀ t, HasDerivAt G (f t * Real.exp (prim a t)) t := by
    intro t
    have hexp : HasDerivAt (fun y => Real.exp (prim a y)) (Real.exp (prim a t) * a t) t := by
      simpa [mul_comm] using (Real.hasDerivAt_exp (prim a t)).comp t (hasDerivAt_prim hacont t)
    have h := (hu t).mul hexp
    refine h.congr_deriv ?_
    ring
  have hcont : Continuous fun t => f t * Real.exp (prim a t) :=
    hfcont.mul (Real.continuous_exp.comp (continuous_prim hacont))
  have hFTC : (∫ t in x..x₀, f t * Real.exp (prim a t)) = G x₀ - G x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hGderiv t)
      (hcont.intervalIntegrable _ _)
  have hexp0 : Real.exp (prim a x₀) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hshift : (∫ t in x..x₀, f t * Real.exp (-(prim a x₀ - prim a t)))
      = Real.exp (-prim a x₀) * ∫ t in x..x₀, f t * Real.exp (prim a t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [← mul_assoc, mul_comm (Real.exp (-prim a x₀)) (f t), mul_assoc, ← Real.exp_add]
    ring_nf
  rw [hshift, hFTC, hG]
  have hsplit : Real.exp (-(prim a x₀ - prim a x))
      = Real.exp (-prim a x₀) * Real.exp (prim a x) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have hinv : Real.exp (-prim a x₀) * Real.exp (prim a x₀) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (-(u x₀)) * hinv

/-- The decayed integral of the source is at most `M / c`. -/
theorem abs_integral_le (hc : 0 < c) (hacont : Continuous a) (hfcont : Continuous f)
    (ha : ∀ x, c ≤ a x) (hM : ∀ x, |f x| ≤ M) {x x₀ : ℝ} (hxx : x ≤ x₀) :
    |∫ t in x..x₀, f t * Real.exp (-(prim a x₀ - prim a t))| ≤ M / c := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hcont1 : Continuous fun t => f t * Real.exp (-(prim a x₀ - prim a t)) :=
    hfcont.mul (Real.continuous_exp.comp (continuous_const.sub (continuous_prim hacont)).neg)
  have hcont2 : Continuous fun t : ℝ => M * Real.exp (-(c * (x₀ - t))) :=
    continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.sub continuous_id)).neg)
  have hstep : |∫ t in x..x₀, f t * Real.exp (-(prim a x₀ - prim a t))|
      ≤ ∫ t in x..x₀, M * Real.exp (-(c * (x₀ - t))) := by
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hxx) ?_
    refine intervalIntegral.integral_mono_on hxx (hcont1.abs.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _) (fun t ht => ?_)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hle : c * (x₀ - t) ≤ prim a x₀ - prim a t := prim_sub_ge hacont ha ht.2
    have hexp : Real.exp (-(prim a x₀ - prim a t)) ≤ Real.exp (-(c * (x₀ - t))) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul (hM t) hexp (le_of_lt (Real.exp_pos _)) hMnn
  have hval : (∫ t in x..x₀, M * Real.exp (-(c * (x₀ - t))))
      = M / c * (1 - Real.exp (-(c * (x₀ - x)))) := by
    have hderiv : ∀ t : ℝ, HasDerivAt (fun s => M / c * Real.exp (-(c * (x₀ - s))))
        (M * Real.exp (-(c * (x₀ - t)))) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => -(c * (x₀ - s))) c t := by
        simpa using (((hasDerivAt_id t).const_sub x₀).const_mul c).neg
      have h2 : HasDerivAt (fun s : ℝ => Real.exp (-(c * (x₀ - s))))
          (Real.exp (-(c * (x₀ - t))) * c) t := (Real.hasDerivAt_exp _).comp t h1
      have h3 := h2.const_mul (M / c)
      refine h3.congr_deriv ?_
      field_simp
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := x₀)
      (fun t _ => hderiv t) ((hcont2).intervalIntegrable _ _)
    rw [this]
    simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
    ring
  rw [hval] at hstep
  have hfac : M / c * (1 - Real.exp (-(c * (x₀ - x)))) ≤ M / c := by
    have h1 : 0 ≤ M / c := by positivity
    have h2 : 1 - Real.exp (-(c * (x₀ - x))) ≤ 1 := by
      have := Real.exp_pos (-(c * (x₀ - x)))
      linarith
    nlinarith
  linarith

/-- **The maximum principle for bounded solutions.**  A bounded solution of
`u' + a u = f` with `a ≥ c > 0` and `|f| ≤ M` satisfies `|u| ≤ M / c`, with no
periodicity assumed. -/
theorem abs_le_of_bounded_dissipative (hc : 0 < c) (hacont : Continuous a)
    (hfcont : Continuous f) (ha : ∀ x, c ≤ a x)
    (hu : ∀ x, HasDerivAt u (f x - a x * u x) x)
    (hB : ∀ x, |u x| ≤ B) (hM : ∀ x, |f x| ≤ M) (x₀ : ℝ) :
    |u x₀| ≤ M / c := by
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  -- choose a far enough starting point
  obtain ⟨x, hxle, hsmall⟩ : ∃ x : ℝ, x ≤ x₀ ∧ B * Real.exp (-(c * (x₀ - x))) ≤ ε := by
    have hpos : 0 < ε / (B + 1) := by positivity
    obtain ⟨y, hy⟩ := exists_gt (Real.log (ε / (B + 1)) / (-c))
    refine ⟨x₀ - (max 0 (Real.log ((B + 1) / ε) / c) + 1), by
      have : (0:ℝ) ≤ max 0 (Real.log ((B + 1) / ε) / c) := le_max_left _ _
      linarith, ?_⟩
    set d : ℝ := max 0 (Real.log ((B + 1) / ε) / c) + 1 with hd
    have hd0 : Real.log ((B + 1) / ε) / c ≤ d := by
      have := le_max_right (0 : ℝ) (Real.log ((B + 1) / ε) / c)
      rw [hd]; linarith
    have hdc : Real.log ((B + 1) / ε) ≤ c * d := by
      rw [div_le_iff₀ hc] at hd0
      linarith [hd0]
    have hxx : x₀ - (x₀ - d) = d := by ring
    rw [hxx]
    have hexp : Real.exp (-(c * d)) ≤ ε / (B + 1) := by
      have h1 : Real.exp (Real.log ((B + 1) / ε)) = (B + 1) / ε :=
        Real.exp_log (by positivity)
      have h2 : Real.exp (Real.log ((B + 1) / ε)) ≤ Real.exp (c * d) :=
        Real.exp_le_exp.mpr hdc
      rw [h1] at h2
      rw [Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos _) (by positivity)]
      calc (ε / (B + 1))⁻¹ = (B + 1) / ε := by
            rw [inv_div]
        _ ≤ Real.exp (c * d) := h2
    calc B * Real.exp (-(c * d)) ≤ B * (ε / (B + 1)) :=
          mul_le_mul_of_nonneg_left hexp hBnn
      _ ≤ ε := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  have hrepr := repr_of_hasDerivAt hacont hfcont hu x x₀
  have h1 : |u x * Real.exp (-(prim a x₀ - prim a x))| ≤ ε := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hle : c * (x₀ - x) ≤ prim a x₀ - prim a x := prim_sub_ge hacont ha hxle
    have hexp : Real.exp (-(prim a x₀ - prim a x)) ≤ Real.exp (-(c * (x₀ - x))) :=
      Real.exp_le_exp.mpr (by linarith)
    calc |u x| * Real.exp (-(prim a x₀ - prim a x))
        ≤ B * Real.exp (-(c * (x₀ - x))) :=
          mul_le_mul (hB x) hexp (le_of_lt (Real.exp_pos _)) hBnn
      _ ≤ ε := hsmall
  have h2 := abs_integral_le hc hacont hfcont ha hM hxle
  calc |u x₀| ≤ |u x * Real.exp (-(prim a x₀ - prim a x))|
        + |∫ t in x..x₀, f t * Real.exp (-(prim a x₀ - prim a t))| := by
        rw [hrepr]; exact abs_add_le _ _
    _ ≤ ε + M / c := add_le_add h1 h2
    _ = M / c + ε := by ring

end BoundedLinearBound
