import Mathlib

/-!
# Two-sided Taylor bounds for the sine and the cosine

The explicit barriers of Section 3 of *A Noncircular Oval with Convex
Unit-Tangent Iterates* are verified by expanding the residual of the translator
operator to fourth order in the steering shift.  Mathlib's `Real.sin_bound` and
`Real.cos_bound` only give a fourth-order error term, which is one order too
crude for that purpose.  This file supplies the sharp alternating-series
bounds, all proved by the same monotonicity argument (the derivative of the
difference is the previous inequality):

```
  1 - x²/2 ≤ cos x ≤ 1 - x²/2 + x⁴/24 ,
  x - x³/6 ≤ sin x ≤ x - x³/6 + x⁵/120        (x ≥ 0).
```
-/

noncomputable section

open Set

namespace TaylorBounds

/-- If `f` vanishes at `0` and has a nonnegative derivative on `[0, ∞)`, it is
nonnegative there. -/
theorem nonneg_of_deriv_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (h0 : f 0 = 0) (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Ici (0:ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hf y).continuousAt.continuousWithinAt)
      (fun y _ => (hf y).differentiableAt.differentiableWithinAt) ?_
    intro y hy
    rw [interior_Ici] at hy
    rw [(hf y).deriv]
    exact hd y (le_of_lt hy)
  have := hmono (self_mem_Ici) (mem_Ici.mpr hx) hx
  rwa [h0] at this

/-- `1 - x²/2 ≤ cos x`. -/
theorem cos_ge (x : ℝ) : 1 - x ^ 2 / 2 ≤ Real.cos x := by
  rcases eq_or_ne x 0 with rfl | h
  · simp
  · exact (Real.one_sub_sq_div_two_lt_cos h).le

/-- `x - x³/6 ≤ sin x` for `x ≥ 0`. -/
theorem sin_ge {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have key : 0 ≤ Real.sin x - (x - x ^ 3 / 6) := by
    refine nonneg_of_deriv_nonneg
      (f := fun y => Real.sin y - (y - y ^ 3 / 6))
      (f' := fun y => Real.cos y - (1 - y ^ 2 / 2)) ?_ (by simp) ?_ hx
    · intro y
      have h1 : HasDerivAt Real.sin (Real.cos y) y := Real.hasDerivAt_sin y
      have h2 : HasDerivAt (fun y : ℝ => y - y ^ 3 / 6) (1 - y ^ 2 / 2) y := by
        have : HasDerivAt (fun y : ℝ => y - y ^ 3 / 6) (1 - 3 * y ^ 2 / 6) y := by
          simpa using ((hasDerivAt_id y).sub (((hasDerivAt_pow 3 y).div_const 6)))
        convert this using 1
        ring
      exact h1.sub h2
    · intro y _
      linarith [cos_ge y]
  linarith

/-- `cos x ≤ 1 - x²/2 + x⁴/24` for `x ≥ 0`. -/
theorem cos_le {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have key : 0 ≤ (1 - x ^ 2 / 2 + x ^ 4 / 24) - Real.cos x := by
    refine nonneg_of_deriv_nonneg
      (f := fun y => (1 - y ^ 2 / 2 + y ^ 4 / 24) - Real.cos y)
      (f' := fun y => Real.sin y - (y - y ^ 3 / 6)) ?_ (by simp) ?_ hx
    · intro y
      have h1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2 / 2 + y ^ 4 / 24) (-y + y ^ 3 / 6) y := by
        have h2 : HasDerivAt (fun y : ℝ => 1 - y ^ 2 / 2 + y ^ 4 / 24)
            (0 - 2 * y ^ 1 / 2 + 4 * y ^ 3 / 24) y := by
          simpa using
            (((hasDerivAt_const y (1:ℝ)).sub ((hasDerivAt_pow 2 y).div_const 2)).add
              ((hasDerivAt_pow 4 y).div_const 24))
        convert h2 using 1
        ring
      have h3 : HasDerivAt Real.cos (-Real.sin y) y := Real.hasDerivAt_cos y
      have := h1.sub h3
      convert this using 1
      ring
    · intro y hy
      linarith [sin_ge hy]
  linarith

/-- `sin x ≤ x - x³/6 + x⁵/120` for `x ≥ 0`. -/
theorem sin_le {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have key : 0 ≤ (x - x ^ 3 / 6 + x ^ 5 / 120) - Real.sin x := by
    refine nonneg_of_deriv_nonneg
      (f := fun y => (y - y ^ 3 / 6 + y ^ 5 / 120) - Real.sin y)
      (f' := fun y => (1 - y ^ 2 / 2 + y ^ 4 / 24) - Real.cos y) ?_ (by simp) ?_ hx
    · intro y
      have h1 : HasDerivAt (fun y : ℝ => y - y ^ 3 / 6 + y ^ 5 / 120)
          (1 - y ^ 2 / 2 + y ^ 4 / 24) y := by
        have h2 : HasDerivAt (fun y : ℝ => y - y ^ 3 / 6 + y ^ 5 / 120)
            (1 - 3 * y ^ 2 / 6 + 5 * y ^ 4 / 120) y := by
          simpa using
            (((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
              ((hasDerivAt_pow 5 y).div_const 120))
        convert h2 using 1
        ring
      exact h1.sub (Real.hasDerivAt_sin y)
    · intro y hy
      linarith [cos_le hy]
  linarith

end TaylorBounds
