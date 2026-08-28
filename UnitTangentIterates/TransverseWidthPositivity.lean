import Mathlib

/-! # Positivity base for transverse width -/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace TransverseWidthPositivity

/-- A tangent angle taking values in `[0,pi]` has nonnegative transverse
displacement on an oriented interval. -/
theorem integral_sin_nonneg
    {theta : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable (fun s => Real.sin (theta s)) volume a b)
    (hangle : ∀ s ∈ Icc a b, theta s ∈ Icc (0 : ℝ) Real.pi) :
    0 ≤ ∫ s in a..b, Real.sin (theta s) := by
  exact intervalIntegral.integral_nonneg hab fun s hs =>
    Real.sin_nonneg_of_mem_Icc (hangle s hs)

/-- If the tangent angle lies strictly between `0` and `pi` throughout the
interior of a nondegenerate interval, its transverse displacement is strictly
positive. -/
theorem integral_sin_pos
    {theta : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (htheta : Continuous theta)
    (hangle : ∀ s ∈ Ioo a b, theta s ∈ Ioo (0 : ℝ) Real.pi) :
    0 < ∫ s in a..b, Real.sin (theta s) := by
  have hc : Continuous fun s => Real.sin (theta s) := Real.continuous_sin.comp htheta
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (show IntervalIntegrable (fun s => Real.sin (theta s)) volume a b from
      hc.intervalIntegrable a b) ?_ hab
  intro s hs
  exact Real.sin_pos_of_pos_of_lt_pi (hangle s hs).1 (hangle s hs).2

end TransverseWidthPositivity
