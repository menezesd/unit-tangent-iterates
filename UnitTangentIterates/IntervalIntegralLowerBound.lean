import Mathlib

/-! # Lower bounds for oriented interval integrals -/

noncomputable section

open Set MeasureTheory intervalIntegral

namespace IntervalIntegralLowerBound

/-- A pointwise lower bound on an oriented interval integrates to the
corresponding constant-times-length lower bound. -/
theorem const_mul_length_le_integral
    {f : ℝ → ℝ} {c a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hlow : ∀ x ∈ Icc a b, c ≤ f x) :
    c * (b - a) ≤ ∫ x in a..b, f x := by
  have hc : IntervalIntegrable (fun _ : ℝ => c) volume a b :=
    _root_.intervalIntegrable_const
  have hmono : (∫ _ in a..b, c) ≤ ∫ x in a..b, f x :=
    intervalIntegral.integral_mono_on hab hc hf hlow
  simpa [hab, mul_comm] using hmono

/-- Strict positivity follows from a positive lower bound on an interval of
positive length. -/
theorem integral_pos_of_pos_lower
    {f : ℝ → ℝ} {c a b : ℝ} (hab : a < b) (hc : 0 < c)
    (hf : IntervalIntegrable f volume a b)
    (hlow : ∀ x ∈ Icc a b, c ≤ f x) :
    0 < ∫ x in a..b, f x := by
  have hle := const_mul_length_le_integral hab.le hf hlow
  exact lt_of_lt_of_le (mul_pos hc (sub_pos.mpr hab)) hle

end IntervalIntegralLowerBound
