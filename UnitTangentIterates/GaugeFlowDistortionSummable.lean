import Mathlib

/-!
# Summable near-identity gauge-flow distortion

The physical `W` component acquires the multiplicative factor `exp x` under
the gauge flow.  On a small nonnegative range its excess over one is linear
in `x`, so any summable gauge-rate budget gives a summable multiplicative
distortion budget.
-/

noncomputable section

open Real

namespace GaugeFlowDistortionSummable

theorem exp_sub_one_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ 2 * x := by
  have habs : |x| ≤ 1 := by simpa [abs_of_nonneg hx0] using hx1
  have h := Real.abs_exp_sub_one_le habs
  have hexp : 0 ≤ Real.exp x - 1 := by
    exact sub_nonneg.mpr ((Real.one_le_exp_iff).2 hx0)
  simpa [abs_of_nonneg hexp, abs_of_nonneg hx0] using h

theorem summable_exp_sub_one_of_small
    {x d : ℕ → ℝ} {C : ℝ}
    (hd : Summable d) (hd0 : ∀ k, 0 ≤ d k)
    (hC : 0 ≤ C) (hx0 : ∀ k, 0 ≤ x k)
    (hx1 : ∀ k, x k ≤ 1) (hxd : ∀ k, x k ≤ C * d k) :
    Summable (fun k => Real.exp (x k) - 1) := by
  have hmajor : Summable (fun k => (2 * C) * d k) := hd.mul_left (2 * C)
  refine hmajor.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
  · exact sub_nonneg.mpr ((Real.one_le_exp_iff).2 (hx0 k))
  · calc
      Real.exp (x k) - 1 ≤ 2 * x k := exp_sub_one_le_two_mul (hx0 k) (hx1 k)
      _ ≤ 2 * (C * d k) := mul_le_mul_of_nonneg_left (hxd k) (by norm_num)
      _ = (2 * C) * d k := by ring

theorem tsum_exp_sub_one_le
    {x d : ℕ → ℝ} {C : ℝ}
    (hd : Summable d) (hd0 : ∀ k, 0 ≤ d k)
    (hC : 0 ≤ C) (hx0 : ∀ k, 0 ≤ x k)
    (hx1 : ∀ k, x k ≤ 1) (hxd : ∀ k, x k ≤ C * d k) :
    ∑' k, (Real.exp (x k) - 1) ≤ 2 * C * ∑' k, d k := by
  have hs := summable_exp_sub_one_of_small hd hd0 hC hx0 hx1 hxd
  calc
    ∑' k, (Real.exp (x k) - 1) ≤ ∑' k, (2 * C) * d k :=
      hs.tsum_le_tsum
        (fun k => by
          calc
            Real.exp (x k) - 1 ≤ 2 * x k :=
              exp_sub_one_le_two_mul (hx0 k) (hx1 k)
            _ ≤ 2 * (C * d k) :=
              mul_le_mul_of_nonneg_left (hxd k) (by norm_num)
            _ = (2 * C) * d k := by ring)
        (hd.mul_left (2 * C))
    _ = 2 * C * ∑' k, d k := by rw [tsum_mul_left]

end GaugeFlowDistortionSummable
