import Mathlib
import UnitTangentIterates.Barriers
import UnitTangentIterates.TaylorBounds

/-!
# Quantitative bounds for the three residual factors

`Barriers.lean` factors the normalized residual of the translator operator
through the three functions

```
  Φ₀(r) = 2(√r / tan √r − 1)/r ,  Φ₁(r) = 2(cos √r − 1)/r ,
  Φ₂(r) = 2(sin √r − √r)/(r tan √r) ,
```

and computes their limits `Φ₀(0) = −2/3`, `Φ₁(0) = −1`, `Φ₂(0) = −1/3`.  The
verification of the explicit barriers needs those limits with an explicit rate.
This file provides them, for `r = d²` with `0 < d ≤ 1`:

* `Phi1_ge`, `Phi1_le` : `−1 ≤ Φ₁(d²) ≤ −1 + d²/12`;
* `abs_Phi0_add_le` : `|Φ₀(d²) + 2/3| ≤ d²/6`;
* `abs_Phi2_le` : `|Φ₂(d²)| ≤ 1/3`.
-/

noncomputable section

open Real Set

namespace PhiBounds

variable {d : ℝ}

theorem sin_pos_of_le_one (hd0 : 0 < d) (hd1 : d ≤ 1) : 0 < Real.sin d :=
  Real.sin_pos_of_pos_of_lt_pi hd0 (by linarith [Real.pi_gt_three])

theorem cos_pos_of_le_one (hd0 : 0 < d) (hd1 : d ≤ 1) : 0 < Real.cos d :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩

/-- `sin d ≥ (5/6) d` for `0 < d ≤ 1`. -/
theorem sin_ge_five_sixth (hd0 : 0 < d) (hd1 : d ≤ 1) : 5 / 6 * d ≤ Real.sin d := by
  have h := TaylorBounds.sin_ge hd0.le
  nlinarith [pow_le_one₀ hd0.le hd1 (n := 3), sq_nonneg d]

/-- `Φ₁(d²) ≥ −1`. -/
theorem Phi1_ge (hd0 : 0 < d) : -1 ≤ Barriers.Phi1 (d ^ 2) := by
  have hd2 : (0:ℝ) < d ^ 2 := by positivity
  have hsqrt : Real.sqrt (d ^ 2) = d := Real.sqrt_sq hd0.le
  rw [Barriers.Phi1, hsqrt, le_div_iff₀ hd2]
  nlinarith [TaylorBounds.cos_ge d]

/-- `Φ₁(d²) ≤ −1 + d²/12`. -/
theorem Phi1_le (hd0 : 0 < d) :
    Barriers.Phi1 (d ^ 2) ≤ -1 + d ^ 2 / 12 := by
  have hd2 : (0:ℝ) < d ^ 2 := by positivity
  have hsqrt : Real.sqrt (d ^ 2) = d := Real.sqrt_sq hd0.le
  rw [Barriers.Phi1, hsqrt, div_le_iff₀ hd2]
  nlinarith [TaylorBounds.cos_le hd0.le]

/-- `|Φ₂(d²)| ≤ 1/3` for `0 < d ≤ 1`. -/
theorem abs_Phi2_le (hd0 : 0 < d) (hd1 : d ≤ 1) : |Barriers.Phi2 (d ^ 2)| ≤ 1 / 3 := by
  have hd2 : (0:ℝ) < d ^ 2 := by positivity
  have hsqrt : Real.sqrt (d ^ 2) = d := Real.sqrt_sq hd0.le
  have hsin : 0 < Real.sin d := sin_pos_of_le_one hd0 hd1
  have hcos : 0 < Real.cos d := cos_pos_of_le_one hd0 hd1
  have htan : d < Real.tan d := Real.lt_tan hd0 (by linarith [Real.pi_gt_three])
  have htanpos : 0 < Real.tan d := lt_trans hd0 htan
  have hden : 0 < d ^ 2 * Real.tan d := mul_pos hd2 htanpos
  rw [Barriers.Phi2, hsqrt, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hlow : Real.sin d - d ≤ 0 := by
    have := Real.sin_le hd0.le
    linarith
  have hhigh : -(d ^ 3 / 6) ≤ Real.sin d - d := by
    have := TaylorBounds.sin_ge hd0.le
    linarith
  have habs : |2 * (Real.sin d - d)| ≤ d ^ 3 / 3 := by
    rw [abs_le]
    constructor <;> linarith
  calc |2 * (Real.sin d - d)| ≤ d ^ 3 / 3 := habs
    _ ≤ 1 / 3 * (d ^ 2 * Real.tan d) := by nlinarith

/-- `|Φ₀(d²) + 2/3| ≤ d²/6` for `0 < d ≤ 1`. -/
theorem abs_Phi0_add_le (hd0 : 0 < d) (hd1 : d ≤ 1) :
    |Barriers.Phi0 (d ^ 2) + 2 / 3| ≤ d ^ 2 / 6 := by
  have hd2 : (0:ℝ) < d ^ 2 := by positivity
  have hsqrt : Real.sqrt (d ^ 2) = d := Real.sqrt_sq hd0.le
  have hsin : 0 < Real.sin d := sin_pos_of_le_one hd0 hd1
  have hcos : 0 < Real.cos d := cos_pos_of_le_one hd0 hd1
  have hsinlow : 5 / 6 * d ≤ Real.sin d := sin_ge_five_sixth hd0 hd1
  -- the exact rewriting of the deviation
  have hkey : Barriers.Phi0 (d ^ 2) + 2 / 3
      = 2 * ((d * Real.cos d - Real.sin d) + d ^ 2 * Real.sin d / 3) / (d ^ 2 * Real.sin d) := by
    rw [Barriers.Phi0, hsqrt, Real.tan_eq_sin_div_cos]
    field_simp
  set P : ℝ := (d * Real.cos d - Real.sin d) + d ^ 2 * Real.sin d / 3 with hP
  have hden : 0 < d ^ 2 * Real.sin d := by positivity
  have hdenlow : 5 / 6 * d ^ 3 ≤ d ^ 2 * Real.sin d := by nlinarith
  -- bounds for the numerator
  have hPle : P ≤ 0 := by
    have h1 := TaylorBounds.cos_le hd0.le
    have h2 := TaylorBounds.sin_ge hd0.le
    have h3 := TaylorBounds.sin_le hd0.le
    have hd7 : d ^ 7 ≤ d ^ 5 := by
      have := pow_le_pow_of_le_one hd0.le hd1 (show 5 ≤ 7 by norm_num)
      simpa using this
    nlinarith [sq_nonneg d, pow_pos hd0 3, pow_pos hd0 5]
  have hPge : -(23 / 360 * d ^ 5) ≤ P := by
    have h1 := TaylorBounds.cos_ge d
    have h2 := TaylorBounds.sin_le hd0.le
    have h3 := TaylorBounds.sin_ge hd0.le
    nlinarith [pow_pos hd0 3, pow_pos hd0 5]
  have habsP : |P| ≤ 23 / 360 * d ^ 5 := by
    rw [abs_le]
    exact ⟨hPge, by nlinarith [pow_pos hd0 5]⟩
  rw [hkey, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have h2P : |2 * P| = 2 * |P| := by
    rw [abs_mul]
    norm_num
  rw [h2P]
  calc 2 * |P| ≤ 2 * (23 / 360 * d ^ 5) := by linarith
    _ ≤ d ^ 2 / 6 * (5 / 6 * d ^ 3) := by nlinarith [pow_pos hd0 5]
    _ ≤ d ^ 2 / 6 * (d ^ 2 * Real.sin d) := by nlinarith [pow_pos hd0 2]

end PhiBounds
