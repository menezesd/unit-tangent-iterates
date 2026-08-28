import Mathlib

/-!
# Scalar term bounds for the fourth pulse derivative

These lemmas isolate the denominator and polynomial estimates used by the
explicit fourth front-arclength pulse formula.  They deliberately do not
import the module containing that formula, so they remain usable while its
assembly proof is revised.
-/

noncomputable section

namespace PulseFourthTermBounds

/-- A square-root times a power of `q ≥ 1` cannot enlarge a quotient. -/
theorem abs_div_sqrt_mul_pow_le_abs {z q : ℝ} (hq : 1 ≤ q) (n : ℕ) :
    |z / (Real.sqrt q * q ^ n)| ≤ |z| := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hs : 1 ≤ Real.sqrt q := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt q := Real.sqrt_le_sqrt hq
  have hp : 1 ≤ q ^ n := one_le_pow₀ hq
  have hden : 1 ≤ Real.sqrt q * q ^ n := by nlinarith
  rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (pow_nonneg hq0 _)]
  rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)]
  nlinarith [abs_nonneg z]

/-- The six polynomial numerators in the fourth pulse expansion, bounded by
the corresponding coefficients after `0 ≤ k ≤ B` and
`|k_j| ≤ D_j k`. -/
theorem pulseFourth_numerator_bounds
    {k k1 k2 k3 k4 B D1 D2 D3 D4 : ℝ}
    (hk0 : 0 ≤ k) (hkB : k ≤ B) (hB : 0 ≤ B)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3) (hD4 : 0 ≤ D4)
    (h1 : |k1| ≤ D1 * k) (h2 : |k2| ≤ D2 * k)
    (h3 : |k3| ≤ D3 * k) (h4 : |k4| ≤ D4 * k) :
    |k4| ≤ D4 * k ∧
    |6 * k * k1 * k3| ≤ 6 * B ^ 2 * D1 * D3 * k ∧
    |25 * k1 ^ 2 * k2 + 13 * k * k2 ^ 2 + 13 * k * k1 * k3| ≤
      (25 * B ^ 2 * D1 ^ 2 * D2 + 13 * B ^ 2 * D2 ^ 2 +
        13 * B ^ 2 * D1 * D3) * k ∧
    |8 * k * k1 * (13 * k * k1 * k2 + 4 * k1 ^ 3)| ≤
      (104 * B ^ 4 * D1 ^ 2 * D2 + 32 * B ^ 4 * D1 ^ 4) * k ∧
    |56 * k * k1 ^ 4 + 84 * k ^ 2 * k1 ^ 2 * k2| ≤
      (56 * B ^ 4 * D1 ^ 4 + 84 * B ^ 4 * D1 ^ 2 * D2) * k ∧
    |280 * k ^ 3 * k1 ^ 4| ≤ 280 * B ^ 6 * D1 ^ 4 * k := by
  have hkabs : |k| = k := abs_of_nonneg hk0
  have hk2 : k ^ 2 ≤ B ^ 2 := by nlinarith
  have hk4 : k ^ 4 ≤ B ^ 4 := by nlinarith [sq_nonneg (k ^ 2), sq_nonneg (B ^ 2)]
  have hk3 : k ^ 3 ≤ B ^ 2 * k := by
    calc
      k ^ 3 = k ^ 2 * k := by ring
      _ ≤ B ^ 2 * k := mul_le_mul_of_nonneg_right hk2 hk0
  have hk5 : k ^ 5 ≤ B ^ 4 * k := by
    calc
      k ^ 5 = k ^ 4 * k := by ring
      _ ≤ B ^ 4 * k := mul_le_mul_of_nonneg_right hk4 hk0
  have hk6 : k ^ 6 ≤ B ^ 6 := by
    calc
      k ^ 6 = k ^ 4 * k ^ 2 := by ring
      _ ≤ B ^ 4 * B ^ 2 :=
        mul_le_mul hk4 hk2 (sq_nonneg k) (pow_nonneg hB 4)
      _ = B ^ 6 := by ring
  have hk7 : k ^ 7 ≤ B ^ 6 * k := by
    calc
      k ^ 7 = k ^ 6 * k := by ring
      _ ≤ B ^ 6 * k := mul_le_mul_of_nonneg_right hk6 hk0
  refine ⟨h4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6), hkabs]
    calc
      6 * k * |k1| * |k3| ≤ 6 * k * (D1 * k) * (D3 * k) := by gcongr
      _ = (6 * D1 * D3) * k ^ 3 := by ring
      _ ≤ (6 * D1 * D3) * (B ^ 2 * k) :=
        mul_le_mul_of_nonneg_left hk3 (by positivity)
      _ = 6 * B ^ 2 * D1 * D3 * k := by ring
  · calc
      |25 * k1 ^ 2 * k2 + 13 * k * k2 ^ 2 + 13 * k * k1 * k3| ≤
          |25 * k1 ^ 2 * k2| + |13 * k * k2 ^ 2| +
          |13 * k * k1 * k3| := by
        calc
          |25 * k1 ^ 2 * k2 + 13 * k * k2 ^ 2 + 13 * k * k1 * k3| ≤
              |25 * k1 ^ 2 * k2 + 13 * k * k2 ^ 2| + |13 * k * k1 * k3| :=
            abs_add_le _ _
          _ ≤ (|25 * k1 ^ 2 * k2| + |13 * k * k2 ^ 2|) +
              |13 * k * k1 * k3| := by
            gcongr
            exact abs_add_le _ _
      _ ≤ _ := by
        have ha : 25 * |k1| ^ 2 * |k2| ≤ 25 * D1 ^ 2 * D2 * (B ^ 2 * k) := by
          calc
            25 * |k1| ^ 2 * |k2| ≤ 25 * (D1 * k) ^ 2 * (D2 * k) := by gcongr
            _ = (25 * D1 ^ 2 * D2) * k ^ 3 := by ring
            _ ≤ (25 * D1 ^ 2 * D2) * (B ^ 2 * k) :=
              mul_le_mul_of_nonneg_left hk3 (by positivity)
        have hb : 13 * k * |k2| ^ 2 ≤ 13 * D2 ^ 2 * (B ^ 2 * k) := by
          calc
            13 * k * |k2| ^ 2 ≤ 13 * k * (D2 * k) ^ 2 := by gcongr
            _ = (13 * D2 ^ 2) * k ^ 3 := by ring
            _ ≤ (13 * D2 ^ 2) * (B ^ 2 * k) :=
              mul_le_mul_of_nonneg_left hk3 (by positivity)
        have hc : 13 * k * |k1| * |k3| ≤ 13 * D1 * D3 * (B ^ 2 * k) := by
          calc
            13 * k * |k1| * |k3| ≤ 13 * k * (D1 * k) * (D3 * k) := by gcongr
            _ = (13 * D1 * D3) * k ^ 3 := by ring
            _ ≤ (13 * D1 * D3) * (B ^ 2 * k) :=
              mul_le_mul_of_nonneg_left hk3 (by positivity)
        simp only [abs_mul, abs_pow, abs_of_nonneg hk0,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 25),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 13)]
        linarith
  · have ha : |13 * k * k1 * k2| ≤ 13 * D1 * D2 * k ^ 3 := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 13), hkabs]
      calc
        13 * k * |k1| * |k2| ≤ 13 * k * (D1 * k) * (D2 * k) := by gcongr
        _ = 13 * D1 * D2 * k ^ 3 := by ring
    have hb : |4 * k1 ^ 3| ≤ 4 * D1 ^ 3 * k ^ 3 := by
      simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      calc
        4 * |k1| ^ 3 ≤ 4 * (D1 * k) ^ 3 := by gcongr
        _ = 4 * D1 ^ 3 * k ^ 3 := by ring
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8), hkabs]
    calc
      8 * k * |k1| * |13 * k * k1 * k2 + 4 * k1 ^ 3| ≤
          8 * k * |k1| * (|13 * k * k1 * k2| + |4 * k1 ^ 3|) := by
        gcongr
        exact abs_add_le _ _
      _ ≤ 8 * k * (D1 * k) *
          (13 * D1 * D2 * k ^ 3 + 4 * D1 ^ 3 * k ^ 3) := by gcongr
      _ = (104 * D1 ^ 2 * D2 + 32 * D1 ^ 4) * k ^ 5 := by ring
      _ ≤ (104 * D1 ^ 2 * D2 + 32 * D1 ^ 4) * (B ^ 4 * k) :=
        mul_le_mul_of_nonneg_left hk5 (by positivity)
      _ = (104 * B ^ 4 * D1 ^ 2 * D2 + 32 * B ^ 4 * D1 ^ 4) * k := by ring
  · calc
      |_ + _| ≤ |56 * k * k1 ^ 4| + |84 * k ^ 2 * k1 ^ 2 * k2| := abs_add_le _ _
      _ ≤ _ := by
        have ha : 56 * k * |k1| ^ 4 ≤ 56 * D1 ^ 4 * (B ^ 4 * k) := by
          calc
            56 * k * |k1| ^ 4 ≤ 56 * k * (D1 * k) ^ 4 := by gcongr
            _ = (56 * D1 ^ 4) * k ^ 5 := by ring
            _ ≤ (56 * D1 ^ 4) * (B ^ 4 * k) :=
              mul_le_mul_of_nonneg_left hk5 (by positivity)
        have hb : 84 * k ^ 2 * |k1| ^ 2 * |k2| ≤
            84 * D1 ^ 2 * D2 * (B ^ 4 * k) := by
          calc
            84 * k ^ 2 * |k1| ^ 2 * |k2| ≤
                84 * k ^ 2 * (D1 * k) ^ 2 * (D2 * k) := by gcongr
            _ = (84 * D1 ^ 2 * D2) * k ^ 5 := by ring
            _ ≤ (84 * D1 ^ 2 * D2) * (B ^ 4 * k) :=
              mul_le_mul_of_nonneg_left hk5 (by positivity)
        simp only [abs_mul, abs_pow, abs_of_nonneg hk0,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 56),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 84)]
        linarith
  · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 280),
      abs_pow, hkabs, abs_pow]
    calc
      280 * k ^ 3 * |k1| ^ 4 ≤ 280 * k ^ 3 * (D1 * k) ^ 4 := by gcongr
      _ = (280 * D1 ^ 4) * k ^ 7 := by ring
      _ ≤ (280 * D1 ^ 4) * (B ^ 6 * k) :=
        mul_le_mul_of_nonneg_left hk7 (by positivity)
      _ = 280 * B ^ 6 * D1 ^ 4 * k := by ring

end PulseFourthTermBounds
