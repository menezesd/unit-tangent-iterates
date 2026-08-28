import UnitTangentIterates.Shadowing
import UnitTangentIterates.RearFamilyNumericConditions

/-!
# The drift bound of the rear-family constructor
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real

namespace GaugeRearFamilyFromFront

/-- **The steering drift is uniformly bounded on the closed strip.**

The constructor's `hKxbd`/`hKxnn`/`hKxm` group bounds

    |(K - sin delta) / cos delta ^ 3|

by a time function `Kx t` with a ceiling `kx`.  On the closed strip the bound is
a constant, and an explicit one: the numerator is at most `2 kh` because both
`|K| <= kh` and `0 <= sin delta <= kh` there, and the denominator is at least
`sqrt(1-kh^2)^3` by `Shadowing.cos_ge_of_mem_strip`.  So

    Kx := 2 kh / sqrt (1 - kh^2) ^ 3

works, with `kx` the same constant — no time dependence is needed. -/
theorem abs_drift_le {K delta kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hK : |K| ≤ kh) (hd0 : 0 ≤ delta) (hd1 : delta ≤ Real.arcsin kh) :
    |(K - Real.sin delta) / Real.cos delta ^ 3|
      ≤ 2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3 := by
  have hsq : (0:ℝ) < 1 - kh ^ 2 := by nlinarith
  have hcpos : (0:ℝ) < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr hsq
  have hcos : Real.sqrt (1 - kh ^ 2) ≤ Real.cos delta :=
    Shadowing.cos_ge_of_mem_strip hd0 hd1
  have hcospos : (0:ℝ) < Real.cos delta := lt_of_lt_of_le hcpos hcos
  -- the numerator
  have hsin0 : 0 ≤ Real.sin delta := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi hd0 ?_
    exact le_trans hd1 (le_trans (Real.arcsin_le_pi_div_two kh) (by linarith [Real.pi_pos]))
  have hsin1 : Real.sin delta ≤ kh := by
    have hmono : Real.sin delta ≤ Real.sin (Real.arcsin kh) := by
      refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ (Real.arcsin_le_pi_div_two kh) hd1
      exact le_trans (by linarith [Real.pi_pos]) hd0
    rwa [Real.sin_arcsin (by linarith) hkh1.le] at hmono
  have hnum : |K - Real.sin delta| ≤ 2 * kh := by
    have := abs_le.mp hK
    rw [abs_le]
    constructor <;> linarith
  -- the denominator
  have hden : Real.sqrt (1 - kh ^ 2) ^ 3 ≤ Real.cos delta ^ 3 :=
    pow_le_pow_left₀ hcpos.le hcos 3
  have hden0 : (0:ℝ) < Real.sqrt (1 - kh ^ 2) ^ 3 := by positivity
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.cos delta ^ 3)]
  rw [div_le_div_iff₀ (by positivity) hden0]
  have h2 : (0:ℝ) ≤ 2 * kh := by linarith
  nlinarith [hnum, hden, hden0, abs_nonneg (K - Real.sin delta)]

theorem drift_bound_nonneg {kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    0 ≤ 2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3 := by
  have hsq : (0:ℝ) < 1 - kh ^ 2 := by nlinarith
  have : (0:ℝ) < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr hsq
  positivity

end GaugeRearFamilyFromFront
