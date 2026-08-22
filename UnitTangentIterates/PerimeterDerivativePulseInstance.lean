import Mathlib
import UnitTangentIterates.PerimeterLeibnizProduced
import UnitTangentIterates.PeriodizationSup

/-!
# The derivative clause holds for a genuine smooth pulse

`PerimeterLeibnizProduced.hasDerivAt_perimeter_of_pulse_leibniz` asks of the
pulse that it be nonnegative, differentiable with a continuous derivative, that
both it and its derivative be exponentially localized, and that all its
periodizations of period above `H₀/2` stay below `a < 1`.  This file checks all
of that for the **nondegenerate smooth** pulse

```
  y(x) = ⅛ sech x = ⅛ / cosh x ,     period H₀ = 8,  α = 1,  a = ½,  β' = ¼,
```

using `cosh x ≥ ½e^{|x|}` and `|sinh x| ≤ cosh x` for the two decay bounds and
the sup bound of `UnitTangentIterates/PeriodizationSup.lean` for the periodizations.

Main result: `sech_pulse_derivative_instance`, an explicit bound
`|P'(8) - 1| ≤ (25/16 + …)e^{-2}` for the rear half-perimeter of this
configuration.
-/

noncomputable section

open Real Set MeasureTheory

namespace PerimeterDerivativePulseInstance

open PerimeterAsymptotics

/-- The smooth pulse `y(x) = ⅛ sech x`. -/
def sechPulse (x : ℝ) : ℝ := (1 / 8) / Real.cosh x

/-- Its derivative. -/
def sechPulse' (x : ℝ) : ℝ := (0 * Real.cosh x - (1 / 8) * Real.sinh x) / Real.cosh x ^ 2

theorem cosh_ne_zero (x : ℝ) : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)

theorem hasDerivAt_sechPulse (x : ℝ) : HasDerivAt sechPulse (sechPulse' x) x :=
  (hasDerivAt_const x (1 / 8 : ℝ)).div (Real.hasDerivAt_cosh x) (cosh_ne_zero x)

theorem continuous_sechPulse' : Continuous sechPulse' := by
  unfold sechPulse'
  exact ((continuous_const.mul Real.continuous_cosh).sub
    (continuous_const.mul Real.continuous_sinh)).div
    (Real.continuous_cosh.pow 2) (fun x => pow_ne_zero 2 (cosh_ne_zero x))

theorem sechPulse_nonneg (x : ℝ) : 0 ≤ sechPulse x := by
  unfold sechPulse
  positivity

/-- `cosh x ≥ ½e^{|x|}`. -/
theorem half_exp_abs_le_cosh (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    have : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
    linarith
  · rw [h]
    have : (0 : ℝ) < Real.exp x := Real.exp_pos _
    linarith

theorem sechPulse_bound (x : ℝ) : sechPulse x ≤ (1 / 4) * Real.exp (-(1 : ℝ) * |x|) := by
  unfold sechPulse
  have hpos : 0 < Real.cosh x := Real.cosh_pos x
  have hlow := half_exp_abs_le_cosh x
  have hexp : (0 : ℝ) < Real.exp |x| := Real.exp_pos _
  rw [div_le_iff₀ hpos, neg_mul, one_mul, Real.exp_neg]
  have hinv : (0 : ℝ) < (Real.exp |x|)⁻¹ := by positivity
  have hkey : (Real.exp |x|)⁻¹ * Real.exp |x| = 1 := inv_mul_cancel₀ (ne_of_gt hexp)
  nlinarith [mul_le_mul_of_nonneg_left hlow hinv.le]

theorem sechPulse_le_eighth (x : ℝ) : sechPulse x ≤ 1 / 8 := by
  unfold sechPulse
  have h1 : (1 : ℝ) ≤ Real.cosh x := Real.one_le_cosh x
  rw [div_le_iff₀ (Real.cosh_pos x)]
  nlinarith

theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  have h := Real.cosh_sq_sub_sinh_sq x
  have hpos : 0 < Real.cosh x := Real.cosh_pos x
  have habs : Real.sinh x ^ 2 = |Real.sinh x| ^ 2 := (sq_abs _).symm
  nlinarith [abs_nonneg (Real.sinh x)]

theorem sechPulse'_bound (x : ℝ) : |sechPulse' x| ≤ (1 / 4) * Real.exp (-(1 : ℝ) * |x|) := by
  have hpos : 0 < Real.cosh x := Real.cosh_pos x
  have hsq : 0 < Real.cosh x ^ 2 := by positivity
  have habs := abs_sinh_le_cosh x
  have hstep : |sechPulse' x| ≤ (1 / 8) / Real.cosh x := by
    unfold sechPulse'
    rw [abs_div, abs_of_pos hsq]
    rw [div_le_div_iff₀ hsq hpos]
    have h1 : |0 * Real.cosh x - (1 / 8) * Real.sinh x| = (1 / 8) * |Real.sinh x| := by
      rw [zero_mul, zero_sub, abs_neg, abs_mul]
      norm_num
    rw [h1]
    nlinarith
  exact le_trans hstep (sechPulse_bound x)

/-! ### Numerical facts -/

theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem exp_neg_one_le_half : Real.exp (-(1 : ℝ)) ≤ 1 / 2 := by
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  rw [Real.exp_neg 1, inv_le_iff_one_le_mul₀ hpos]
  linarith [two_le_exp_one]

theorem exp_neg_two_le : Real.exp (-(2 : ℝ)) ≤ 1 / 4 := by
  have hrw : Real.exp (-(2 : ℝ)) = Real.exp (-(1 : ℝ)) ^ (2 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hrw]
  calc Real.exp (-(1 : ℝ)) ^ (2 : ℕ) ≤ (1 / 2 : ℝ) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_one_le_half 2
    _ = 1 / 4 := by norm_num

/-! ### The periodizations stay below `½` -/

/-- **Every periodization of period above `4` stays below `½`.** -/
theorem periodization_le (Q : ℝ) (hQ : (8 : ℝ) / 2 < Q) (v : ℝ) :
    |∑' m : ℤ, sechPulse (v - m * Q)| ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hq : Real.exp (-(1 : ℝ) * Q) ≤ 1 / 2 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_one_le_half
    nlinarith
  have h := PeriodizationSup.periodization_le_of_sup (y := sechPulse) (C := 1 / 4) (alpha := 1)
    (P := Q) (b := 1 / 8) (by norm_num) hQ0 hq sechPulse_nonneg sechPulse_bound
    sechPulse_le_eighth v
  have hexp : Real.exp (-((1 : ℝ) / 2) * Q) ≤ Real.exp (-(2 : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 := exp_neg_two_le
  have hY0 : 0 ≤ ∑' m : ℤ, sechPulse (v - m * Q) := tsum_nonneg fun _ => sechPulse_nonneg _
  rw [abs_of_nonneg hY0]
  have : 4 * (1 / 4 : ℝ) * Real.exp (-((1 : ℝ) / 2) * Q) ≤ 1 / 4 := by
    have := le_trans hexp h2
    linarith
  linarith

/-! ### The derivative clause for this pulse -/

/-- The rear half-perimeter of the configuration, defined by the defect
identity. -/
def perim (H : ℝ) : ℝ := H - ∫ u in (-(H / 2))..(H / 2),
  Phi (∑' m : ℤ, sechPulse (u - m * H))

/-- **`P'(8) = 1 + O(e^{-2})` for the smooth pulse `⅛ sech`.**  Every
hypothesis of the produced derivative clause is verified for a nondegenerate
pulse. -/
theorem sech_pulse_derivative_instance :
    ∃ p : ℝ, HasDerivAt perim p 8 ∧
      |p - 1| ≤ (25 * (1 / 4 : ℝ) ^ 2
        + (1 / 2) / Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) * (8 * (1 / 4))
            / ((1 / 2 - 1 / 4) * Real.exp 1)) * Real.exp (-(1 / 4) * (8 : ℝ)) := by
  have hthr : Real.exp (-(1 : ℝ) * ((8 : ℝ) / 2)) ≤ 1 / 2 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_one_le_half
    norm_num
  exact PerimeterLeibnizProduced.hasDerivAt_perimeter_of_pulse_leibniz
    (y := sechPulse) (yp := sechPulse') (C := 1 / 4) (a := 1 / 2) (alpha := 1) (H0 := 8)
    (beta' := 1 / 4) (P := perim)
    (by norm_num) (by norm_num) (by norm_num) hthr
    hasDerivAt_sechPulse continuous_sechPulse' sechPulse_nonneg
    (fun x => by rw [abs_of_nonneg (sechPulse_nonneg x)]; exact sechPulse_bound x)
    sechPulse'_bound (by norm_num) (by norm_num) periodization_le
    (fun H => by unfold perim; ring)

end PerimeterDerivativePulseInstance
