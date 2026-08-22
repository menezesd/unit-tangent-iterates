import Mathlib
import UnitTangentIterates.PerimeterValueProduced
import UnitTangentIterates.PeriodizationSup

/-!
# The value clause holds for a genuine pulse

`PerimeterValueProduced.abs_defect_sub_delta_le_pulse_full` asks of the pulse
only that it be continuous, nonnegative, exponentially localized and that its
periodization stay below `a < 1`.  This file checks all of that for the
**nondegenerate** pulse

```
  y(x) = ¼ e^{-|x|} ,      period H = 8,   α = 1,  a = ½,  β' = ¼,
```

whose periodization is bounded by `¼ + e^{-4} < ½` — the cell bound coming from
the periodization error of `UnitTangentIterates/Periodization.lean` together with the
periodicity of the periodized profile, which reduces an arbitrary point to the
centred cell.

The conclusion obtained is an explicit exponentially small bound for the
difference between the perimeter defect of the periodized profile and the
defect `Δ = ∫_ℝ Φ(y)` of the isolated pulse.
-/

noncomputable section

open Real Set MeasureTheory

namespace PerimeterValueProducedInstance

open PerimeterAsymptotics

/-- The exponential pulse `y(x) = ¼e^{-|x|}`. -/
def pulse (x : ℝ) : ℝ := (1 / 4) * Real.exp (-|x|)

theorem pulse_continuous : Continuous pulse := by
  unfold pulse
  fun_prop

theorem pulse_nonneg (x : ℝ) : 0 ≤ pulse x := by
  unfold pulse; positivity

theorem pulse_bound (x : ℝ) : pulse x ≤ (1 / 4) * Real.exp (-(1 : ℝ) * |x|) := by
  unfold pulse
  rw [neg_mul, one_mul]

theorem pulse_le_quarter (x : ℝ) : pulse x ≤ 1 / 4 := by
  unfold pulse
  have h : Real.exp (-|x|) ≤ 1 := Real.exp_le_one_iff.mpr (by simp [abs_nonneg])
  nlinarith

/-! ### Numerical facts -/

theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem exp_neg_one_le_half : Real.exp (-(1 : ℝ)) ≤ 1 / 2 := by
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  rw [Real.exp_neg 1, inv_le_iff_one_le_mul₀ hpos]
  linarith [two_le_exp_one]

theorem exp_neg_four_le : Real.exp (-(4 : ℝ)) ≤ 1 / 16 := by
  have hrw : Real.exp (-(4 : ℝ)) = Real.exp (-(1 : ℝ)) ^ (4 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hrw]
  have h1 : (0 : ℝ) ≤ Real.exp (-(1 : ℝ)) := (Real.exp_pos _).le
  calc Real.exp (-(1 : ℝ)) ^ (4 : ℕ) ≤ (1 / 2 : ℝ) ^ (4 : ℕ) :=
        pow_le_pow_left₀ h1 exp_neg_one_le_half 4
    _ = 1 / 16 := by norm_num

theorem exp_neg_eight_le_half : Real.exp (-(1 : ℝ) * (8 : ℝ)) ≤ 1 / 2 := by
  refine le_trans (Real.exp_le_exp.mpr (by norm_num)) exp_neg_one_le_half

/-! ### The periodization of the pulse stays below `½` -/

/-- **The periodization of the pulse stays below `½`** at every point: the
periodization error on the centred cell plus the periodicity of the periodized
profile. -/
theorem periodization_le (u : ℝ) : (∑' m : ℤ, pulse (u - m * 8)) ≤ 1 / 2 := by
  have h := PeriodizationSup.periodization_le_of_sup (y := pulse) (C := 1 / 4) (alpha := 1)
    (P := 8) (b := 1 / 4) (by norm_num) (by norm_num)
    (by simpa using exp_neg_eight_le_half) pulse_nonneg pulse_bound pulse_le_quarter u
  have hrw : 4 * (1 / 4 : ℝ) * Real.exp (-((1 : ℝ) / 2) * (8 : ℝ)) = Real.exp (-(4 : ℝ)) := by
    norm_num
  rw [hrw] at h
  have h3 := exp_neg_four_le
  linarith

/-! ### The value clause for this pulse -/

/-- **The value clause of the two-cap asymptotics, for the exponential pulse
`¼e^{-|x|}` of period `8`.**  Every hypothesis is verified: the defect of the
periodized profile differs from `Δ = ∫_ℝ Φ(y)` by at most an explicit multiple
of `e^{-2}`. -/
theorem exponential_pulse_instance :
    |((8 : ℝ) - ∫ s in (0:ℝ)..(8:ℝ),
        Real.sqrt (1 - (∑' m : ℤ, pulse (s - m * 8)) ^ 2)) - ∫ s : ℝ, Phi (pulse s)|
      ≤ ((1 / 2) / Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) * (4 * (1 / 4))
            / ((1 / 2 - 1 / 4) * Real.exp 1) + 2 * (1 / 4 : ℝ) ^ 2 / 1)
          * Real.exp (-(1 / 4) * (8 : ℝ)) :=
  PerimeterValueProduced.abs_defect_sub_delta_le_pulse_full
    (y := pulse) (C := 1 / 4) (a := 1 / 2) (alpha := 1) (H := 8) (beta' := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) exp_neg_eight_le_half
    pulse_continuous pulse_nonneg pulse_bound (by norm_num) (by norm_num) periodization_le

end PerimeterValueProducedInstance
