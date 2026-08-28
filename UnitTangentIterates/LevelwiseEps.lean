import UnitTangentIterates.HairpinRelativeDerivatives
import UnitTangentIterates.OrbitBudgetSharp

/-!
# A levelwise choice of `ε` meeting the backward-orbit ceiling threshold
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real HairpinRelative

namespace LevelwiseEps

/-- **The curvature ceiling of a hairpin profile is the reciprocal of its lower
barrier.**  `curvField f t = sin t / f t`, so the barrier `m ≤ f` caps the
curvature at `1/m`. -/
theorem curvField_le_of_barrier {f : ℝ → ℝ} {m t : ℝ} (hm : 0 < m)
    (hlow : m ≤ f t) : curvField f t ≤ 1 / m := by
  have hft : 0 < f t := lt_of_lt_of_le hm hlow
  have hsin : Real.sin t ≤ 1 := Real.sin_le_one t
  calc curvField f t = Real.sin t / f t := rfl
    _ ≤ 1 / f t := div_le_div_of_nonneg_right hsin hft.le
    _ ≤ 1 / m := one_div_le_one_div_of_le hm hlow

/-- The barrier `m = ε⁻¹ − ε` has reciprocal `ε/(1−ε²)`. -/
theorem one_div_barrier {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    1 / (1 / e - e) = e / (1 - e ^ 2) := by
  have h1 : (1:ℝ) - e ^ 2 ≠ 0 := by nlinarith
  have h2 : 1 / e - e = (1 - e ^ 2) / e := by field_simp
  rw [h2, one_div_div]

/-- **The levelwise choice.**  At level `m` take
`ε = min (1/10) (1/(2√(m+1)))`. -/
def levelEps (m : ℕ) : ℝ := min (1 / 10) (1 / (2 * Real.sqrt (m + 1)))

theorem levelEps_pos (m : ℕ) : 0 < levelEps m := by
  have hs : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  exact lt_min (by norm_num) (by positivity)

theorem levelEps_le_ten (m : ℕ) : levelEps m ≤ 1 / 10 := min_le_left _ _

/-- **The levelwise choice meets the threshold of `OrbitCeiling.ceiling_lt_of_steps`.**
The ceiling of the level-`m` model is `1/(ε⁻¹−ε)`, and with this `ε` it lies
strictly below `1/√(m+1)` — the exact bound the backward orbit requires of a
model that must admit `m` steps. -/
theorem levelEps_ceiling_lt (m : ℕ) :
    1 / (1 / levelEps m - levelEps m) < 1 / Real.sqrt ((m : ℝ) + 1) := by
  set e : ℝ := levelEps m with hedef
  have hepos : 0 < e := levelEps_pos m
  have he10 : e ≤ 1 / 10 := levelEps_le_ten m
  have he1 : e < 1 := by linarith
  have hs : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hehalf : e ≤ 1 / (2 * Real.sqrt ((m : ℝ) + 1)) := min_le_right _ _
  rw [one_div_barrier hepos he1]
  -- `1 - e² ≥ 99/100`
  have hsq : e ^ 2 ≤ 1 / 100 := by nlinarith
  have hden : (99:ℝ) / 100 ≤ 1 - e ^ 2 := by linarith
  have hdenpos : (0:ℝ) < 1 - e ^ 2 := by linarith
  -- `e/(1-e²) ≤ e · 100/99`
  have hstep1 : e / (1 - e ^ 2) ≤ e * (100 / 99) := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [hepos.le, hden]
  -- `e · 100/99 ≤ 50/(99 √(m+1)) < 1/√(m+1)`
  have hstep2 : e * (100 / 99) ≤ (1 / (2 * Real.sqrt ((m : ℝ) + 1))) * (100 / 99) :=
    mul_le_mul_of_nonneg_right hehalf (by norm_num)
  have hstep3 : (1 / (2 * Real.sqrt ((m : ℝ) + 1))) * (100 / 99)
      < 1 / Real.sqrt ((m : ℝ) + 1) := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by positivity) hs]
    nlinarith [hs]
  linarith

end LevelwiseEps
