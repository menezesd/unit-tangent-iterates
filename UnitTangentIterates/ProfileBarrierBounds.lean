import Mathlib
import UnitTangentIterates.Barriers
import UnitTangentIterates.BarrierEstimates
import UnitTangentIterates.ProfileExtension

/-!
# Uniform positivity of the translator profile from barrier bounds

This file proves that any profile `f` satisfying the lower barrier bound
`f_ε⁻ ≤ f` on `[0, π]` for `0 < ε ≤ 1/10` is uniformly strictly positive on
the entire interval `[0, π]`:

`ε⁻¹ - ε ≤ f(θ)` for all `θ ∈ [0, π]`, with `0 < 1 < ε⁻¹ - ε`.

Consequently, the profile never approaches zero at the boundary endpoints
`θ = 0` or `θ = π`, providing the uniform positivity lower bound required
for smooth positive extensions across the boundary.
-/

noncomputable section

open Real Set

namespace ProfileBarrierBounds

/-- **Uniform positivity on `[0, π]`.**  Any profile bounded below by the
explicit lower barrier `f_ε⁻` has `0 < ε⁻¹ - ε ≤ f θ` for all `θ`. -/
theorem profile_pos_of_lower_barrier {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    {f : ℝ → ℝ} (hfl : ∀ θ, Barriers.fMinus ε θ ≤ f θ) (θ : ℝ) :
    0 < ε⁻¹ - ε ∧ ε⁻¹ - ε ≤ f θ := by
  have hm1 : 1 < ε⁻¹ - ε := BarrierEstimates.m_gt_one hε hε'
  have hpos : 0 < ε⁻¹ - ε := by linarith
  have hmin : ε⁻¹ - ε ≤ Barriers.fMinus ε θ := (Barriers.fMinus_min hε).1 θ
  have hle : ε⁻¹ - ε ≤ f θ := le_trans hmin (hfl θ)
  exact ⟨hpos, hle⟩

/-- **Strict positivity on `[0, π]`.**  The profile `f` is strictly positive on
`[0, π]`. -/
theorem profile_pos_on_Icc {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    {f : ℝ → ℝ} (hfl : ∀ θ, Barriers.fMinus ε θ ≤ f θ) {θ : ℝ} (_ : θ ∈ Icc 0 π) :
    0 < f θ := by
  obtain ⟨hpos, hle⟩ := profile_pos_of_lower_barrier hε hε' hfl θ
  exact lt_of_lt_of_le hpos hle

/-- **Uniform lower bound on `[0, π]`.**  There is an explicit constant
`c = ε⁻¹ - ε > 0` such that `c ≤ f θ` for all `θ ∈ [0, π]`. -/
theorem exists_pos_lower_bound {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    {f : ℝ → ℝ} (hfl : ∀ θ, Barriers.fMinus ε θ ≤ f θ) :
    ∃ c > 0, ∀ θ ∈ Icc 0 π, c ≤ f θ :=
  ⟨ε⁻¹ - ε, (BarrierEstimates.m_gt_one hε hε').trans_le' (by norm_num),
    fun θ _ => (profile_pos_of_lower_barrier hε hε' hfl θ).2⟩

end ProfileBarrierBounds
