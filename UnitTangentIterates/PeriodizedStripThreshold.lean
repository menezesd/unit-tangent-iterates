import UnitTangentIterates.PaperHairpinConfig
import UnitTangentIterates.FrontPeriodizationPositivity

/-! # Uniform large-period strip certificate -/

namespace PaperHairpinConfig.PeriodizedStripData

/-- A nonnegative exponentially localized pulse with pointwise supremum
strictly below one supplies `PeriodizedStripData` at every sufficiently large
period. -/
theorem exists_threshold
    {y : ℝ → ℝ} {alpha C b : ℝ}
    (halpha : 0 < alpha) (hb1 : b < 1)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) :
    ∃ H0 : ℝ, 0 < H0 ∧ ∀ H ≥ H0,
      PeriodizedStripData y alpha C H b := by
  have hq : ∀ᶠ H : ℝ in Filter.atTop,
      Real.exp (-alpha * H) ≤ 1 / 2 := by
    simpa using FrontPeriodizationPositivity.eventually_const_mul_exp_neg_le
      (A := 1) (c := alpha) (b := 1 / 2) halpha (by norm_num)
  have hover : ∀ᶠ H : ℝ in Filter.atTop,
      4 * C * Real.exp (-(alpha / 2) * H) < 1 - b := by
    have hrate : 0 < alpha / 2 := by linarith
    have ht : Filter.Tendsto
        (fun H : ℝ => (4 * C) * Real.exp (-(alpha / 2) * H))
        Filter.atTop (nhds 0) := by
      have harg : Filter.Tendsto (fun H : ℝ => -(alpha / 2) * H)
          Filter.atTop Filter.atBot :=
        tendsto_const_nhds.neg_mul_atTop
          (show -(alpha / 2) < 0 by linarith) Filter.tendsto_id
      simpa using (Real.tendsto_exp_atBot.comp harg).const_mul (4 * C)
    exact ((tendsto_order.1 ht).2 (1 - b) (by linarith)).mono fun H h => h
  have hev : ∀ᶠ H : ℝ in Filter.atTop,
      0 < H ∧ Real.exp (-alpha * H) ≤ 1 / 2 ∧
        b + 4 * C * Real.exp (-(alpha / 2) * H) < 1 := by
    filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ), hq, hover] with H hH hqH hoH
    exact ⟨hH, hqH, by linarith⟩
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max Q 1, by positivity, ?_⟩
  intro H hH
  obtain ⟨hHp, hqH, hoverH⟩ := hQ H (le_trans (le_max_left Q 1) hH)
  exact
    { alpha_pos := halpha
      period_pos := hHp
      half_overlap := hqH
      nonneg := hy0
      decay := hyb
      pointwise := hsup
      overlap_budget := hoverH }

end PaperHairpinConfig.PeriodizedStripData

