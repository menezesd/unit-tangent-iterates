import UnitTangentIterates.WidthUniform

/-!
# A uniform lower bound on the model width

§51 localized the missing floor-free chord estimate: for points far apart in
arclength on the two-cap model of separation `H`, the chord must be bounded
below by the model's **width**, which stays of order one however large `H` is.

`WidthUniform.exists_uniform_width_bound` already gives `0 < width` for each
`H` past a threshold, together with the upper bound `C₀ + 1`.  That positivity
is per-`H` and could in principle degenerate.  This file supplies the companion:
past a threshold the width stays above a *fixed* positive constant.

The mechanism is the one the upper bound uses, run in the other direction: the
model tangent angle converges to the isolated hairpin's at rate `C e^{−βH}`, so
the two width integrals differ by at most `C e^{−βH}·H`, which tends to zero.
`PhaseWidth.abs_width_sub_le` supplies the two-sided comparison; the upper bound
had only needed one side of it.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Filter Topology MeasureTheory intervalIntegral Real

namespace WidthUniform


/-- **A uniform *lower* width bound.**  The companion of
`exists_uniform_width_bound`: past a threshold, the model width stays above a
fixed positive constant, because the error `C e^{−βH}·H` tends to zero. -/
theorem exists_uniform_width_lower {Θ : ℝ → ℝ → ℝ} {Θs : ℝ → ℝ} {c0 C beta : ℝ}
    (hbeta : 0 < beta) (hC : 0 ≤ C) (hc0 : 0 < c0)
    (hΘ : ∀ H, Continuous (Θ H)) (hΘs : Continuous Θs)
    (hmodel : ∀ H, c0 ≤ ∫ t in (-(H / 2))..(H / 2), Real.sin (Θs t))
    (hclose : ∀ H, ∀ t ∈ uIoc (-(H / 2)) (H / 2),
      |Θ H t - Θs t| ≤ C * Real.exp (-beta * H)) :
    ∃ Hstar : ℝ, 0 < Hstar ∧ ∀ H, Hstar ≤ H →
      c0 / 2 ≤ ∫ t in (-(H / 2))..(H / 2), Real.sin (Θ H t) := by
  have hsmall : ∀ᶠ H in atTop, C * Real.exp (-beta * H) * H ≤ c0 / 2 := by
    have h0 : Tendsto (fun x : ℝ => C * ((1 + x) ^ 2 * Real.exp (-beta * x)))
        atTop (𝓝 0) := by
      have := (MainThresholds.tendsto_tail_zero (beta := beta) hbeta).const_mul C
      simpa using this
    have hev := h0.eventually (gt_mem_nhds (by linarith : (0:ℝ) < c0 / 2))
    filter_upwards [hev, eventually_ge_atTop (0:ℝ)] with H hH hH0
    have hexp : 0 < Real.exp (-beta * H) := Real.exp_pos _
    have hle : C * Real.exp (-beta * H) * H
        ≤ C * ((1 + H) ^ 2 * Real.exp (-beta * H)) := by
      have hHle : H ≤ (1 + H) ^ 2 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hHle (mul_nonneg hC hexp.le)
      calc C * Real.exp (-beta * H) * H
          ≤ C * Real.exp (-beta * H) * (1 + H) ^ 2 := hmul
        _ = C * ((1 + H) ^ 2 * Real.exp (-beta * H)) := by ring
    linarith [hH.le]
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro H hH
  have hH1 : (1:ℝ) ≤ H := le_trans (le_max_right _ _) hH
  have hHB : B ≤ H := le_trans (le_max_left _ _) hH
  have hab : -(H / 2) ≤ H / 2 := by linarith
  have habs := PhaseWidth.abs_width_sub_le (Θ := Θ H) (Θs := Θs)
    (ε := C * Real.exp (-beta * H)) (hΘ H) hΘs hab (hclose H)
  have herr : C * Real.exp (-beta * H) * (H / 2 - -(H / 2)) ≤ c0 / 2 := by
    have hEq : H / 2 - -(H / 2) = H := by ring
    rw [hEq]
    exact hB H hHB
  have h1 := (abs_le.mp habs).1
  linarith [hmodel H, h1, herr]

end WidthUniform
