import Mathlib
import UnitTangentIterates.PhaseWidth
import UnitTangentIterates.MainThresholds

/-!
# The uniform transverse width

The lemma *Uniform transverse width* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* states that the transverse displacement

`W_H = ∫_{-H/2}^{H/2} sin Θ_H(s) ds`

of the front over the centred half-period satisfies `0 < W_H ≤ C` for all
sufficiently large `H`.  The proof compares `Θ_H` with the tangent angle `Θ_*`
of the isolated translated hairpin, for which
`‖Θ_H − Θ_*‖_{L^∞(I_H)} ≤ Ce^{-βH}`, so that

`W_H ≤ ∫_{I_H} sin Θ_* + H‖Θ_H − Θ_*‖_∞ ≤ ∫_ℝ sin Θ_* + 1`

for large `H`, the last step because `He^{-βH} → 0`.

`UnitTangentIterates/PhaseWidth.lean` contains the two comparison steps
(`width_le`, `width_pos`).  This file assembles them into the statement of the
lemma.

Main result: `exists_uniform_width_bound`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory

namespace WidthUniform

/-- **Uniform transverse width.**  Let `Θ_H` be the front tangent angle on the
centred cell, `Θ_*` the tangent angle of the isolated model, `C₀` a bound for
the model's cell integral, and suppose
`‖Θ_H − Θ_*‖_{L^∞(I_H)} ≤ Ce^{-βH}` and that `Θ_H` stays in `(0, π)` on the
open cell.  Then there is a threshold past which

`0 < W_H ≤ C₀ + 1`.

In particular the transverse width stays bounded while the perimeter `2H`
grows — the input of the closing argument. -/
theorem exists_uniform_width_bound {Θ : ℝ → ℝ → ℝ} {Θs : ℝ → ℝ} {C0 C beta : ℝ}
    (hbeta : 0 < beta) (hC : 0 ≤ C)
    (hΘ : ∀ H, Continuous (Θ H)) (hΘs : Continuous Θs)
    (hmodel : ∀ H, (∫ t in (-(H/2))..(H/2), Real.sin (Θs t)) ≤ C0)
    (hclose : ∀ H, ∀ t ∈ uIoc (-(H/2)) (H/2), |Θ H t - Θs t| ≤ C * Real.exp (-beta * H))
    (hpos : ∀ H, ∀ t ∈ Ioo (-(H/2)) (H/2), Θ H t ∈ Ioo 0 π) :
    ∃ Hstar : ℝ, 0 < Hstar ∧ ∀ H, Hstar ≤ H →
      0 < (∫ t in (-(H/2))..(H/2), Real.sin (Θ H t)) ∧
        (∫ t in (-(H/2))..(H/2), Real.sin (Θ H t)) ≤ C0 + 1 := by
  -- the error term `C e^{-βH} · H` tends to zero
  have hsmall : ∀ᶠ H in atTop, C * Real.exp (-beta * H) * H ≤ 1 := by
    have h0 : Tendsto (fun x : ℝ => C * ((1 + x) ^ 2 * Real.exp (-beta * x))) atTop (𝓝 0) := by
      have := (MainThresholds.tendsto_tail_zero (beta := beta) hbeta).const_mul C
      simpa using this
    have hev := h0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
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
  have hab : -(H/2) ≤ H/2 := by linarith
  constructor
  · exact PhaseWidth.width_pos (Θ := Θ H) (hΘ H) (by linarith) (hpos H)
  · have hle := PhaseWidth.width_le (Θ := Θ H) (Θs := Θs)
      (ε := C * Real.exp (-beta * H)) (hΘ H) hΘs hab (hclose H)
    have herr : C * Real.exp (-beta * H) * (H/2 - -(H/2)) ≤ 1 := by
      have : H/2 - -(H/2) = H := by ring
      rw [this]
      exact hB H hHB
    linarith [hmodel H]

end WidthUniform
