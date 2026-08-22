import Mathlib
import UnitTangentIterates.AngleClose
import UnitTangentIterates.WidthUniform

/-!
# The uniform transverse width, with the angle comparison produced

`WidthUniform.exists_uniform_width_bound` states the lemma *Uniform transverse
width* of *A Noncircular Oval with Convex Unit-Tangent Iterates* with the
comparison `‖Θ_H − Θ_*‖_{L^∞(I_H)} ≤ Ce^{−βH}` carried as a hypothesis.
`AngleClose.angle_sup_close` now produces that comparison from the front
periodization error and the omitted mass.  This file combines the two.

* `exists_uniform_width_bound_of_large` : the width bound with all its
  hypotheses required only past a threshold (the form the produced comparison
  comes in);
* `exists_uniform_width_bound_of_pulse` : **the lemma with the comparison
  produced** — the only inputs are the exponential decay of the isolated pulse
  `y` and of its derivative, the relation `K_* = y + G(y)y'`, the periodization
  bound `Y_H ≤ a < 1`, and the geometric data of the front (its tangent angle
  is a primitive of the periodized curvature with the common origin, stays in
  `(0,π)` on the open cell, and the model's cell integral is bounded).
-/

noncomputable section

open MeasureTheory Set Real Filter Topology

namespace WidthUniformProduced

open FrontPeriodization AngleClose

/-- **Uniform transverse width, past a threshold.**  This is
`WidthUniform.exists_uniform_width_bound` with every hypothesis on the
configuration required only for `H ≥ H₁`. -/
theorem exists_uniform_width_bound_of_large {Θ : ℝ → ℝ → ℝ} {Θs : ℝ → ℝ}
    {C0 C beta H1 : ℝ}
    (hbeta : 0 < beta) (hC : 0 ≤ C) (hH1 : 0 < H1)
    (hΘ : ∀ H, H1 ≤ H → Continuous (Θ H)) (hΘs : Continuous Θs)
    (hmodel : ∀ H, H1 ≤ H → (∫ t in (-(H / 2))..(H / 2), Real.sin (Θs t)) ≤ C0)
    (hclose : ∀ H, H1 ≤ H → ∀ t ∈ uIoc (-(H / 2)) (H / 2),
      |Θ H t - Θs t| ≤ C * Real.exp (-beta * H))
    (hpos : ∀ H, H1 ≤ H → ∀ t ∈ Ioo (-(H / 2)) (H / 2), Θ H t ∈ Ioo 0 π) :
    ∃ Hstar : ℝ, 0 < Hstar ∧ ∀ H, Hstar ≤ H →
      0 < (∫ t in (-(H / 2))..(H / 2), Real.sin (Θ H t)) ∧
        (∫ t in (-(H / 2))..(H / 2), Real.sin (Θ H t)) ≤ C0 + 1 := by
  -- the error term `C e^{−βH} · H` tends to zero
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
  refine ⟨max (max B 1) H1, lt_of_lt_of_le zero_lt_one
    (le_trans (le_max_right _ _) (le_max_left _ _)), ?_⟩
  intro H hH
  have hH1' : H1 ≤ H := le_trans (le_max_right _ _) hH
  have hH1c : (1:ℝ) ≤ H := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hH
  have hHB : B ≤ H := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hH
  have hab : -(H / 2) ≤ H / 2 := by linarith
  refine ⟨PhaseWidth.width_pos (Θ := Θ H) (hΘ H hH1') (by linarith) (hpos H hH1'), ?_⟩
  have hle := PhaseWidth.width_le (Θ := Θ H) (Θs := Θs)
    (ε := C * Real.exp (-beta * H)) (hΘ H hH1') hΘs hab (hclose H hH1')
  have herr : C * Real.exp (-beta * H) * (H / 2 - -(H / 2)) ≤ 1 := by
    have hrw : H / 2 - -(H / 2) = H := by ring
    rw [hrw]
    exact hB H hHB
  linarith [hmodel H hH1']

/-- **Uniform transverse width, with the angle comparison produced.**  For the
isolated pulse `y` with `0 ≤ y ≤ Ce^{−α|·|}` and `|y'| ≤ Dy`, whose
`H`-periodization stays below `a < 1`, the tangent angle `Θ_H` of the
periodized front (a primitive of `K_H = Y_H + G(Y_H)Y_H'` with the origin of
the isolated angle `Θ_*`) satisfies, past a threshold,

`0 < W_H ≤ C₀ + 1`,   `W_H = ∫_{−H/2}^{H/2} sin Θ_H`,

so the transverse width stays bounded while the perimeter `2H` grows.  The
angle comparison `‖Θ_H − Θ_*‖_∞ ≤ Ce^{−βH}` is no longer assumed: it is
produced by `AngleClose.angle_sup_close`. -/
theorem exists_uniform_width_bound_of_pulse
    {y yp Kstar Ths : ℝ → ℝ} {Θ KH : ℝ → ℝ → ℝ}
    {C CK D a alpha beta C0 H1 : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hba : beta < alpha / 2)
    (hy : Continuous y) (hyp : Continuous yp)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hD : 0 ≤ D) (hypb : ∀ s, |yp s| ≤ D * y s)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hKstar : ∀ s, Kstar s = y s + G (y s) * yp s)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|))
    (hThs : ∀ t, HasDerivAt Ths (Kstar t) t)
    (hH1 : 0 < H1)
    (hYa : ∀ H, H1 ≤ H → ∀ u, (∑' m : ℤ, y (u - m * H)) ≤ a)
    (hKH : ∀ H, H1 ≤ H → ∀ t, KH H t = (∑' m : ℤ, y (t - m * H))
      + G (∑' m : ℤ, y (t - m * H)) * (∑' m : ℤ, yp (t - m * H)))
    (hderiv : ∀ H, H1 ≤ H → ∀ t, HasDerivAt (Θ H) (KH H t) t)
    (horigin : ∀ H, H1 ≤ H → Θ H 0 = Ths 0)
    (hmodel : ∀ H, H1 ≤ H → (∫ t in (-(H / 2))..(H / 2), Real.sin (Ths t)) ≤ C0)
    (hpos : ∀ H, H1 ≤ H → ∀ t ∈ Ioo (-(H / 2)) (H / 2), Θ H t ∈ Ioo 0 π) :
    ∃ Hstar : ℝ, 0 < Hstar ∧ ∀ H, Hstar ≤ H →
      0 < (∫ t in (-(H / 2))..(H / 2), Real.sin (Θ H t)) ∧
        (∫ t in (-(H / 2))..(H / 2), Real.sin (Θ H t)) ≤ C0 + 1 := by
  -- past this threshold the geometric decay `e^{−βH} ≤ 1/2` also holds
  set H2 : ℝ := max H1 (Real.log 2 / beta) with hH2
  have hH2pos : 0 < H2 := lt_of_lt_of_le hH1 (le_max_left _ _)
  have hCst : 0 ≤ lipConst a * D * (8 * C ^ 2 / (alpha - beta)) + 2 * CK / alpha := by
    have hlip : 0 ≤ lipConst a := lipConst_nonneg ha0 ha1
    have hgap : 0 < alpha - beta := by linarith
    have hCK : 0 ≤ CK := by
      have h := hKbd 0
      have h0 := le_abs_self (Kstar 0)
      have h1 := hK0 0
      simp at h
      linarith
    positivity
  have hΘcont : ∀ H, H2 ≤ H → Continuous (Θ H) := by
    intro H hH
    have hH1' : H1 ≤ H := le_trans (le_max_left _ _) hH
    exact continuous_iff_continuousAt.mpr fun t => (hderiv H hH1' t).continuousAt
  have hThscont : Continuous Ths :=
    continuous_iff_continuousAt.mpr fun t => (hThs t).continuousAt
  have hclose : ∀ H, H2 ≤ H → ∀ t ∈ uIoc (-(H / 2)) (H / 2),
      |Θ H t - Ths t|
        ≤ (lipConst a * D * (8 * C ^ 2 / (alpha - beta)) + 2 * CK / alpha)
          * Real.exp (-beta * H) := by
    intro H hH t ht
    have hH1' : H1 ≤ H := le_trans (le_max_left _ _) hH
    have hHpos : 0 < H := lt_of_lt_of_le hH2pos hH
    have hlog : Real.log 2 / beta ≤ H := le_trans (le_max_right _ _) hH
    have hhalf : Real.exp (-(beta * H)) ≤ 1 / 2 := by
      have hlogle : Real.log 2 ≤ beta * H := by
        rw [div_le_iff₀ hbeta] at hlog
        linarith [hlog]
      have h2 : Real.exp (-(beta * H)) ≤ Real.exp (-Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have h3 : Real.exp (-Real.log 2) = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
        norm_num
      linarith [h2, h3.le, h3.ge]
    have hs : t ∈ Icc (-(H / 2)) (H / 2) := by
      rw [uIoc_of_le (by linarith : -(H / 2) ≤ H / 2)] at ht
      exact ⟨ht.1.le, ht.2⟩
    have h := angle_sup_close (y := y) (yp := yp) (Kstar := Kstar) (KH := KH H)
      (ThH := Θ H) (Ths := Ths) (C := C) (CK := CK) (D := D) (a := a)
      (alpha := alpha) (beta := beta) (H := H)
      halpha hHpos hbeta hba hhalf hy hyp hy0 hyb hD hypb ha0 ha1 (hYa H hH1')
      hKstar (hKH H hH1') hKint hK0 hKbd (hderiv H hH1') hThs (horigin H hH1') hs
    have hexp : Real.exp (-(beta * H)) = Real.exp (-beta * H) := by congr 1; ring
    rwa [hexp] at h
  exact exists_uniform_width_bound_of_large hbeta hCst hH2pos hΘcont hThscont
    (fun H hH => hmodel H (le_trans (le_max_left _ _) hH)) hclose
    (fun H hH => hpos H (le_trans (le_max_left _ _) hH))

end WidthUniformProduced
