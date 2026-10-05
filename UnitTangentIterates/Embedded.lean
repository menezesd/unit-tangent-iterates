module

public import UnitTangentIterates.CurveFromCurvature

/-!
# Closed curves of nonnegative curvature and total turning `2π` are embedded

Proposition 4.3, Lemma 6.1 and the limit argument of Theorem 6.4 all need that the closed
curves they build do not cross themselves.  We prove the elementary criterion behind this.

* `Ovals.ne_of_turning_le_pi`: if a regular curve with unit tangent `τ(θ)` has monotone tangent
  angle and turns by at most `π` on `[a, b]` (`a < b`), then `X a ≠ X b`.  Indeed, in the
  direction bisecting the tangent angles, the velocity has nonnegative component, positive
  where the tangent points exactly in that direction.
* `Ovals.injOn_of_turning`: a `p`-periodic regular curve whose monotone tangent angle increases
  by exactly `2π` per period is injective on `[0, p)`.  Any two parameters split the period
  into two arcs, one of which turns by at most `π`.
* `Ovals.injOn_curveOfCurvature`: the centrally symmetric curves `(6.2)` built from a
  nonnegative `L`-periodic curvature with `∫₀ᴸ κ = π` are embedded.
* `Ovals.isOval_curveOfCurvature`: for smooth positive such curvature they are ovals.
-/

@[expose] public section

namespace Ovals

open Complex Real intervalIntegral MeasureTheory
open scoped ContDiff

lemma tau_mul_conj_tau (a b : ℝ) : tau a * (starRingEnd ℂ) (tau b) = tau (a - b) := by
  unfold tau
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

lemma re_tau (a : ℝ) : (tau a).re = Real.cos a := by
  rw [tau_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

/-- **Arcs of small turning are not closed.**  Let `X' = g · τ(θ)` with `g > 0` continuous and
`θ` continuous and monotone.  If `a < b` and `θ b - θ a ≤ π`, then `X a ≠ X b`. -/
theorem ne_of_turning_le_pi {X : ℝ → ℂ} {g θ : ℝ → ℝ} (hg : Continuous g)
    (hgpos : ∀ s, 0 < g s) (hθ : Continuous θ) (hmono : Monotone θ)
    (hX : ∀ s, HasDerivAt X ((g s : ℂ) * tau (θ s)) s) {a b : ℝ} (hab : a < b)
    (hturn : θ b - θ a ≤ π) : X a ≠ X b := by
  intro hXab
  set c := (θ a + θ b) / 2 with hc
  have hcont : Continuous fun s => (g s : ℂ) * tau (θ s) :=
    (Complex.continuous_ofReal.comp hg).mul (continuous_tau.comp hθ)
  have hftc : ∫ s in a..b, (g s : ℂ) * tau (θ s) = X b - X a :=
    integral_eq_sub_of_hasDerivAt (fun s _ => hX s) (hcont.intervalIntegrable _ _)
  -- the component in direction `τ(c)`
  have hcomp : ∫ s in a..b, g s * Real.cos (θ s - c) = 0 := by
    have h1 : (∫ s in a..b, (g s : ℂ) * tau (θ s)) * (starRingEnd ℂ) (tau c) = 0 := by
      rw [hftc, hXab, sub_self, zero_mul]
    rw [← intervalIntegral.integral_mul_const] at h1
    have h2 := congrArg Complex.re h1
    have h3 := Complex.reCLM.intervalIntegral_comp_comm
      ((hcont.mul (continuous_const (y := (starRingEnd ℂ) (tau c)))).intervalIntegrable
        (μ := volume) a b)
    simp only [Complex.reCLM_apply, Pi.mul_apply] at h3
    rw [Complex.zero_re, ← h3] at h2
    convert h2 using 2
    funext s
    rw [mul_assoc, tau_mul_conj_tau, Complex.re_ofReal_mul, re_tau]
  have hpos : 0 < ∫ s in a..b, g s * Real.cos (θ s - c) := by
    apply intervalIntegral.integral_pos hab
    · exact (hg.mul (Real.continuous_cos.comp (hθ.sub continuous_const))).continuousOn
    · intro s hs
      have h1 := hmono hs.1.le
      have h2 := hmono hs.2
      apply mul_nonneg (hgpos s).le
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith [hc]
    · obtain ⟨s₀, hs₀, hθs₀⟩ : ∃ s₀ ∈ Set.Icc a b, θ s₀ = c := by
        have := intermediate_value_Icc hab.le hθ.continuousOn
        exact this ⟨by have := hmono hab.le; linarith [hc], by have := hmono hab.le; linarith [hc]⟩
      exact ⟨s₀, hs₀, by rw [hθs₀, sub_self, Real.cos_zero, mul_one]; exact hgpos s₀⟩
  linarith

/-- **Embeddedness criterion.**  A `p`-periodic curve with `X' = g · τ(θ)`, `g > 0`, whose
continuous monotone tangent angle satisfies `θ(s + p) = θ(s) + 2π`, is injective on `[0, p)`. -/
theorem injOn_of_turning {X : ℝ → ℂ} {g θ : ℝ → ℝ} {p : ℝ} (hg : Continuous g)
    (hgpos : ∀ s, 0 < g s) (hθ : Continuous θ) (hmono : Monotone θ)
    (hX : ∀ s, HasDerivAt X ((g s : ℂ) * tau (θ s)) s) (hXp : Function.Periodic X p)
    (hθp : ∀ s, θ (s + p) = θ s + 2 * π) : Set.InjOn X (Set.Ico 0 p) := by
  -- it suffices to treat `u < w`
  have key : ∀ u w, u ∈ Set.Ico 0 p → w ∈ Set.Ico 0 p → u < w → X u ≠ X w := by
    intro u w hu hw huw hXuw
    rcases le_or_gt (θ w - θ u) π with h | h
    · exact ne_of_turning_le_pi hg hgpos hθ hmono hX huw h hXuw
    · -- the complementary arc `[w, u + p]` turns by less than `π`
      have hwu : w < u + p := by linarith [hw.2, hu.1]
      have hturn : θ (u + p) - θ w ≤ π := by rw [hθp]; linarith
      apply ne_of_turning_le_pi hg hgpos hθ hmono hX hwu hturn
      rw [hXp, hXuw]
  intro u hu w hw huw
  rcases lt_trichotomy u w with h | h | h
  · exact absurd huw (key u w hu hw h)
  · exact h
  · exact absurd huw.symm (key w u hw hu h)

/-- **The closed curves `(6.2)` are embedded.**  If `κ ≥ 0` is continuous and `L`-periodic
with `∫₀ᴸ κ = π`, the centered curve with curvature `κ` is injective on `[0, 2L)`. -/
theorem injOn_curveOfCurvature {θ₀ L : ℝ} {κ : ℝ → ℝ} (hκ : Continuous κ)
    (hκ0 : ∀ s, 0 ≤ κ s) (hκp : Function.Periodic κ L) (hint : ∫ r in (0 : ℝ)..L, κ r = π) :
    Set.InjOn (curveOfCurvature θ₀ κ L) (Set.Ico 0 (2 * L)) := by
  have hmono : Monotone (angleOfCurvature θ₀ κ) := by
    intro u w huw
    unfold angleOfCurvature
    have h1 := intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := u) (c := w)
      (hκ.intervalIntegrable (μ := volume) _ _) (hκ.intervalIntegrable _ _)
    have := intervalIntegral.integral_nonneg (μ := volume) huw (fun r _ => hκ0 r)
    linarith
  refine injOn_of_turning (g := fun _ => 1) continuous_const (fun _ => one_pos)
    (continuous_angleOfCurvature hκ) hmono (fun s => ?_)
    (curveOfCurvature_periodic hκ hκp hint) (fun s => ?_)
  · simpa using hasDerivAt_curveOfCurvature (θ₀ := θ₀) (L := L) hκ s
  · rw [two_mul, ← add_assoc, angleOfCurvature_add_period hκ hκp hint,
      angleOfCurvature_add_period hκ hκp hint]; ring

theorem contDiff_angleOfCurvature {θ₀ : ℝ} {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) :
    ContDiff ℝ ∞ (angleOfCurvature θ₀ κ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (hasDerivAt_angleOfCurvature hκ.continuous s).differentiableAt, ?_⟩
  rw [show deriv (angleOfCurvature θ₀ κ) = κ from
    funext fun s => (hasDerivAt_angleOfCurvature hκ.continuous s).deriv]
  exact hκ

theorem contDiff_curveOfCurvature {θ₀ L : ℝ} {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) :
    ContDiff ℝ ∞ (curveOfCurvature θ₀ κ L) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (hasDerivAt_curveOfCurvature hκ.continuous s).differentiableAt, ?_⟩
  rw [deriv_curveOfCurvature hκ.continuous]
  exact contDiff_tau.comp (contDiff_angleOfCurvature hκ)

/-- **The closed curves `(6.2)` are ovals.**  If `κ > 0` is smooth and `L`-periodic with
`∫₀ᴸ κ = π`, the centered curve with curvature `κ` is an oval of perimeter `2L`. -/
theorem isOval_curveOfCurvature {θ₀ L : ℝ} {κ : ℝ → ℝ} (hL : 0 < L) (hκ : ContDiff ℝ ∞ κ)
    (hκ0 : ∀ s, 0 < κ s) (hκp : Function.Periodic κ L) (hint : ∫ r in (0 : ℝ)..L, κ r = π) :
    IsOval (curveOfCurvature θ₀ κ L) where
  contDiff := contDiff_curveOfCurvature hκ
  regular := fun s => by
    rw [← norm_ne_zero_iff, norm_deriv_curveOfCurvature hκ.continuous]; exact one_ne_zero
  curvature_pos := fun s => by rw [curvature_curveOfCurvature hκ.continuous]; exact hκ0 s
  closed_simple := ⟨2 * L, by positivity, curveOfCurvature_periodic hκ.continuous hκp hint,
    injOn_curveOfCurvature hκ.continuous (fun s => (hκ0 s).le) hκp hint⟩

end Ovals

end
