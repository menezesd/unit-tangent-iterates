import Mathlib

/-!
# The fundamental interval and the uniform transverse width

This file formalizes the self-contained cores of two lemmas of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*:

* the lemma *Common phase and fundamental interval*: since the rear
  arclength satisfies `x_H' = c_H > 0`, the image `J_H = x_H(I_H)` of the
  centred cell is an interval of length `P(H) = ∫_{I_H} c_H`, and its
  translates by `P(H)ℤ` tile the line;
* the lemma *Uniform transverse width*: the transverse displacement
  `W_H = ∫_{I_H} sin Θ_H` is positive, and is compared with the
  corresponding integral for the isolated hairpin through the sup-norm
  distance of the two tangent angles, which itself is controlled by the
  curvature distance.

Main results:

* `strictMono_of_hasDerivAt_pos`, `image_Icc_eq_Icc`, `length_image_eq_integral` :
  the fundamental interval and its length;
* `exists_unique_translate_mem_Ico` : the translates of a half-open interval of
  length `P > 0` tile `ℝ`;
* `abs_angle_sub_le` : `‖Θ - Θ_*‖_{L^∞[a,b]} ≤ e + d(b-a)` from
  `|Θ(a) - Θ_*(a)| ≤ e` and `‖Θ' - Θ_*'‖_∞ ≤ d`;
* `abs_width_sub_le`, `width_le` : the width comparison
  `W ≤ ∫ sin Θ_* + (b-a)ε`;
* `width_pos` : positivity of the width.
-/

noncomputable section

open Real MeasureTheory intervalIntegral Set

namespace PhaseWidth

/-! ### The fundamental interval -/

section Fundamental

variable {x c : ℝ → ℝ} {a b : ℝ}

/-- A function with everywhere positive derivative is strictly monotone. -/
theorem strictMono_of_hasDerivAt_pos (hx : ∀ t, HasDerivAt x (c t) t) (hc : ∀ t, 0 < c t) :
    StrictMono x := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(hx t).deriv]
  exact hc t

/-- **The fundamental interval.**  The image of `[a,b]` under the rear
arclength map is the interval `[x a, x b]`. -/
theorem image_Icc_eq_Icc (hx : ∀ t, HasDerivAt x (c t) t) (hc : ∀ t, 0 < c t) (hab : a ≤ b) :
    x '' Icc a b = Icc (x a) (x b) := by
  have hmono : StrictMono x := strictMono_of_hasDerivAt_pos hx hc
  have hdiff : Differentiable ℝ x := fun t => (hx t).differentiableAt
  exact hdiff.continuous.continuousOn.image_Icc_of_monotoneOn hab (hmono.monotone.monotoneOn _)

/-- **The length of the fundamental interval** is `∫ c`. -/
theorem length_image_eq_integral (hx : ∀ t, HasDerivAt x (c t) t) (hcc : Continuous c) :
    x b - x a = ∫ t in a..b, c t :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hx t)
    (hcc.intervalIntegrable _ _)).symm

/-- **Tiling.**  The translates of a half-open interval of length `P > 0` by
`Pℤ` tile the line. -/
theorem exists_unique_translate_mem_Ico {P : ℝ} (hP : 0 < P) (alpha t : ℝ) :
    ∃! m : ℤ, t - m * P ∈ Ico alpha (alpha + P) := by
  refine ⟨⌊(t - alpha) / P⌋, ?_, ?_⟩
  · have h1 : (⌊(t - alpha) / P⌋ : ℝ) ≤ (t - alpha) / P := Int.floor_le _
    have h2 : (t - alpha) / P < ⌊(t - alpha) / P⌋ + 1 := Int.lt_floor_add_one _
    have h1' : (⌊(t - alpha) / P⌋ : ℝ) * P ≤ t - alpha := by
      rw [le_div_iff₀ hP] at h1; linarith
    have h2' : t - alpha < ((⌊(t - alpha) / P⌋ : ℝ) + 1) * P := by
      rw [div_lt_iff₀ hP] at h2; linarith
    constructor <;> [linarith; nlinarith]
  · intro m hm
    obtain ⟨hm1, hm2⟩ := hm
    have hlo : (m : ℝ) ≤ (t - alpha) / P := by
      rw [le_div_iff₀ hP]; linarith
    have hhi : (t - alpha) / P < m + 1 := by
      rw [div_lt_iff₀ hP]; linarith [hm2]
    symm
    exact Int.floor_eq_iff.mpr ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

end Fundamental

/-! ### The transverse width -/

section Width

variable {Θ Θs K Ks : ℝ → ℝ} {a b d e ε : ℝ}

/-- **Sup-norm control of the tangent angle** from the curvature distance and
the value at the left endpoint. -/
theorem abs_angle_sub_le (hΘ : ∀ t, HasDerivAt Θ (K t) t) (hΘs : ∀ t, HasDerivAt Θs (Ks t) t)
    (hd : ∀ t ∈ Icc a b, |K t - Ks t| ≤ d) (he : |Θ a - Θs a| ≤ e) (hab : a ≤ b)
    {s : ℝ} (hs : s ∈ Icc a b) :
    |Θ s - Θs s| ≤ e + d * (b - a) := by
  have ha : a ∈ Icc a b := ⟨le_refl a, hab⟩
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) (hd a ha)
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun r => Θ r - Θs r) (K t - Ks t) (Icc a b) t := fun t _ =>
    ((hΘ t).sub (hΘs t)).hasDerivWithinAt
  have hbound : ∀ t ∈ Icc a b, ‖K t - Ks t‖ ≤ d := fun t ht => by
    simpa [Real.norm_eq_abs] using hd t ht
  have hmain := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound ha hs
  have hstep : |(Θ s - Θs s) - (Θ a - Θs a)| ≤ d * (b - a) := by
    have h := hmain
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    refine h.trans ?_
    have : |s - a| ≤ b - a := by
      rw [abs_of_nonneg (by linarith [hs.1])]
      linarith [hs.2]
    exact mul_le_mul_of_nonneg_left this hd0
  have := abs_sub_abs_le_abs_sub (Θ s - Θs s) (Θ a - Θs a)
  calc |Θ s - Θs s| ≤ |(Θ s - Θs s) - (Θ a - Θs a)| + |Θ a - Θs a| := by linarith
    _ ≤ d * (b - a) + e := add_le_add hstep he
    _ = e + d * (b - a) := by ring

/-- **Width comparison.**  If two tangent angles are `ε`-close on `[a,b]`, the
transverse displacements they produce differ by at most `ε (b-a)`. -/
theorem abs_width_sub_le (hΘ : Continuous Θ) (hΘs : Continuous Θs) (hab : a ≤ b)
    (hε : ∀ t ∈ uIoc a b, |Θ t - Θs t| ≤ ε) :
    |(∫ t in a..b, Real.sin (Θ t)) - ∫ t in a..b, Real.sin (Θs t)| ≤ ε * (b - a) := by
  have hi1 : IntervalIntegrable (fun t => Real.sin (Θ t)) volume a b :=
    (Real.continuous_sin.comp hΘ).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t => Real.sin (Θs t)) volume a b :=
    (Real.continuous_sin.comp hΘs).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hi1 hi2]
  have hbd : ∀ t ∈ uIoc a b, ‖Real.sin (Θ t) - Real.sin (Θs t)‖ ≤ ε := by
    intro t ht
    have hlip : |Real.sin (Θ t) - Real.sin (Θs t)| ≤ |Θ t - Θs t| := by
      have := Real.lipschitzWith_sin.dist_le_mul (Θ t) (Θs t)
      simpa [Real.dist_eq] using this
    simpa [Real.norm_eq_abs] using hlip.trans (hε t ht)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at this
  exact this

/-- The width is bounded by the width of the model plus the error term. -/
theorem width_le (hΘ : Continuous Θ) (hΘs : Continuous Θs) (hab : a ≤ b)
    (hε : ∀ t ∈ uIoc a b, |Θ t - Θs t| ≤ ε) :
    (∫ t in a..b, Real.sin (Θ t)) ≤ (∫ t in a..b, Real.sin (Θs t)) + ε * (b - a) := by
  have h := abs_width_sub_le hΘ hΘs hab hε
  have := (abs_le.mp h).2
  linarith

/-- **Positivity of the width.**  If the tangent angle stays in `(0,π)` on the
open cell, the transverse displacement is positive. -/
theorem width_pos (hΘ : Continuous Θ) (hab : a < b)
    (hpos : ∀ t ∈ Ioo a b, Θ t ∈ Ioo 0 Real.pi) :
    0 < ∫ t in a..b, Real.sin (Θ t) := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((Real.continuous_sin.comp hΘ).intervalIntegrable _ _) (fun t ht => ?_) hab
  exact Real.sin_pos_of_pos_of_lt_pi (hpos t ht).1 (hpos t ht).2

end Width

end PhaseWidth
