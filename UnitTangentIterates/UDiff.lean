module

public import UnitTangentIterates.ParamSteering

/-!
# Differentiability in a path parameter, uniformly in the curve parameter

For a family `f : ℝ → ℝ → ℝ` (`f t u`, with `t` the path parameter and `u` the curve
parameter) we say that `f` is differentiable in `t` at `t₀`, uniformly in `u`, with derivative
`fd`, if `f t u - f t₀ u - (t - t₀) fd u = o(t - t₀)` uniformly in `u`.  This is the notion used
in `Ovals.steering_param_deriv`.  We record the elementary calculus rules.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-- Differentiability of `f t u` in `t` at `t₀`, uniformly in `u`, with derivative `fd`. -/
def UDiffAt (f : ℝ → ℝ → ℝ) (fd : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ t in 𝓝 t₀, ∀ u, |f t u - f t₀ u - (t - t₀) * fd u| ≤ ε * |t - t₀|

lemma eventually_abs_sub_le (t₀ : ℝ) {r : ℝ} (hr : 0 < r) : ∀ᶠ t in 𝓝 t₀, |t - t₀| ≤ r := by
  have : Tendsto (fun t => |t - t₀|) (𝓝 t₀) (𝓝 (|t₀ - t₀|)) :=
    (continuous_abs.comp (continuous_id.sub continuous_const)).tendsto t₀
  simp only [sub_self, abs_zero] at this
  exact this.eventually (ge_mem_nhds hr)

/-- A uniformly differentiable family is uniformly Lipschitz in `t` near `t₀`. -/
lemma UDiffAt.lip {f : ℝ → ℝ → ℝ} {fd : ℝ → ℝ} {t₀ B : ℝ} (hf : UDiffAt f fd t₀)
    (hB : ∀ u, |fd u| ≤ B) : ∀ᶠ t in 𝓝 t₀, ∀ u, |f t u - f t₀ u| ≤ (B + 1) * |t - t₀| := by
  filter_upwards [hf 1 one_pos] with t ht u
  have h2 : |(t - t₀) * fd u| ≤ B * |t - t₀| := by
    rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hB u) (abs_nonneg _)
  calc |f t u - f t₀ u| = |(f t u - f t₀ u - (t - t₀) * fd u) + (t - t₀) * fd u| := by ring_nf
    _ ≤ |f t u - f t₀ u - (t - t₀) * fd u| + |(t - t₀) * fd u| := abs_add_le _ _
    _ ≤ 1 * |t - t₀| + B * |t - t₀| := add_le_add (ht u) h2
    _ = (B + 1) * |t - t₀| := by ring

lemma UDiffAt.add {f g : ℝ → ℝ → ℝ} {fd gd : ℝ → ℝ} {t₀ : ℝ} (hf : UDiffAt f fd t₀)
    (hg : UDiffAt g gd t₀) : UDiffAt (fun t u => f t u + g t u) (fun u => fd u + gd u) t₀ := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by positivity), hg (ε / 2) (by positivity)] with t h1 h2 u
  calc |f t u + g t u - (f t₀ u + g t₀ u) - (t - t₀) * (fd u + gd u)|
      = |(f t u - f t₀ u - (t - t₀) * fd u) + (g t u - g t₀ u - (t - t₀) * gd u)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ ε / 2 * |t - t₀| + ε / 2 * |t - t₀| := add_le_add (h1 u) (h2 u)
    _ = ε * |t - t₀| := by ring

lemma UDiffAt.neg {f : ℝ → ℝ → ℝ} {fd : ℝ → ℝ} {t₀ : ℝ} (hf : UDiffAt f fd t₀) :
    UDiffAt (fun t u => - f t u) (fun u => - fd u) t₀ := by
  intro ε hε
  filter_upwards [hf ε hε] with t h u
  calc |-f t u - -f t₀ u - (t - t₀) * -fd u| = |f t u - f t₀ u - (t - t₀) * fd u| := by
        rw [← abs_neg]; ring_nf
    _ ≤ _ := h u

lemma UDiffAt.sub {f g : ℝ → ℝ → ℝ} {fd gd : ℝ → ℝ} {t₀ : ℝ} (hf : UDiffAt f fd t₀)
    (hg : UDiffAt g gd t₀) : UDiffAt (fun t u => f t u - g t u) (fun u => fd u - gd u) t₀ := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

lemma UDiffAt.const (c : ℝ → ℝ) (t₀ : ℝ) : UDiffAt (fun _ u => c u) (fun _ => 0) t₀ := by
  intro ε hε
  exact Eventually.of_forall fun t u => by simp; positivity

/-- **Product rule.** -/
lemma UDiffAt.mul {f g : ℝ → ℝ → ℝ} {fd gd : ℝ → ℝ} {t₀ B : ℝ} (hf : UDiffAt f fd t₀)
    (hg : UDiffAt g gd t₀) (hfB : ∀ u, |f t₀ u| ≤ B) (hgB : ∀ u, |g t₀ u| ≤ B)
    (hfdB : ∀ u, |fd u| ≤ B) (hgdB : ∀ u, |gd u| ≤ B) :
    UDiffAt (fun t u => f t u * g t u) (fun u => fd u * g t₀ u + f t₀ u * gd u) t₀ := by
  intro ε hε
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hfB 0)
  set ε' := ε / (3 * (3 * B + 2)) with hε'
  have hε'0 : 0 < ε' := by positivity
  set r := min 1 (ε / (3 * (B * (B + 1) + 1))) with hr
  have hr0 : 0 < r := lt_min one_pos (by positivity)
  filter_upwards [hf ε' hε'0, hg ε' hε'0, hg.lip hgdB, eventually_abs_sub_le t₀ hr0]
    with t h1 h2 h3 h4 u
  set h := t - t₀
  have hh1 : |h| ≤ 1 := h4.trans (min_le_left _ _)
  have hh2 : |h| ≤ ε / (3 * (B * (B + 1) + 1)) := h4.trans (min_le_right _ _)
  have hgt : |g t u| ≤ 2 * B + 1 := by
    have := h3 u
    calc |g t u| = |(g t u - g t₀ u) + g t₀ u| := by ring_nf
      _ ≤ |g t u - g t₀ u| + |g t₀ u| := abs_add_le _ _
      _ ≤ (B + 1) * 1 + B := add_le_add (this.trans (by gcongr)) (hgB u)
      _ = 2 * B + 1 := by ring
  have e : f t u * g t u - f t₀ u * g t₀ u - h * (fd u * g t₀ u + f t₀ u * gd u) =
      (f t u - f t₀ u - h * fd u) * g t u + h * fd u * (g t u - g t₀ u) +
        f t₀ u * (g t u - g t₀ u - h * gd u) := by simp only [h]; ring
  rw [e]
  have t1 : |(f t u - f t₀ u - h * fd u) * g t u| ≤ ε' * |h| * (2 * B + 1) := by
    rw [abs_mul]; exact mul_le_mul (h1 u) hgt (abs_nonneg _) (by positivity)
  have t2 : |h * fd u * (g t u - g t₀ u)| ≤ |h| * B * ((B + 1) * |h|) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul le_rfl (hfdB u) (abs_nonneg _) (abs_nonneg _)) (h3 u)
      (abs_nonneg _) (by positivity)
  have t3 : |f t₀ u * (g t u - g t₀ u - h * gd u)| ≤ B * (ε' * |h|) := by
    rw [abs_mul]; exact mul_le_mul (hfB u) (h2 u) (abs_nonneg _) hB0
  have t2' : |h| * B * ((B + 1) * |h|) ≤ ε / 3 * |h| := by
    have : B * (B + 1) * |h| ≤ ε / 3 := by
      have hpos : 0 < 3 * (B * (B + 1) + 1) := by positivity
      have := mul_le_mul_of_nonneg_left hh2 (show 0 ≤ B * (B + 1) by positivity)
      calc B * (B + 1) * |h| ≤ B * (B + 1) * (ε / (3 * (B * (B + 1) + 1))) := this
        _ ≤ (B * (B + 1) + 1) * (ε / (3 * (B * (B + 1) + 1))) := by
          gcongr; linarith
        _ = ε / 3 := by field_simp
    nlinarith [abs_nonneg h]
  have t13 : ε' * |h| * (2 * B + 1) + B * (ε' * |h|) ≤ 2 * ε / 3 * |h| := by
    have : ε' * (3 * B + 1) ≤ 2 * ε / 3 := by
      rw [hε']
      have hpos : 0 < 3 * (3 * B + 2) := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith
    nlinarith [abs_nonneg h]
  calc _ ≤ |(f t u - f t₀ u - h * fd u) * g t u| + |h * fd u * (g t u - g t₀ u)| +
        |f t₀ u * (g t u - g t₀ u - h * gd u)| := abs_add_three _ _ _
    _ ≤ ε * |h| := by linarith

lemma UDiffAt.const_mul {f : ℝ → ℝ → ℝ} {fd : ℝ → ℝ} {t₀ : ℝ} (c : ℝ) (hf : UDiffAt f fd t₀) :
    UDiffAt (fun t u => c * f t u) (fun u => c * fd u) t₀ := by
  intro ε hε
  filter_upwards [hf (ε / (|c| + 1)) (by positivity)] with t h u
  have e : c * f t u - c * f t₀ u - (t - t₀) * (c * fd u) = c * (f t u - f t₀ u - (t - t₀) * fd u) := by
    ring
  rw [e, abs_mul]
  calc |c| * |f t u - f t₀ u - (t - t₀) * fd u| ≤ (|c| + 1) * (ε / (|c| + 1) * |t - t₀|) := by
        gcongr; · linarith [abs_nonneg c]
        · exact h u
    _ = ε * |t - t₀| := by field_simp

lemma abs_cos_sub_cos_add_sin_mul_le (x y : ℝ) :
    |Real.cos x - Real.cos y + Real.sin y * (x - y)| ≤ (x - y) ^ 2 := by
  have := abs_sin_sub_sin_sub_cos_mul_le (x + π / 2) (y + π / 2)
  rw [Real.sin_add_pi_div_two, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at this
  convert this using 2 <;> ring

/-- Composition with `sin`. -/
lemma UDiffAt.sin {f : ℝ → ℝ → ℝ} {fd : ℝ → ℝ} {t₀ B : ℝ} (hf : UDiffAt f fd t₀)
    (hB : ∀ u, |fd u| ≤ B) :
    UDiffAt (fun t u => Real.sin (f t u)) (fun u => Real.cos (f t₀ u) * fd u) t₀ := by
  intro ε hε
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set r := ε / (2 * (B + 1) ^ 2) with hr
  have hr0 : 0 < r := by positivity
  filter_upwards [hf (ε / 2) (by positivity), hf.lip hB, eventually_abs_sub_le t₀ hr0]
    with t h1 h2 h3 u
  set h := t - t₀
  have e : Real.sin (f t u) - Real.sin (f t₀ u) - h * (Real.cos (f t₀ u) * fd u) =
      (Real.sin (f t u) - Real.sin (f t₀ u) - Real.cos (f t₀ u) * (f t u - f t₀ u)) +
        Real.cos (f t₀ u) * (f t u - f t₀ u - h * fd u) := by simp only [h]; ring
  rw [e]
  have a1 : |Real.sin (f t u) - Real.sin (f t₀ u) - Real.cos (f t₀ u) * (f t u - f t₀ u)| ≤
      ((B + 1) * |h|) ^ 2 := by
    refine (abs_sin_sub_sin_sub_cos_mul_le _ _).trans ?_
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h2 u) 2
  have a2 : |Real.cos (f t₀ u) * (f t u - f t₀ u - h * fd u)| ≤ ε / 2 * |h| := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans (h1 u)
  have a3 : ((B + 1) * |h|) ^ 2 ≤ ε / 2 * |h| := by
    have : (B + 1) ^ 2 * |h| ≤ ε / 2 := by
      calc (B + 1) ^ 2 * |h| ≤ (B + 1) ^ 2 * r := by gcongr
        _ = ε / 2 := by rw [hr]; field_simp
    nlinarith [abs_nonneg h]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ ε * |h| := by linarith

/-- Composition with `cos`. -/
lemma UDiffAt.cos {f : ℝ → ℝ → ℝ} {fd : ℝ → ℝ} {t₀ B : ℝ} (hf : UDiffAt f fd t₀)
    (hB : ∀ u, |fd u| ≤ B) :
    UDiffAt (fun t u => Real.cos (f t u)) (fun u => -(Real.sin (f t₀ u) * fd u)) t₀ := by
  intro ε hε
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set r := ε / (2 * (B + 1) ^ 2) with hr
  have hr0 : 0 < r := by positivity
  filter_upwards [hf (ε / 2) (by positivity), hf.lip hB, eventually_abs_sub_le t₀ hr0]
    with t h1 h2 h3 u
  set h := t - t₀
  have e : Real.cos (f t u) - Real.cos (f t₀ u) - h * -(Real.sin (f t₀ u) * fd u) =
      (Real.cos (f t u) - Real.cos (f t₀ u) + Real.sin (f t₀ u) * (f t u - f t₀ u)) -
        Real.sin (f t₀ u) * (f t u - f t₀ u - h * fd u) := by simp only [h]; ring
  rw [e]
  have a1 : |Real.cos (f t u) - Real.cos (f t₀ u) + Real.sin (f t₀ u) * (f t u - f t₀ u)| ≤
      ((B + 1) * |h|) ^ 2 := by
    refine (abs_cos_sub_cos_add_sin_mul_le _ _).trans ?_
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h2 u) 2
  have a2 : |Real.sin (f t₀ u) * (f t u - f t₀ u - h * fd u)| ≤ ε / 2 * |h| := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)).trans (h1 u)
  have a3 : ((B + 1) * |h|) ^ 2 ≤ ε / 2 * |h| := by
    have : (B + 1) ^ 2 * |h| ≤ ε / 2 := by
      calc (B + 1) ^ 2 * |h| ≤ (B + 1) ^ 2 * r := by gcongr
        _ = ε / 2 := by rw [hr]; field_simp
    nlinarith [abs_nonneg h]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ ε * |h| := by linarith

/-- Two uniform derivatives agree if the families agree near `t₀`. -/
lemma UDiffAt.congr {f g : ℝ → ℝ → ℝ} {fd gd : ℝ → ℝ} {t₀ : ℝ} (hf : UDiffAt f fd t₀)
    (hfg : ∀ t u, f t u = g t u) (hd : ∀ u, fd u = gd u) : UDiffAt g gd t₀ := by
  intro ε hε
  filter_upwards [hf ε hε] with t h u
  rw [← hfg, ← hfg, ← hd]; exact h u

/-- **Differentiation under the integral sign.** -/
lemma UDiffAt.hasDerivAt_integral {f : ℝ → ℝ → ℝ} {fd : ℝ → ℝ} {t₀ a b : ℝ}
    (hf : UDiffAt f fd t₀) (hfc : ∀ t, Continuous (f t)) (hfdc : Continuous fd) (hab : a ≤ b) :
    HasDerivAt (fun t => ∫ u in a..b, f t u) (∫ u in a..b, fd u) t₀ := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hba : 0 ≤ b - a := by linarith
  filter_upwards [hf (ε / (b - a + 1)) (by positivity)] with t ht
  have e : (∫ u in a..b, f t u) - (∫ u in a..b, f t₀ u) - (t - t₀) • ∫ u in a..b, fd u =
      ∫ u in a..b, (f t u - f t₀ u - (t - t₀) * fd u) := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, smul_eq_mul]
    · exact (hfc t).intervalIntegrable _ _
    · exact (hfc t₀).intervalIntegrable _ _
    · exact ((hfc t).sub (hfc t₀)).intervalIntegrable _ _
    · exact (continuous_const.mul hfdc).intervalIntegrable _ _
  rw [e, Real.norm_eq_abs, Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (C := ε / (b - a + 1) * |t - t₀|)
    (f := fun u => f t u - f t₀ u - (t - t₀) * fd u) (fun u _ => by
      rw [Real.norm_eq_abs]; exact ht u)
  rw [Real.norm_eq_abs, abs_of_nonneg hba] at this
  calc _ ≤ ε / (b - a + 1) * |t - t₀| * (b - a) := this
    _ ≤ ε * |t - t₀| := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg (t - t₀), hε.le, mul_nonneg hε.le (abs_nonneg (t - t₀))]

end Ovals

end
