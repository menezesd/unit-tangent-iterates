import Mathlib

/-!
# Regularity of a fixed point of the translator operator

In Section 3 of *A Noncircular Oval with Convex Unit-Tangent Iterates* the
hairpin profile is produced as the limit of the monotone iteration
`f_{n+1} = 𝒫 f_n`, where the translator operator is

`(𝒫f)(θ) = sin θ · cot D_f(θ)`,  `∫_θ^{θ + D_f(θ)} f = sin θ`.

The monotone limit of the iterates is only known *a priori* to be a bounded
(measurable) function: monotone pointwise limits need not be continuous.  This
file supplies the missing bootstrap, which upgrades a bounded fixed point to a
continuous one:

* the accumulated mass `A(x) = ∫₀ˣ f` of a profile with `0 < m ≤ f ≤ M` is
  bi-Lipschitz, `m(y − x) ≤ A(y) − A(x) ≤ M(y − x)` for `x ≤ y`
  (`mass_lower_bound`, `mass_upper_bound`);
* consequently the shift `D_f` is Lipschitz: two solutions of the defining
  equation at parameters `θ₁, θ₂` satisfy
  `|u₁ − u₂| ≤ ((M+1)/m)|θ₁ − θ₂|` (`shift_lipschitz`), so `θ ↦ D_f(θ)` is
  continuous on `(0, π)` (`shift_continuousOn`);
* the shift is small, `0 < D ≤ sin θ / m < π/2` (`shift_lt_pi_div_two`), so
  `cot D` is defined;
* therefore a bounded fixed point `f = sin θ · cot D_f` is automatically
  continuous on `(0, π)` (`fixedPoint_continuousOn`), which is the hypothesis
  under which `UnitTangentIterates/Hairpin.lean` shows that the profile equations
  define a complete embedded strictly convex hairpin.

Throughout, the profile is only assumed to be interval integrable and squeezed
between two constants `0 < m ≤ f ≤ M`; no continuity of `f` is assumed.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace TranslatorRegularity

variable {f : ℝ → ℝ} {m M : ℝ}

/-- The accumulated mass `A(x) = ∫₀ˣ f` of a profile. -/
def mass (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, f t

lemma mass_sub_mass (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b) (x y : ℝ) :
    mass f y - mass f x = ∫ t in x..y, f t := by
  have := intervalIntegral.integral_add_adjacent_intervals (a := (0:ℝ)) (b := x) (c := y)
    (hint 0 x) (hint x y)
  simp only [mass]
  linarith [this]

/-- **Lower bound for the accumulated mass**: `m (y − x) ≤ A(y) − A(x)` for
`x ≤ y`. -/
theorem mass_lower_bound (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hmf : ∀ t, m ≤ f t) {x y : ℝ} (hxy : x ≤ y) :
    m * (y - x) ≤ mass f y - mass f x := by
  rw [mass_sub_mass hint]
  have h := intervalIntegral.integral_mono_on (μ := volume) (a := x) (b := y)
    (f := fun _ => m) (g := f) hxy _root_.intervalIntegrable_const (hint x y) (fun t _ => hmf t)
  simpa [mul_comm] using h

/-- **Upper bound for the accumulated mass**: `A(y) − A(x) ≤ M (y − x)` for
`x ≤ y`. -/
theorem mass_upper_bound (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hfM : ∀ t, f t ≤ M) {x y : ℝ} (hxy : x ≤ y) :
    mass f y - mass f x ≤ M * (y - x) := by
  rw [mass_sub_mass hint]
  have h := intervalIntegral.integral_mono_on (μ := volume) (a := x) (b := y)
    (f := f) (g := fun _ => M) hxy (hint x y) _root_.intervalIntegrable_const (fun t _ => hfM t)
  simpa [mul_comm] using h

/-- The two-sided version: `m|y − x| ≤ |A(y) − A(x)| ≤ M|y − x|`. -/
theorem abs_mass_sub (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b) (hm0 : 0 ≤ m)
    (hmf : ∀ t, m ≤ f t) (hfM : ∀ t, f t ≤ M) (x y : ℝ) :
    m * |y - x| ≤ |mass f y - mass f x| ∧ |mass f y - mass f x| ≤ M * |y - x| := by
  rcases le_total x y with h | h
  · have hlo := mass_lower_bound hint hmf h
    have hhi := mass_upper_bound hint hfM h
    have hd : 0 ≤ mass f y - mass f x := le_trans (by nlinarith) hlo
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x), abs_of_nonneg hd]
    exact ⟨hlo, hhi⟩
  · have hlo := mass_lower_bound hint hmf h
    have hhi := mass_upper_bound hint hfM h
    have hd : mass f y - mass f x ≤ 0 := by nlinarith
    rw [abs_of_nonpos (by linarith : y - x ≤ 0), abs_of_nonpos hd]
    constructor <;> nlinarith

/-! ### The shift is Lipschitz -/

/-- **The translator shift is Lipschitz.**  If `u₁` and `u₂` solve the defining
equations `∫_{θ_i}^{u_i} f = sin θ_i` for a profile with `0 < m ≤ f ≤ M`, then
`|u₁ − u₂| ≤ ((M+1)/m)|θ₁ − θ₂|`. -/
theorem shift_lipschitz (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b) (hm0 : 0 < m)
    (hmf : ∀ t, m ≤ f t) (hfM : ∀ t, f t ≤ M) {θ₁ θ₂ u₁ u₂ : ℝ}
    (h₁ : (∫ t in θ₁..u₁, f t) = Real.sin θ₁)
    (h₂ : (∫ t in θ₂..u₂, f t) = Real.sin θ₂) :
    |u₁ - u₂| ≤ (M + 1) / m * |θ₁ - θ₂| := by
  have e₁ : mass f u₁ - mass f θ₁ = Real.sin θ₁ := by rw [mass_sub_mass hint, h₁]
  have e₂ : mass f u₂ - mass f θ₂ = Real.sin θ₂ := by rw [mass_sub_mass hint, h₂]
  have hsplit : mass f u₁ - mass f u₂
      = (mass f θ₁ - mass f θ₂) + (Real.sin θ₁ - Real.sin θ₂) := by linarith
  have hsin : |Real.sin θ₁ - Real.sin θ₂| ≤ |θ₁ - θ₂| := by
    have := Real.lipschitzWith_sin.dist_le_mul θ₁ θ₂
    simpa [Real.dist_eq] using this
  have hθ : |mass f θ₁ - mass f θ₂| ≤ M * |θ₁ - θ₂| :=
    (abs_mass_sub hint hm0.le hmf hfM θ₂ θ₁).2
  have hu : m * |u₁ - u₂| ≤ |mass f u₁ - mass f u₂| :=
    (abs_mass_sub hint hm0.le hmf hfM u₂ u₁).1
  have hchain : m * |u₁ - u₂| ≤ (M + 1) * |θ₁ - θ₂| := by
    calc m * |u₁ - u₂| ≤ |mass f u₁ - mass f u₂| := hu
      _ ≤ |mass f θ₁ - mass f θ₂| + |Real.sin θ₁ - Real.sin θ₂| := by
          rw [hsplit]; exact abs_add_le _ _
      _ ≤ M * |θ₁ - θ₂| + |θ₁ - θ₂| := add_le_add hθ hsin
      _ = (M + 1) * |θ₁ - θ₂| := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hm0, mul_comm]
  linarith

/-- **The shift function is continuous** on any set on which it solves the
defining equation. -/
theorem shift_continuousOn (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b) (hm0 : 0 < m)
    (hmf : ∀ t, m ≤ f t) (hfM : ∀ t, f t ≤ M) {s : Set ℝ} {U : ℝ → ℝ}
    (hU : ∀ θ ∈ s, (∫ t in θ..U θ, f t) = Real.sin θ) :
    ContinuousOn U s := by
  intro θ hθ
  refine Metric.continuousWithinAt_iff.mpr ?_
  intro ε hε
  have hMpos : 0 < M + 1 := by
    have : m ≤ M := le_trans (hmf 0) (hfM 0)
    linarith
  have hM1 : 0 < (M + 1) / m := div_pos hMpos hm0
  refine ⟨ε / ((M + 1) / m), by positivity, ?_⟩
  intro y hy hdist
  have hlip := shift_lipschitz hint hm0 hmf hfM (hU y hy) (hU θ hθ)
  rw [Real.dist_eq] at hdist ⊢
  calc |U y - U θ| ≤ (M + 1) / m * |y - θ| := hlip
    _ < (M + 1) / m * (ε / ((M + 1) / m)) := mul_lt_mul_of_pos_left hdist hM1
    _ = ε := by field_simp

/-! ### The shift is small, so the cotangent is defined -/

/-- The shift satisfies `0 < u − θ ≤ sin θ / m < π/2`.  (Same statement as in
`TranslatorFixedPoint`, but assuming only integrability of the profile.) -/
theorem shift_lt_pi_div_two (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b) (hm : 1 < m)
    (hmf : ∀ t, m ≤ f t) {θ u : ℝ} (hu : θ < u)
    (hval : (∫ t in θ..u, f t) = Real.sin θ) :
    0 < u - θ ∧ u - θ ≤ Real.sin θ / m ∧ u - θ < π / 2 := by
  have hm0 : (0:ℝ) < m := lt_trans zero_lt_one hm
  have hlow : m * (u - θ) ≤ Real.sin θ := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (a := θ) (b := u)
      (f := fun _ => m) (g := f) hu.le _root_.intervalIntegrable_const (hint θ u)
      (fun t _ => hmf t)
    rw [hval] at h
    simpa [mul_comm] using h
  have hle : u - θ ≤ Real.sin θ / m := by
    rw [le_div_iff₀ hm0]; linarith
  refine ⟨by linarith, hle, ?_⟩
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hdiv : Real.sin θ / m ≤ 1 := by rw [div_le_one hm0]; linarith
  have hpi : (1:ℝ) < π / 2 := by linarith [Real.pi_gt_three]
  linarith

/-! ### A bounded fixed point is continuous -/

/-- **Bootstrap: a bounded fixed point of the translator operator is
continuous.**  If `f` is interval integrable with `1 < m ≤ f ≤ M`, if `U`
solves the defining equation `∫_θ^{U θ} f = sin θ` with `θ < U θ` on `(0, π)`,
and if `f` is the fixed point `f θ = sin θ · cot (U θ − θ)` there, then `f` is
continuous on `(0, π)`. -/
theorem fixedPoint_continuousOn (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hm : 1 < m) (hmf : ∀ t, m ≤ f t) (hfM : ∀ t, f t ≤ M) {U : ℝ → ℝ}
    (hlt : ∀ θ ∈ Ioo 0 π, θ < U θ)
    (hU : ∀ θ ∈ Ioo 0 π, (∫ t in θ..U θ, f t) = Real.sin θ)
    (hfix : ∀ θ ∈ Ioo 0 π,
      f θ = Real.sin θ * (Real.cos (U θ - θ) / Real.sin (U θ - θ))) :
    ContinuousOn f (Ioo 0 π) := by
  have hm0 : (0:ℝ) < m := lt_trans zero_lt_one hm
  have hUc : ContinuousOn U (Ioo 0 π) := shift_continuousOn hint hm0 hmf hfM hU
  have hD : ContinuousOn (fun θ => U θ - θ) (Ioo 0 π) := hUc.sub continuousOn_id
  have hne : ∀ θ ∈ Ioo 0 π, Real.sin (U θ - θ) ≠ 0 := by
    intro θ hθ
    obtain ⟨hpos, -, hhalf⟩ := shift_lt_pi_div_two hint hm hmf (hlt θ hθ) (hU θ hθ)
    have : 0 < Real.sin (U θ - θ) :=
      Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [Real.pi_pos])
    exact ne_of_gt this
  have hcont : ContinuousOn
      (fun θ => Real.sin θ * (Real.cos (U θ - θ) / Real.sin (U θ - θ))) (Ioo 0 π) := by
    refine (Real.continuous_sin.continuousOn).mul ?_
    exact (Real.continuous_cos.comp_continuousOn hD).div
      (Real.continuous_sin.comp_continuousOn hD) hne
  exact hcont.congr hfix

end TranslatorRegularity
