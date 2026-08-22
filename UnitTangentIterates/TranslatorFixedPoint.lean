import Mathlib

/-!
# The translator operator is well defined, and its fixed points

This file completes two steps of Section 3 (*A translating hairpin*) of the
paper *A Noncircular Oval with Convex Unit-Tangent Iterates* that were left
aside: the fact that the shift `D_f(θ)` used to define the translator operator

`(𝒫f)(θ) = sin θ · cot D_f(θ)`,  `∫_θ^{θ + D_f(θ)} f = sin θ`,

exists and is unique for every profile `1 < m ≤ f ≤ M`, and the last clause of
the lemma *Monotone translator operator*: a profile is a fixed point of `𝒫`
exactly when it satisfies the translator equation `D_f(θ) = arctan(sin θ/f(θ))`.

Main results:

* `sin_lt_mul_pi_sub` : `sin θ < m (π - θ)` for `θ < π` and `1 ≤ m`, which
  is what makes the defining equation solvable;
* `exists_unique_translator_shift` : there is a unique `u ∈ (θ, π)` with
  `∫_θ^u f = sin θ`;
* `translator_shift_lt_pi_div_two` : the shift `D = u - θ` satisfies
  `0 < D ≤ sin θ / m < π/2`, so `cot D` is defined and positive;
* `fixed_point_iff_arctan` : for `0 < D < π/2` and `0 < F`, the fixed-point
  equation `F = sin θ · cot D` holds iff `D = arctan (sin θ / F)`;
* `hairpin_coordinate_derivs` : the coordinate equations `X' = f cot θ`,
  `Z' = f` of a hairpin parametrized by its tangent angle.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace TranslatorFixedPoint

/-! ### Solvability of the defining equation -/

/-- For `0 < θ < π` and `1 ≤ m` one has `sin θ < m (π - θ)`; this is the
inequality that makes the defining equation of `D_f` solvable. -/
theorem sin_lt_mul_pi_sub {θ m : ℝ} (hθπ : θ < π) (hm : 1 ≤ m) :
    Real.sin θ < m * (π - θ) := by
  have hpos : 0 < π - θ := by linarith
  have h1 : Real.sin (π - θ) < π - θ := Real.sin_lt hpos
  have h2 : Real.sin θ = Real.sin (π - θ) := (Real.sin_pi_sub θ).symm
  nlinarith

variable {f : ℝ → ℝ} {θ m M : ℝ}

/-- Strict monotonicity of the accumulated mass `u ↦ ∫_θ^u f` for a profile
bounded below by `m > 0`. -/
theorem integral_strictMonoOn (hf : Continuous f) (hm0 : 0 < m) (hmf : ∀ t, m ≤ f t) :
    StrictMono fun u => ∫ t in θ..u, f t := by
  intro a b hab
  have hadd : (∫ t in θ..a, f t) + (∫ t in a..b, f t) = ∫ t in θ..b, f t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hlow : m * (b - a) ≤ ∫ t in a..b, f t := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (a := a) (b := b)
      (f := fun _ => m) (g := f) hab.le
      (_root_.intervalIntegrable_const) (hf.intervalIntegrable _ _) (fun t _ => hmf t)
    simpa [mul_comm] using h
  have : 0 < m * (b - a) := by
    apply mul_pos hm0; linarith
  linarith

/-- **The shift `D_f(θ)` is well defined**: for a continuous profile with
`1 < m ≤ f` there is a unique `u ∈ (θ, π)` with `∫_θ^u f = sin θ`. -/
theorem exists_unique_translator_shift (hf : Continuous f) (hm : 1 < m)
    (hmf : ∀ t, m ≤ f t) (hθ0 : 0 < θ) (hθπ : θ < π) :
    ∃! u : ℝ, u ∈ Ioo θ π ∧ (∫ t in θ..u, f t) = Real.sin θ := by
  set G : ℝ → ℝ := fun u => ∫ t in θ..u, f t with hG
  have hm0 : (0:ℝ) < m := lt_trans zero_lt_one hm
  have hmono : StrictMono G := integral_strictMonoOn (θ := θ) hf hm0 hmf
  have hcont : Continuous G := by
    have : ∀ u, HasDerivAt G (f u) u := fun u =>
      (hf.integral_hasStrictDerivAt θ u).hasDerivAt
    exact continuous_iff_continuousAt.mpr fun u => (this u).continuousAt
  have hGθ : G θ = 0 := by simp [hG]
  have hGπ : Real.sin θ < G π := by
    have hlow : m * (π - θ) ≤ G π := by
      have h := intervalIntegral.integral_mono_on (μ := volume) (a := θ) (b := π)
        (f := fun _ => m) (g := f) hθπ.le
        (_root_.intervalIntegrable_const) (hf.intervalIntegrable _ _) (fun t _ => hmf t)
      simpa [hG, mul_comm] using h
    exact lt_of_lt_of_le (sin_lt_mul_pi_sub hθπ hm.le) hlow
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hsub : Ioo (G θ) (G π) ⊆ G '' Ioo θ π :=
    intermediate_value_Ioo hθπ.le hcont.continuousOn
  obtain ⟨u, hu, hGu⟩ := hsub ⟨by rw [hGθ]; exact hsin, hGπ⟩
  refine ⟨u, ⟨hu, hGu⟩, ?_⟩
  rintro v ⟨-, hGv⟩
  exact hmono.injective (by simp only [hG]; rw [hGv]; exact hGu.symm)

/-- The shift is at most `sin θ / m`, hence lies in `(0, π/2)`: `cot D` is
defined and positive. -/
theorem translator_shift_lt_pi_div_two (hf : Continuous f) (hm : 1 < m)
    (hmf : ∀ t, m ≤ f t) {u : ℝ} (hu : θ < u)
    (hint : (∫ t in θ..u, f t) = Real.sin θ) :
    0 < u - θ ∧ u - θ ≤ Real.sin θ / m ∧ u - θ < π / 2 := by
  have hm0 : (0:ℝ) < m := lt_trans zero_lt_one hm
  have hlow : m * (u - θ) ≤ Real.sin θ := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (a := θ) (b := u)
      (f := fun _ => m) (g := f) hu.le
      (_root_.intervalIntegrable_const) (hf.intervalIntegrable _ _) (fun t _ => hmf t)
    rw [hint] at h
    simpa [mul_comm] using h
  have hle : u - θ ≤ Real.sin θ / m := by
    rw [le_div_iff₀ hm0]; linarith [hlow]
  refine ⟨by linarith, hle, ?_⟩
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hdiv : Real.sin θ / m ≤ 1 := by
    rw [div_le_one hm0]; linarith
  have hpi : (1:ℝ) < π / 2 := by linarith [Real.pi_gt_three]
  linarith

/-! ### Fixed points of the translator operator -/

/-- **The fixed-point equation is the translator equation**: for a shift
`0 < D < π/2` and a positive value `F`, the identity `F = sin θ · cot D` holds
if and only if `D = arctan (sin θ / F)`. -/
theorem fixed_point_iff_arctan {D F : ℝ} (hD0 : 0 < D) (hD : D < π / 2) (hF : 0 < F) :
    F = Real.sin θ * (Real.cos D / Real.sin D) ↔ D = Real.arctan (Real.sin θ / F) := by
  have hcos : 0 < Real.cos D := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hD⟩
  have hsinD : 0 < Real.sin D := Real.sin_pos_of_pos_of_lt_pi hD0 (by linarith [Real.pi_pos])
  constructor
  · intro h
    have hsθ : Real.sin θ ≠ 0 := by
      intro h0
      rw [h0] at h
      simp at h
      linarith
    have htan : Real.tan D = Real.sin θ / F := by
      rw [Real.tan_eq_sin_div_cos, h]
      field_simp
    rw [← htan, Real.arctan_tan (by linarith [Real.pi_pos]) hD]
  · intro h
    have htan : Real.tan D = Real.sin θ / F := by rw [h, Real.tan_arctan]
    rw [Real.tan_eq_sin_div_cos] at htan
    field_simp at htan ⊢
    linarith [htan]

/-! ### The coordinate equations of a hairpin -/

/-- **The coordinate equations** `X' = f cot θ`, `Z' = f` of a hairpin
parametrized by its tangent angle: if the curve has velocity `ρ(θ) τ(θ)` in the
tangent-angle parameter and `f = ρ sin θ`, then its horizontal and vertical
components satisfy `X' = f cot θ` and `Z' = f`. -/
theorem hairpin_coordinate_derivs {X Z rho : ℝ → ℝ} {θ : ℝ}
    (hX : HasDerivAt X (rho θ * Real.cos θ) θ)
    (hZ : HasDerivAt Z (rho θ * Real.sin θ) θ)
    (hsin : Real.sin θ ≠ 0) (fval : ℝ) (hf : fval = rho θ * Real.sin θ) :
    HasDerivAt X (fval * (Real.cos θ / Real.sin θ)) θ ∧ HasDerivAt Z fval θ := by
  constructor
  · have : fval * (Real.cos θ / Real.sin θ) = rho θ * Real.cos θ := by
      rw [hf]; field_simp
    rwa [this]
  · rwa [hf]

end TranslatorFixedPoint
