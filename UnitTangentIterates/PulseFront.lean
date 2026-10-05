module

public import UnitTangentIterates.PulseRear
public import UnitTangentIterates.HairpinCurve

/-!
# Lemma 3.5, step 2: identities for the translated front

For a translator profile `f` (`TranslatorEq f`), the front point attached to the rear point of
tangent angle `θ` has tangent angle `g(θ) = θ + d(θ)`, `d = arctan (sin θ / f θ)`.  With
`K = sin θ / f θ` (the rear curvature) and `g' = (f θ + cos θ) / f (g θ)`:

* `sin (g θ) / f (g θ) = K g' / √(1 + K²)` — the front curvature (`front_curv_identity`);
* `f (g θ) / sin (g θ) · g' · K = √(1 + K²)` — the ratio of front and rear arclength
  (`front_speed_identity`).
-/

@[expose] public section

namespace Ovals

open Real Set

variable {f : ℝ → ℝ} {m : ℝ}

/-- The derivative `g' = (f θ + cos θ) / f (g θ)` of the translator angle map. -/
noncomputable def hairpinGd (f : ℝ → ℝ) (θ : ℝ) : ℝ := (f θ + Real.cos θ) / f (hairpinG f θ)

theorem hairpinG_mem_Ioo (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) : hairpinG f θ ∈ Ioo 0 π := by
  have h := hairpinG_mem hm hf hθ
  exact ⟨by linarith [h.1, hθ.1], h.2⟩

theorem hasDerivAt_hairpinG_gd (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ)
    (hfd : DifferentiableOn ℝ f (Ioo 0 π)) (hT : TranslatorEq f) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (hairpinG f) (hairpinGd f θ) θ := by
  obtain ⟨g', hg, hfg⟩ := hasDerivAt_hairpinG hm hf hfd hT hθ
  have hpos : 0 < f (hairpinG f θ) := by linarith [hf _ (hairpinG_mem_Ioo hm hf hθ)]
  convert hg using 1
  unfold hairpinGd
  rw [← hfg]; field_simp

theorem hairpinGd_bounds {M : ℝ} (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ)
    (hfM : ∀ θ ∈ Ioo 0 π, f θ ≤ M) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 < hairpinGd f θ ∧ hairpinGd f θ ≤ (M + 1) / m := by
  have hg := hairpinG_mem_Ioo hm hf hθ
  have h1 := hf _ hg
  have h2 := hfM θ hθ
  have h3 := hf θ hθ
  have hc1 := Real.neg_one_le_cos θ
  have hc2 := Real.cos_le_one θ
  have hm0 : 0 < m := by linarith
  unfold hairpinGd
  constructor
  · exact div_pos (by linarith) (by linarith)
  · rw [div_le_div_iff₀ (by linarith) hm0]
    nlinarith

theorem sin_hairpinG (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    Real.sin (hairpinG f θ) = Real.sin θ * (f θ + Real.cos θ) /
      (f θ * √(1 + (Real.sin θ / f θ) ^ 2)) := by
  have hf0 : 0 < f θ := by linarith [hf θ hθ]
  have hsq : 0 < √(1 + (Real.sin θ / f θ) ^ 2) := Real.sqrt_pos.2 (by positivity)
  unfold hairpinG hairpinD
  rw [Real.sin_add, Real.sin_arctan, Real.cos_arctan]
  field_simp

/-- The front curvature identity `sin (g θ) / f (g θ) = K g' / √(1 + K²)`. -/
theorem front_curv_identity (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) :
    Real.sin (hairpinG f θ) / f (hairpinG f θ) =
      (Real.sin θ / f θ) * hairpinGd f θ / √(1 + (Real.sin θ / f θ) ^ 2) := by
  have hf0 : 0 < f θ := by linarith [hf θ hθ]
  have hg0 : 0 < f (hairpinG f θ) := by linarith [hf _ (hairpinG_mem_Ioo hm hf hθ)]
  have hc : 0 < f θ + Real.cos θ := by linarith [Real.neg_one_le_cos θ, hf θ hθ]
  have hsq : 0 < √(1 + (Real.sin θ / f θ) ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [sin_hairpinG hm hf hθ]
  unfold hairpinGd
  field_simp

/-- The arclength ratio identity `f (g θ) / sin (g θ) · g' · K = √(1 + K²)`. -/
theorem front_speed_identity (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) :
    f (hairpinG f θ) / Real.sin (hairpinG f θ) * (hairpinGd f θ * (Real.sin θ / f θ)) =
      √(1 + (Real.sin θ / f θ) ^ 2) := by
  have hf0 : 0 < f θ := by linarith [hf θ hθ]
  have hg0 : 0 < f (hairpinG f θ) := by linarith [hf _ (hairpinG_mem_Ioo hm hf hθ)]
  have hc : 0 < f θ + Real.cos θ := by linarith [Real.neg_one_le_cos θ, hf θ hθ]
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsq : 0 < √(1 + (Real.sin θ / f θ) ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [sin_hairpinG hm hf hθ]
  unfold hairpinGd
  field_simp

end Ovals

end
