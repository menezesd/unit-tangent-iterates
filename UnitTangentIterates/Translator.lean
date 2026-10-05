module

public import UnitTangentIterates.Circle

/-!
# The translating hairpin: the translator equation (Lemma 3.1)

A hairpin `C = (X, Z)` is parametrized by its tangent angle `θ ∈ (0, π)` with
`C'(θ) = ρ(θ) τ(θ)`.  Writing `f = ρ sin θ` we get `X' = f cot θ`, `Z' = f`.
The tangent angle of `C + τ` at the point with parameter `θ` is
`g(θ) = θ + d(θ)`, `d(θ) = arctan (sin θ / f θ)`.

Lemma 3.1: if `1 < m ≤ f ≤ M` and `∫_θ^{θ + d(θ)} f = sin θ` on `(0, π)`, then `g` is an
increasing diffeomorphism of `(0, π)` and `C(θ) + τ(θ) = C(g(θ)) + (V, 0)` for a constant `V`,
i.e. `𝒯 C` is the horizontal translate `C + (V, 0)`.
-/

@[expose] public section

namespace Ovals

open Real Set

/-- The steering angle of the hairpin, `d(θ) = arctan (sin θ / f θ)`. -/
noncomputable def hairpinD (f : ℝ → ℝ) (θ : ℝ) : ℝ := Real.arctan (Real.sin θ / f θ)

/-- The tangent angle `g(θ) = θ + d(θ)` of `C + τ`. -/
noncomputable def hairpinG (f : ℝ → ℝ) (θ : ℝ) : ℝ := θ + hairpinD f θ

/-- The horizontal coordinate `X(θ) = ∫_{π/2}^θ f(t) cot t dt` of the hairpin. -/
noncomputable def hairpinX (f : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ t in (π / 2)..θ, f t * Real.cot t

/-- The vertical coordinate `Z(θ) = ∫_{π/2}^θ f(t) dt` of the hairpin. -/
noncomputable def hairpinZ (f : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ t in (π / 2)..θ, f t

/-- The hairpin `C = X + i Z` (parametrized by tangent angle). -/
noncomputable def hairpin (f : ℝ → ℝ) (θ : ℝ) : ℂ :=
  (hairpinX f θ : ℂ) + (hairpinZ f θ : ℂ) * Complex.I

/-- The translator equation (3.3): `∫_θ^{θ + d(θ)} f = sin θ` on `(0, π)`. -/
def TranslatorEq (f : ℝ → ℝ) : Prop :=
  ∀ θ ∈ Ioo 0 π, ∫ t in θ..hairpinG f θ, f t = Real.sin θ

theorem arctan_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · have h1 : 0 < Real.arctan x := Real.arctan_pos.2 h
    have h2 : Real.arctan x < π / 2 := Real.arctan_lt_pi_div_two x
    have := Real.lt_tan h1 h2
    rw [Real.tan_arctan] at this
    exact this.le

variable {f : ℝ → ℝ} {m M : ℝ}

/-- `0 < d(θ) ≤ sin θ / m < π - θ`, so `θ < g(θ) < π`. -/
theorem hairpinD_bounds (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) :
    0 < hairpinD f θ ∧ hairpinD f θ ≤ Real.sin θ / m ∧ Real.sin θ / m < π - θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hfθ : m ≤ f θ := hf θ hθ
  have hf0 : 0 < f θ := by linarith
  refine ⟨Real.arctan_pos.2 (div_pos hs hf0), ?_, ?_⟩
  · calc hairpinD f θ ≤ Real.sin θ / f θ := arctan_le_self_of_nonneg (div_pos hs hf0).le
      _ ≤ Real.sin θ / m := div_le_div_of_nonneg_left hs.le (by linarith) hfθ
  · have h1 : Real.sin θ ≤ π - θ := by
      rw [← Real.sin_pi_sub]; exact Real.sin_le (by linarith [hθ.2])
    have h2 : Real.sin θ / m < Real.sin θ := div_lt_self hs hm
    linarith

theorem hairpinG_mem (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) : hairpinG f θ ∈ Ioo θ π := by
  obtain ⟨h1, h2, h3⟩ := hairpinD_bounds hm hf hθ
  unfold hairpinG
  constructor <;> linarith

theorem intervalIntegrable_of_Ioo {h : ℝ → ℝ} (hc : ContinuousOn h (Ioo 0 π)) {a b : ℝ}
    (ha : a ∈ Ioo 0 π) (hb : b ∈ Ioo 0 π) : IntervalIntegrable h MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply hc.mono
  intro x hx
  rw [Set.mem_uIcc] at hx
  constructor <;> rcases hx with h | h <;> linarith [ha.1, ha.2, hb.1, hb.2, h.1, h.2]

theorem hasDerivAt_integral_of_Ioo {h : ℝ → ℝ} (hc : ContinuousOn h (Ioo 0 π)) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) : HasDerivAt (fun x => ∫ t in (π / 2)..x, h t) (h θ) θ := by
  have hpi : π / 2 ∈ Ioo 0 π := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  exact intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_of_Ioo hc hpi hθ)
    (hc.stronglyMeasurableAtFilter isOpen_Ioo θ hθ)
    (hc.continuousAt (isOpen_Ioo.mem_nhds hθ))

theorem hasDerivAt_hairpinZ (hfc : ContinuousOn f (Ioo 0 π)) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (hairpinZ f) (f θ) θ :=
  hasDerivAt_integral_of_Ioo hfc hθ

theorem continuousOn_cot_Ioo : ContinuousOn Real.cot (Ioo 0 π) := by
  have : Real.cot = fun x => Real.cos x / Real.sin x := funext Real.cot_eq_cos_div_sin
  rw [this]
  exact Real.continuous_cos.continuousOn.div Real.continuous_sin.continuousOn
    (fun x hx => (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne')

theorem hasDerivAt_hairpinX (hfc : ContinuousOn f (Ioo 0 π)) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (hairpinX f) (f θ * Real.cot θ) θ :=
  hasDerivAt_integral_of_Ioo (h := fun t => f t * Real.cot t) (hfc.mul continuousOn_cot_Ioo) hθ

theorem integral_eq_hairpinZ_sub (hfc : ContinuousOn f (Ioo 0 π)) {a b : ℝ}
    (ha : a ∈ Ioo 0 π) (hb : b ∈ Ioo 0 π) :
    ∫ t in a..b, f t = hairpinZ f b - hairpinZ f a := by
  have hpi : π / 2 ∈ Ioo 0 π := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  unfold hairpinZ
  rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_of_Ioo hfc hpi hb)
    (intervalIntegrable_of_Ioo hfc hpi ha)]

theorem differentiableAt_hairpinG (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ) (hm : 1 < m)
    (hfd : DifferentiableOn ℝ f (Ioo 0 π)) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    DifferentiableAt ℝ (hairpinG f) θ := by
  have hfθ : DifferentiableAt ℝ f θ := hfd.differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hne : f θ ≠ 0 := by linarith [hf θ hθ]
  unfold hairpinG hairpinD
  exact differentiableAt_id.add ((Real.differentiable_sin θ).div hfθ hne).arctan

/-- Differentiating the translator equation: `f(g) g' = f + cos θ`. -/
theorem hasDerivAt_hairpinG (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ)
    (hfd : DifferentiableOn ℝ f (Ioo 0 π)) (hT : TranslatorEq f) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ∃ g' : ℝ, HasDerivAt (hairpinG f) g' θ ∧ f (hairpinG f θ) * g' = f θ + Real.cos θ := by
  have hfc : ContinuousOn f (Ioo 0 π) := hfd.continuousOn
  have hg := (differentiableAt_hairpinG hf hm hfd hθ).hasDerivAt
  refine ⟨_, hg, ?_⟩
  have hgθ := hairpinG_mem hm hf hθ
  have hgθ' : hairpinG f θ ∈ Ioo 0 π := ⟨by linarith [hgθ.1, hθ.1], hgθ.2⟩
  have h1 := ((hasDerivAt_hairpinZ hfc hgθ').comp θ hg).sub (hasDerivAt_hairpinZ hfc hθ)
  have hev : (fun y => Real.sin y) =ᶠ[nhds θ]
      (fun y => hairpinZ f (hairpinG f y) - hairpinZ f y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
    have hgy := hairpinG_mem hm hf hy
    rw [← hT y hy, integral_eq_hairpinZ_sub hfc hy ⟨by linarith [hgy.1, hy.1], hgy.2⟩]
  have h2 := h1.congr_of_eventuallyEq hev
  have := h2.unique (Real.hasDerivAt_sin θ)
  linarith

/-- The cotangent identity `(f + cos θ) cot g = f cot θ - sin θ`. -/
theorem cot_hairpinG (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) :
    (f θ + Real.cos θ) * Real.cot (hairpinG f θ) = f θ * Real.cot θ - Real.sin θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hf0 : 0 < f θ := by linarith [hf θ hθ]
  have hfc : 0 < f θ + Real.cos θ := by linarith [Real.neg_one_le_cos θ, hf θ hθ]
  set d := hairpinD f θ with hd
  have hcd : 0 < Real.cos d := Real.cos_arctan_pos _
  have htan : Real.tan d = Real.sin θ / f θ := Real.tan_arctan _
  have hsd : Real.sin d = Real.sin θ / f θ * Real.cos d := by
    rw [← htan, Real.tan_eq_sin_div_cos]; field_simp
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, hairpinG, ← hd, Real.cos_add,
    Real.sin_add, hsd]
  have hden : Real.sin θ * Real.cos d + Real.cos θ * (Real.sin θ / f θ * Real.cos d) ≠ 0 := by
    have : Real.sin θ * Real.cos d + Real.cos θ * (Real.sin θ / f θ * Real.cos d) =
        Real.cos d * Real.sin θ * (f θ + Real.cos θ) / f θ := by field_simp
    rw [this]; positivity
  field_simp

/-- **Lemma 3.1 (a).** `g` is a strictly increasing bijection of `(0, π)` onto itself with
positive derivative. -/
theorem hairpinG_strictMonoOn (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ)
    (hfd : DifferentiableOn ℝ f (Ioo 0 π)) (hT : TranslatorEq f) :
    StrictMonoOn (hairpinG f) (Ioo 0 π) ∧ MapsTo (hairpinG f) (Ioo 0 π) (Ioo 0 π) ∧
      SurjOn (hairpinG f) (Ioo 0 π) (Ioo 0 π) ∧
      ∀ θ ∈ Ioo 0 π, ∃ g' > 0, HasDerivAt (hairpinG f) g' θ := by
  have hderiv : ∀ θ ∈ Ioo 0 π, ∃ g' > 0, HasDerivAt (hairpinG f) g' θ := by
    intro θ hθ
    obtain ⟨g', hg, hfg⟩ := hasDerivAt_hairpinG hm hf hfd hT hθ
    have hgθ := hairpinG_mem hm hf hθ
    have hpos : 0 < f (hairpinG f θ) := by
      linarith [hf _ ⟨by linarith [hgθ.1, hθ.1], hgθ.2⟩]
    have : 0 < f θ + Real.cos θ := by linarith [Real.neg_one_le_cos θ, hf θ hθ]
    refine ⟨g', ?_, hg⟩
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hcont : ContinuousOn (hairpinG f) (Ioo 0 π) := fun θ hθ =>
    (differentiableAt_hairpinG hf hm hfd hθ).continuousAt.continuousWithinAt
  have hmapsto : MapsTo (hairpinG f) (Ioo 0 π) (Ioo 0 π) := fun θ hθ => by
    have := hairpinG_mem hm hf hθ
    exact ⟨by linarith [this.1, hθ.1], this.2⟩
  refine ⟨?_, hmapsto, ?_, hderiv⟩
  · apply strictMonoOn_of_deriv_pos (convex_Ioo 0 π) hcont
    intro θ hθ
    rw [interior_Ioo] at hθ
    obtain ⟨g', hg', hg⟩ := hderiv θ hθ
    rw [hg.deriv]; exact hg'
  · intro y hy
    have hy2 : y / 2 ∈ Ioo 0 π := ⟨by linarith [hy.1], by linarith [hy.1, hy.2]⟩
    have h1 : hairpinG f (y / 2) ≤ y := by
      obtain ⟨_, h2, _⟩ := hairpinD_bounds hm hf hy2
      have hs : Real.sin (y / 2) ≤ y / 2 := Real.sin_le (by linarith [hy.1])
      have hs0 : 0 < Real.sin (y / 2) := Real.sin_pos_of_pos_of_lt_pi hy2.1 hy2.2
      have : Real.sin (y / 2) / m ≤ Real.sin (y / 2) := div_le_self hs0.le hm.le
      unfold hairpinG; linarith
    have h2 : y ≤ hairpinG f y := (hairpinG_mem hm hf hy).1.le
    have hsub : Icc (y / 2) y ⊆ Ioo 0 π := fun x hx =>
      ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
    obtain ⟨θ, hθ, hθy⟩ := intermediate_value_Icc (by linarith [hy.1]) (hcont.mono hsub)
      ⟨h1, h2⟩
    exact ⟨θ, hsub hθ, hθy⟩

/-- **Lemma 3.1 (b).** The translation law `C(θ) + τ(θ) = C(g(θ)) + (V, 0)`. -/
theorem hairpin_translation (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ)
    (hfd : DifferentiableOn ℝ f (Ioo 0 π)) (hT : TranslatorEq f) :
    ∃ V : ℝ, ∀ θ ∈ Ioo 0 π, hairpin f θ + tau θ = hairpin f (hairpinG f θ) + V := by
  have hfc : ContinuousOn f (Ioo 0 π) := hfd.continuousOn
  set Φ := fun θ => hairpinX f θ + Real.cos θ - hairpinX f (hairpinG f θ) with hΦ
  have hΦd : ∀ θ ∈ Ioo 0 π, HasDerivAt Φ 0 θ := by
    intro θ hθ
    obtain ⟨g', hg, hfg⟩ := hasDerivAt_hairpinG hm hf hfd hT hθ
    have hgθ := hairpinG_mem hm hf hθ
    have hgθ' : hairpinG f θ ∈ Ioo 0 π := ⟨by linarith [hgθ.1, hθ.1], hgθ.2⟩
    have h := ((hasDerivAt_hairpinX hfc hθ).add (Real.hasDerivAt_cos θ)).sub
      ((hasDerivAt_hairpinX hfc hgθ').comp θ hg)
    convert h using 1
    have hcot := cot_hairpinG hm hf hθ
    have : f (hairpinG f θ) * Real.cot (hairpinG f θ) * g' =
        (f θ + Real.cos θ) * Real.cot (hairpinG f θ) := by rw [← hfg]; ring
    linarith
  have hconst : ∀ θ ∈ Ioo 0 π, Φ θ = Φ (π / 2) := by
    intro θ hθ
    have hpi : π / 2 ∈ Ioo 0 π := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun x hx => (hΦd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hΦd x hx).deriv) hθ hpi
  refine ⟨Φ (π / 2), fun θ hθ => ?_⟩
  have hgθ := hairpinG_mem hm hf hθ
  have hgθ' : hairpinG f θ ∈ Ioo 0 π := ⟨by linarith [hgθ.1, hθ.1], hgθ.2⟩
  have hre := hconst θ hθ
  have him : hairpinZ f θ + Real.sin θ = hairpinZ f (hairpinG f θ) := by
    rw [← hT θ hθ, integral_eq_hairpinZ_sub hfc hθ hgθ']; ring
  have hre' : hairpinX f θ + Real.cos θ - hairpinX f (hairpinG f θ) = Φ (π / 2) := hre
  apply Complex.ext
  · simp [hairpin, tau_eq, -Complex.ofReal_cos, -Complex.ofReal_sin]; linarith
  · simp [hairpin, tau_eq, -Complex.ofReal_cos, -Complex.ofReal_sin]; linarith

theorem hasDerivAt_hairpin (hfc : ContinuousOn f (Ioo 0 π)) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (hairpin f) (((f θ / Real.sin θ : ℝ) : ℂ) * tau θ) θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have h := ((hasDerivAt_hairpinX hfc hθ).ofReal_comp).add
    (((hasDerivAt_hairpinZ hfc hθ).ofReal_comp).mul_const Complex.I)
  convert h using 1
  rw [tau_eq, Real.cot_eq_cos_div_sin]
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  have : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp

/-- **Lemma 3.1, curve form.** `𝒯 C = C + (V, 0)`: the unit-tangent transform of the hairpin,
evaluated at the point with tangent angle `θ`, is the point of the translated hairpin with
tangent angle `g(θ)`. -/
theorem unitTangentTransform_hairpin (hm : 1 < m) (hf : ∀ θ ∈ Ioo 0 π, m ≤ f θ)
    (hfd : DifferentiableOn ℝ f (Ioo 0 π)) (hT : TranslatorEq f) :
    ∃ V : ℝ, ∀ θ ∈ Ioo 0 π,
      unitTangentTransform (hairpin f) θ = hairpin f (hairpinG f θ) + V := by
  obtain ⟨V, hV⟩ := hairpin_translation hm hf hfd hT
  refine ⟨V, fun θ hθ => ?_⟩
  rw [← hV θ hθ]
  unfold unitTangentTransform
  rw [(hasDerivAt_hairpin hfd.continuousOn hθ).deriv]
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hpos : 0 < f θ / Real.sin θ := div_pos (by linarith [hf θ hθ]) hs
  rw [norm_mul, norm_tau, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  have : ((f θ / Real.sin θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

end Ovals

end
