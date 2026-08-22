import Mathlib
import UnitTangentIterates.Translator
import UnitTangentIterates.TranslatorShiftDeriv
import UnitTangentIterates.TranslatingHairpin
import UnitTangentIterates.TranslatorSmooth

/-!
# The translation law for the translating hairpin

This file completes Section 3 of the paper *A Noncircular Oval with Convex
Unit-Tangent Iterates*: the hairpin `C` built in `TranslatingHairpin.lean` is
carried by the unit-tangent transform onto a horizontal translate of itself,

`𝒯C = C + (V, 0)`  with `V > 0`.

The statements of `Translator.lean` assume that the primitive of the profile
and the tangent-angle map `g = θ + arctan(sin θ / f)` are differentiable on all
of `ℝ`.  For the constructed profile this is false (the profile is only
continuous on `(0, π)`), so the arguments are repeated here with hypotheses
localized to `(0, π)`:

* `translator_next_deriv_on` : `f(g) g' = f + cos θ`;
* `translator_horizontal_deriv_on` : the horizontal defect
  `V(θ) = X(θ) + cos θ − X(g θ)` has vanishing derivative;
* `translator_horizontal_const_on` : hence it is constant;
* `translation_pos_on` : the constant is positive, since `−∫_{π/2}^b f cot > 0`
  for `π/2 < b < π`;
* `exists_translating_hairpin_translation` : the **translation law** for the
  hairpin of `TranslatingHairpin.exists_translating_hairpin`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace TranslatorTranslation

open Translator

/-! ### The translator equation, localized to `(0, π)` -/

variable {f A X : ℝ → ℝ}

/-- **Differentiating the translator integral equation** (local form).  Only
the values of the data on `(0, π)` are used. -/
theorem translator_next_deriv_on {g gp : ℝ → ℝ}
    (hA : ∀ t ∈ Ioo (0:ℝ) π, HasDerivAt A (f t) t)
    (hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt g (gp θ) θ)
    (hmaps : ∀ θ ∈ Ioo (0:ℝ) π, g θ ∈ Ioo (0:ℝ) π)
    (heq : ∀ θ ∈ Ioo (0:ℝ) π, A (g θ) - A θ = Real.sin θ)
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    f (g θ) * gp θ = f θ + Real.cos θ := by
  have hd1 : HasDerivAt (fun σ => A (g σ) - A σ) (f (g θ) * gp θ - f θ) θ :=
    ((hA _ (hmaps θ hθ)).comp θ (hg θ hθ)).sub (hA θ hθ)
  have hev : (fun σ => A (g σ) - A σ) =ᶠ[nhds θ] Real.sin := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with σ hσ using heq σ hσ
  have hd2 : HasDerivAt Real.sin (f (g θ) * gp θ - f θ) θ := hd1.congr_of_eventuallyEq hev.symm
  have := hd2.unique (Real.hasDerivAt_sin θ)
  linarith

/-- **The horizontal defect is locally constant** (local form). -/
theorem translator_horizontal_deriv_on {gp : ℝ → ℝ}
    (hA : ∀ t ∈ Ioo (0:ℝ) π, HasDerivAt A (f t) t)
    (hfpos : ∀ t, 0 < f t)
    (hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt (next f) (gp θ) θ)
    (heq : ∀ θ ∈ Ioo (0:ℝ) π, A (next f θ) - A θ = Real.sin θ)
    (hmaps : ∀ θ ∈ Ioo (0:ℝ) π, next f θ ∈ Ioo (0:ℝ) π)
    (hX : ∀ t ∈ Ioo (0:ℝ) π, HasDerivAt X (f t * (Real.cos t / Real.sin t)) t)
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    HasDerivAt (fun σ => X σ + Real.cos σ - X (next f σ)) 0 θ := by
  have hgθ : next f θ ∈ Ioo (0:ℝ) π := hmaps θ hθ
  have hXg : HasDerivAt (fun σ => X (next f σ))
      ((f (next f θ) * (Real.cos (next f θ) / Real.sin (next f θ))) * gp θ) θ :=
    (hX _ hgθ).comp θ (hg θ hθ)
  have htotal : HasDerivAt (fun σ => X σ + Real.cos σ - X (next f σ))
      (f θ * (Real.cos θ / Real.sin θ) + (-Real.sin θ)
        - (f (next f θ) * (Real.cos (next f θ) / Real.sin (next f θ))) * gp θ) θ :=
    ((hX θ hθ).add (Real.hasDerivAt_cos θ)).sub hXg
  have key := translator_next_deriv_on hA hg hmaps heq hθ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsg : 0 < Real.sin (next f θ) := Real.sin_pos_of_pos_of_lt_pi hgθ.1 hgθ.2
  have hrel : f θ * Real.sin (steer f θ) = Real.sin θ * Real.cos (steer f θ) :=
    mul_sin_steer hθ (hfpos θ)
  have hcosg : Real.cos (next f θ)
      = Real.cos θ * Real.cos (steer f θ) - Real.sin θ * Real.sin (steer f θ) := by
    rw [next, Real.cos_add]
  have hsing : Real.sin (next f θ)
      = Real.sin θ * Real.cos (steer f θ) + Real.cos θ * Real.sin (steer f θ) := by
    rw [next, Real.sin_add]
  have hzero : f θ * (Real.cos θ / Real.sin θ) + (-Real.sin θ)
      - (f (next f θ) * (Real.cos (next f θ) / Real.sin (next f θ))) * gp θ = 0 := by
    have hswap : (f (next f θ) * (Real.cos (next f θ) / Real.sin (next f θ))) * gp θ
        = (Real.cos (next f θ) / Real.sin (next f θ)) * (f θ + Real.cos θ) := by
      rw [← key]
      field_simp
    have hfirst : f θ * (Real.cos θ / Real.sin θ) = f θ * Real.cos θ / Real.sin θ := by
      ring
    rw [hswap, hfirst, hcosg, hsing]
    have hden : Real.sin θ * Real.cos (steer f θ) + Real.cos θ * Real.sin (steer f θ) ≠ 0 := by
      rw [← hsing]; exact ne_of_gt hsg
    exact horizontal_algebra (hfpos θ) hs hrel hden
  rw [hzero] at htotal
  exact htotal

theorem pi_div_two_mem : (π / 2) ∈ Ioo (0:ℝ) π := by
  constructor <;> linarith [Real.pi_pos]

/-- **The horizontal defect is constant on `(0, π)`** (local form of Lemma 3.1). -/
theorem translator_horizontal_const_on {gp : ℝ → ℝ}
    (hA : ∀ t ∈ Ioo (0:ℝ) π, HasDerivAt A (f t) t)
    (hfpos : ∀ t, 0 < f t)
    (hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt (next f) (gp θ) θ)
    (heq : ∀ θ ∈ Ioo (0:ℝ) π, A (next f θ) - A θ = Real.sin θ)
    (hmaps : ∀ θ ∈ Ioo (0:ℝ) π, next f θ ∈ Ioo (0:ℝ) π)
    (hX : ∀ t ∈ Ioo (0:ℝ) π, HasDerivAt X (f t * (Real.cos t / Real.sin t)) t)
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    X θ + Real.cos θ - X (next f θ)
      = X (π/2) - X (next f (π/2)) := by
  set W : ℝ → ℝ := fun σ => X σ + Real.cos σ - X (next f σ) with hW
  have hderiv : ∀ σ ∈ Ioo (0:ℝ) π, HasDerivAt W 0 σ := fun σ hσ =>
    translator_horizontal_deriv_on hA hfpos hg heq hmaps hX hσ
  have hconst : W θ = W (π/2) := by
    refine (convex_Ioo (0:ℝ) π).is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (f := W) ?_ ?_ hθ
      pi_div_two_mem
    · exact fun z hz => ((hderiv z hz).differentiableAt).differentiableWithinAt
    · intro z hz
      rw [((hderiv z hz).hasFDerivAt.hasFDerivWithinAt).fderivWithin
        (isOpen_Ioo.uniqueDiffOn z hz)]
      ext
      simp
  simpa [hW, Real.cos_pi_div_two] using hconst

/-! ### Positivity of the translation -/

/-- **The translation is positive** (local form of
`HairpinIteration.translation_pos`, for a profile continuous only on
`(0, π)`). -/
theorem translation_pos_on {b : ℝ} (hf : ContinuousOn f (Ioo 0 π)) (hfpos : ∀ t, 0 < f t)
    (hb1 : π / 2 < b) (hb2 : b < π) :
    0 < -∫ t in (π / 2)..b, f t * (Real.cos t / Real.sin t) := by
  have hsub : uIcc (π/2) b ⊆ Ioo (0:ℝ) π := by
    rw [uIcc_of_le hb1.le]
    intro t ht
    exact ⟨by linarith [Real.pi_pos, ht.1], by linarith [ht.2]⟩
  have hsin : ∀ t ∈ Ioo (π / 2) b, 0 < Real.sin t := by
    intro t ht
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, ht.1]) (by linarith [ht.2])
  have hcos : ∀ t ∈ Ioo (π / 2) b, Real.cos t < 0 := fun t ht =>
    Real.cos_neg_of_pi_div_two_lt_of_lt ht.1 (by linarith [Real.pi_pos, ht.2])
  have hneg : ∀ t ∈ Ioo (π / 2) b, 0 < -(f t * (Real.cos t / Real.sin t)) := by
    intro t ht
    have h1 : Real.cos t / Real.sin t < 0 := div_neg_of_neg_of_pos (hcos t ht) (hsin t ht)
    have := mul_neg_of_pos_of_neg (hfpos t) h1
    linarith
  have hcont : ContinuousOn (fun t => -(f t * (Real.cos t / Real.sin t))) (uIcc (π / 2) b) := by
    refine ContinuousOn.neg ((hf.mono hsub).mul ?_)
    refine ContinuousOn.div Real.continuous_cos.continuousOn Real.continuous_sin.continuousOn ?_
    intro t ht
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (hsub ht).1 (hsub ht).2)
  have hpos : 0 < ∫ t in (π / 2)..b, -(f t * (Real.cos t / Real.sin t)) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hcont.intervalIntegrable hneg hb1
  rwa [intervalIntegral.integral_neg] at hpos

/-! ### The translation law for the constructed hairpin -/

/-- **The translating hairpin translates.**  For every `0 < ε ≤ 1/10` the
hairpin `C = (X, Z)` of `TranslatingHairpin.exists_translating_hairpin` is
mapped by the unit-tangent transform onto its own translate by a *positive*
horizontal vector: with `g(θ) = θ + arctan(sin θ / f(θ))` the tangent-angle
map,

`C(θ) + (cos θ, sin θ) = C(g θ) + (V, 0)`,  `V > 0`,

for every `θ ∈ (0, π)`. -/
theorem exists_translating_hairpin_translation {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    ∃ f : ℝ → ℝ, ∃ V : ℝ, 0 < V ∧
      (∀ t, Barriers.fMinus ε t ≤ f t) ∧ (∀ t, f t ≤ Barriers.fPlus ε t) ∧
      ContinuousOn f (Ioo 0 π) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, Translator.next f θ ∈ Ioo θ π) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, (∫ t in θ..(Translator.next f θ), f t) = Real.sin θ) ∧
      (∀ n : ℕ, ContDiffOn ℝ n f (Ioo 0 π)) ∧
      (∀ θ ∈ Ioo (0:ℝ) π,
        (Hairpin.hairpinX f θ + Real.cos θ, Hairpin.hairpinZ f θ + Real.sin θ)
          = (Hairpin.hairpinX f (Translator.next f θ) + V,
             Hairpin.hairpinZ f (Translator.next f θ))) := by
  obtain ⟨f, hmeas, hfl, hfu, hcont, hmapsShift, hintEq, harctan, hfixShift⟩ :=
    BarrierEstimates.exists_hairpin_profile hε hε'
  have hm1 : 1 < ε⁻¹ - ε := BarrierEstimates.m_gt_one hε hε'
  have hm0 : (0:ℝ) < ε⁻¹ - ε := lt_trans zero_lt_one hm1
  have hlow : ∀ t, ε⁻¹ - ε ≤ f t := fun t =>
    le_trans ((Barriers.fMinus_min hε).1 t) (hfl t)
  have hup : ∀ t, f t ≤ ε⁻¹ + 4 / 3 + 3 * ε := fun t =>
    le_trans (hfu t) ((BarrierEstimates.profile_fPlus hε).upper t)
  have hfpos : ∀ t, 0 < f t := fun t => lt_of_lt_of_le hm0 (hlow t)
  have hprof : TranslatorOperator.Profile (ε⁻¹ - ε) (ε⁻¹ + 4 / 3 + 3 * ε) f :=
    ⟨hmeas, hlow, hup⟩
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b := hprof.int
  -- the tangent-angle map is the mass time
  have hnext : ∀ θ ∈ Ioo (0:ℝ) π, Translator.next f θ = θ + TranslatorOperator.shift f θ := by
    intro θ hθ
    rw [Translator.next, Translator.steer, harctan θ hθ]
  have hmaps' : ∀ θ ∈ Ioo (0:ℝ) π, Translator.next f θ ∈ Ioo θ π := by
    intro θ hθ; rw [hnext θ hθ]; exact hmapsShift θ hθ
  have hmaps : ∀ θ ∈ Ioo (0:ℝ) π, Translator.next f θ ∈ Ioo (0:ℝ) π := by
    intro θ hθ
    exact ⟨lt_trans hθ.1 (hmaps' θ hθ).1, (hmaps' θ hθ).2⟩
  have hU : ∀ θ ∈ Ioo (0:ℝ) π, (∫ t in θ..(Translator.next f θ), f t) = Real.sin θ := by
    intro θ hθ; rw [hnext θ hθ]; exact hintEq θ hθ
  -- the primitive and its increments
  have hAsub : ∀ x y : ℝ, Hairpin.hairpinZ f y - Hairpin.hairpinZ f x = ∫ t in x..y, f t := by
    intro x y
    simpa [Hairpin.hairpinZ] using
      intervalIntegral.integral_interval_sub_left (hint (π/2) y) (hint (π/2) x)
  have heq : ∀ θ ∈ Ioo (0:ℝ) π,
      Hairpin.hairpinZ f (Translator.next f θ) - Hairpin.hairpinZ f θ = Real.sin θ := by
    intro θ hθ; rw [hAsub]; exact hU θ hθ
  -- the tangent-angle map is differentiable
  have hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt (Translator.next f)
      ((f θ + Real.cos θ) / f (Translator.next f θ)) θ := fun θ hθ =>
    TranslatorShift.hasDerivAt_shift hint hAsub hmeas hm0 hlow hcont hU hmaps hθ
  have hA : ∀ t ∈ Ioo (0:ℝ) π, HasDerivAt (Hairpin.hairpinZ f) (f t) t := fun t ht =>
    HairpinOn.hasDerivAt_hairpinZ' hcont ht
  have hX : ∀ t ∈ Ioo (0:ℝ) π,
      HasDerivAt (Hairpin.hairpinX f) (f t * (Real.cos t / Real.sin t)) t := fun t ht =>
    HairpinOn.hasDerivAt_hairpinX' hcont ht
  -- the translation
  set b : ℝ := Translator.next f (π/2) with hb
  have hbmem : b ∈ Ioo (π/2) π := hmaps' _ pi_div_two_mem
  set V : ℝ := Hairpin.hairpinX f (π/2) - Hairpin.hairpinX f b with hV
  have hX0 : Hairpin.hairpinX f (π/2) = 0 := by simp [Hairpin.hairpinX]
  have hVpos : 0 < V := by
    rw [hV, hX0, zero_sub]
    simpa [Hairpin.hairpinX] using translation_pos_on hcont hfpos hbmem.1 hbmem.2
  -- the profile is smooth on `(0, π)`
  have hsinD : ∀ θ ∈ Ioo (0:ℝ) π, Real.sin (Translator.next f θ - θ) ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Translator.next f θ - θ := sub_pos.mpr (hmaps' θ hθ).1
    have h2 : Translator.next f θ - θ < π := by
      have := (hmaps' θ hθ).2; linarith [hθ.1]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  have hfix : ∀ θ ∈ Ioo (0:ℝ) π, f θ = Real.sin θ *
      (Real.cos (Translator.next f θ - θ) / Real.sin (Translator.next f θ - θ)) := by
    intro θ hθ
    have hd : Translator.next f θ - θ = TranslatorOperator.shift f θ := by
      rw [hnext θ hθ]; ring
    rw [hd]
    exact hfixShift θ hθ
  have hsmooth : ∀ n : ℕ, ContDiffOn ℝ n f (Ioo 0 π) := fun n =>
    (TranslatorSmooth.contDiffOn_of_fixedPoint hcont hg
      (fun θ hθ => hmaps θ hθ) (fun t _ => ne_of_gt (hfpos t)) hsinD hfix n).1
  refine ⟨f, V, hVpos, hfl, hfu, hcont, hmaps', hU, hsmooth, ?_⟩
  intro θ hθ
  have hconst := translator_horizontal_const_on hA hfpos hg heq hmaps hX hθ
  have hZ := heq θ hθ
  simp only [Prod.mk.injEq]
  constructor
  · rw [hV]; linarith [hconst]
  · linarith [hZ]

end TranslatorTranslation
