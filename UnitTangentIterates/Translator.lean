import Mathlib

/-!
# The translator equation

This file formalizes Lemma 3.1 (*Translator equation*) of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*, together with the
order-preserving properties of the translator operator `𝒫` (Lemma 3.2).

A hairpin is parametrized by its tangent angle `θ ∈ (0, π)`; the profile
`f(θ) = ρ(θ) sin θ` determines the curve `C = (X, Z)` through
`X' = f cot θ`, `Z' = f`.  The tangent angle of `C + τ` is `g = θ + d` with
`d(θ) = arctan (sin θ / f(θ))`.

Main results:

* `translator_next_deriv` : differentiating the integral equation
  `∫_θ^{g θ} f = sin θ` gives `f(g) g' = f + cos θ`, so `g` is strictly
  increasing when `f > 1`.
* `translator_horizontal_deriv` : the horizontal defect
  `V(θ) = X(θ) + cos θ - X(g θ)` has vanishing derivative.
* `translator_equation` : consequently `C(θ) + τ(θ) = C(g θ) + (V, 0)` for a
  constant `V`.
* `translator_shift_antitone` : the operator `𝒫` is order preserving
  (the monotonicity half of Lemma 3.2), in the form: a larger profile reaches
  the mass `sin θ` sooner, and `sin θ cot (·)` reverses this.
-/

noncomputable section

open Real Set

namespace Translator

/-- The steering angle `d(θ) = arctan (sin θ / f(θ))` of the profile `f`. -/
noncomputable def steer (f : ℝ → ℝ) (θ : ℝ) : ℝ := Real.arctan (Real.sin θ / f θ)

/-- The tangent angle `g(θ) = θ + d(θ)` of the translated curve. -/
noncomputable def next (f : ℝ → ℝ) (θ : ℝ) : ℝ := θ + steer f θ

section Basic

variable {f : ℝ → ℝ}

lemma steer_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (hf : 0 < f θ) : 0 < steer f θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  exact Real.arctan_pos.mpr (div_pos hs hf)

lemma steer_lt_pi_div_two (θ : ℝ) : steer f θ < π / 2 := Real.arctan_lt_pi_div_two _

lemma cos_steer_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (hf : 0 < f θ) :
    0 < Real.cos (steer f θ) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [steer_pos hθ hf, Real.pi_pos], steer_lt_pi_div_two θ⟩

/-- The defining relation of the steering angle, in the form
`f · sin d = sin θ · cos d`. -/
lemma mul_sin_steer {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (hf : 0 < f θ) :
    f θ * Real.sin (steer f θ) = Real.sin θ * Real.cos (steer f θ) := by
  have hc : 0 < Real.cos (steer f θ) := cos_steer_pos hθ hf
  have htan : Real.tan (steer f θ) = Real.sin θ / f θ := Real.tan_arctan _
  rw [Real.tan_eq_sin_div_cos] at htan
  field_simp at htan
  linarith [htan]

end Basic

section Derivatives

variable {f A X : ℝ → ℝ}

/-- **Differentiating the translator integral equation.**  If `A` is a
primitive of `f` and `A (g θ) - A θ = sin θ` on `(0, π)`, then
`f (g θ) · g'(θ) = f(θ) + cos θ`. -/
theorem translator_next_deriv {g gp : ℝ → ℝ}
    (hA : ∀ t, HasDerivAt A (f t) t)
    (hg : ∀ θ, HasDerivAt g (gp θ) θ)
    (heq : ∀ θ ∈ Ioo (0:ℝ) π, A (g θ) - A θ = Real.sin θ)
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    f (g θ) * gp θ = f θ + Real.cos θ := by
  have hd1 : HasDerivAt (fun σ => A (g σ) - A σ) (f (g θ) * gp θ - f θ) θ :=
    ((hA (g θ)).comp θ (hg θ)).sub (hA θ)
  have hev : (fun σ => A (g σ) - A σ) =ᶠ[nhds θ] Real.sin := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with σ hσ using heq σ hσ
  have hd2 : HasDerivAt Real.sin (f (g θ) * gp θ - f θ) θ := hd1.congr_of_eventuallyEq hev.symm
  have := hd2.unique (Real.hasDerivAt_sin θ)
  linarith

/-- With `f > 1`, the tangent angle map `g` is strictly increasing. -/
theorem translator_next_deriv_pos {g gp : ℝ → ℝ}
    (hA : ∀ t, HasDerivAt A (f t) t)
    (hg : ∀ θ, HasDerivAt g (gp θ) θ)
    (heq : ∀ θ ∈ Ioo (0:ℝ) π, A (g θ) - A θ = Real.sin θ)
    (hf1 : ∀ t, 1 < f t)
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) : 0 < gp θ := by
  have key := translator_next_deriv hA hg heq hθ
  have hnum : 0 < f θ + Real.cos θ := by
    have := hf1 θ
    have := Real.neg_one_le_cos θ
    linarith
  have hfg : 0 < f (g θ) := lt_trans one_pos (hf1 (g θ))
  nlinarith [key, hnum, hfg]

/-- The algebraic identity behind the vanishing of the horizontal defect:
with `F sin d = s cos d` one has `F c/s - s - cot(θ + d)(F + c) = 0`. -/
lemma horizontal_algebra {F s c sd cd : ℝ} (hF : 0 < F) (hs : 0 < s)
    (hrel : F * sd = s * cd) (hden : s * cd + c * sd ≠ 0) :
    F * c / s - s - ((c * cd - s * sd) / (s * cd + c * sd)) * (F + c) = 0 := by
  have hF0 : F ≠ 0 := ne_of_gt hF
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hsd : sd = s * cd / F := by field_simp; linarith
  subst hsd
  have hd2 : s * cd * (F + c) ≠ 0 := by
    intro h
    apply hden
    field_simp
    nlinarith [h]
  have hcd : cd ≠ 0 := by
    intro h; apply hd2; rw [h]; ring
  have hFc : F + c ≠ 0 := by
    intro h; apply hd2; rw [h]; ring
  field_simp
  ring

/-- **The horizontal defect is locally constant.**  With `X' = f cot θ`, the
function `V(θ) = X(θ) + cos θ - X(g θ)` has vanishing derivative on `(0, π)`. -/
theorem translator_horizontal_deriv {gp : ℝ → ℝ}
    (hA : ∀ t, HasDerivAt A (f t) t)
    (hfpos : ∀ t, 0 < f t)
    (hg : ∀ θ, HasDerivAt (next f) (gp θ) θ)
    (heq : ∀ θ ∈ Ioo (0:ℝ) π, A (next f θ) - A θ = Real.sin θ)
    (hmaps : ∀ θ ∈ Ioo (0:ℝ) π, next f θ ∈ Ioo (0:ℝ) π)
    (hX : ∀ t ∈ Ioo (0:ℝ) π, HasDerivAt X (f t * Real.cos t / Real.sin t) t)
    {θ : ℝ} (hθ : θ ∈ Ioo (0:ℝ) π) :
    HasDerivAt (fun σ => X σ + Real.cos σ - X (next f σ)) 0 θ := by
  have hgθ : next f θ ∈ Ioo (0:ℝ) π := hmaps θ hθ
  have hXg : HasDerivAt (fun σ => X (next f σ))
      ((f (next f θ) * Real.cos (next f θ) / Real.sin (next f θ)) * gp θ) θ :=
    (hX _ hgθ).comp θ (hg θ)
  have htotal : HasDerivAt (fun σ => X σ + Real.cos σ - X (next f σ))
      (f θ * Real.cos θ / Real.sin θ + (-Real.sin θ)
        - (f (next f θ) * Real.cos (next f θ) / Real.sin (next f θ)) * gp θ) θ :=
    ((hX θ hθ).add (Real.hasDerivAt_cos θ)).sub hXg
  -- the derivative vanishes
  have key := translator_next_deriv hA hg heq hθ
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
  have hzero : f θ * Real.cos θ / Real.sin θ + (-Real.sin θ)
      - (f (next f θ) * Real.cos (next f θ) / Real.sin (next f θ)) * gp θ = 0 := by
    have hswap : (f (next f θ) * Real.cos (next f θ) / Real.sin (next f θ)) * gp θ
        = (Real.cos (next f θ) / Real.sin (next f θ)) * (f θ + Real.cos θ) := by
      rw [← key]
      field_simp
    rw [hswap, hcosg, hsing]
    have hden : Real.sin θ * Real.cos (steer f θ) + Real.cos θ * Real.sin (steer f θ) ≠ 0 := by
      rw [← hsing]; exact ne_of_gt hsg
    exact horizontal_algebra (hfpos θ) hs hrel hden
  rw [hzero] at htotal
  exact htotal

/-- **Lemma 3.1 (Translator equation).**  If the profile `f` satisfies the
translator integral equation, then the unit-tangent transform moves the
hairpin `C = (X, Z)` by a fixed horizontal vector:
`C(θ) + τ(θ) = C(g θ) + (V, 0)`. -/
theorem translator_equation {Z : ℝ → ℝ} {gp : ℝ → ℝ}
    (hZ : ∀ t, HasDerivAt Z (f t) t)
    (hfpos : ∀ t, 0 < f t)
    (hg : ∀ θ, HasDerivAt (next f) (gp θ) θ)
    (heq : ∀ θ ∈ Ioo (0:ℝ) π, Z (next f θ) - Z θ = Real.sin θ)
    (hmaps : ∀ θ ∈ Ioo (0:ℝ) π, next f θ ∈ Ioo (0:ℝ) π)
    (hX : ∀ t ∈ Ioo (0:ℝ) π, HasDerivAt X (f t * Real.cos t / Real.sin t) t) :
    ∃ V : ℝ, ∀ θ ∈ Ioo (0:ℝ) π,
      (X θ + Real.cos θ, Z θ + Real.sin θ) = (X (next f θ) + V, Z (next f θ)) := by
  set W : ℝ → ℝ := fun σ => X σ + Real.cos σ - X (next f σ) with hW
  have hderiv : ∀ σ ∈ Ioo (0:ℝ) π, HasDerivAt W 0 σ := fun σ hσ =>
    translator_horizontal_deriv hZ hfpos hg heq hmaps hX hσ
  have hconst : ∀ θ₁ ∈ Ioo (0:ℝ) π, ∀ θ₂ ∈ Ioo (0:ℝ) π, W θ₁ = W θ₂ := by
    intro θ₁ hθ₁ θ₂ hθ₂
    refine (convex_Ioo (0:ℝ) π).is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (f := W) ?_ ?_ hθ₁ hθ₂
    · exact fun z hz => ((hderiv z hz).differentiableAt).differentiableWithinAt
    · intro z hz
      rw [((hderiv z hz).hasFDerivAt.hasFDerivWithinAt).fderivWithin
        (isOpen_Ioo.uniqueDiffOn z hz)]
      ext
      simp
  have hhalf : (π / 2) ∈ Ioo (0:ℝ) π := by
    constructor <;> [linarith [Real.pi_pos]; linarith [Real.pi_pos]]
  refine ⟨W (π / 2), ?_⟩
  intro θ hθ
  have h1 : W θ = W (π / 2) := hconst θ hθ _ hhalf
  have h2 : Z (next f θ) - Z θ = Real.sin θ := heq θ hθ
  rw [hW] at h1
  simp only [Prod.mk.injEq]
  constructor
  · linarith [h1]
  · linarith [h2]

end Derivatives

section Monotone

/-- **Order preservation of the translator operator (Lemma 3.2).**  If
`f ≤ h` and the two "mass" times `D_f`, `D_h` both realize the mass `sin θ`,
then `D_h ≤ D_f`; consequently `𝒫f = sin θ cot D_f ≤ sin θ cot D_h = 𝒫h`. -/
theorem translator_shift_antitone {f h : ℝ → ℝ} {Df Dh θ : ℝ}
    (hfh : ∀ t, f t ≤ h t) (hf0 : ∀ t, 0 < f t)
    (hDf : 0 < Df)
    (hIf : ∫ t in θ..(θ + Df), f t = Real.sin θ)
    (hIh : ∫ t in θ..(θ + Dh), h t = Real.sin θ)
    (hfint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b)
    (hhint : ∀ a b : ℝ, IntervalIntegrable h MeasureTheory.volume a b) :
    Dh ≤ Df := by
  by_contra hcon
  push_neg at hcon
  have hmono : (∫ t in θ..(θ + Df), f t) ≤ ∫ t in θ..(θ + Df), h t :=
    intervalIntegral.integral_mono_on (by linarith) (hfint _ _) (hhint _ _)
      (fun x _ => hfh x)
  have hsplit : (∫ t in θ..(θ + Dh), h t)
      = (∫ t in θ..(θ + Df), h t) + ∫ t in (θ + Df)..(θ + Dh), h t :=
    (intervalIntegral.integral_add_adjacent_intervals (hhint _ _) (hhint _ _)).symm
  have hpos : 0 < ∫ t in (θ + Df)..(θ + Dh), h t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hhint _ _)
      (fun x _ => lt_of_lt_of_le (hf0 x) (hfh x)) (by linarith)
  rw [hIh, hIf] at *
  linarith

/-- The operator `𝒫f = sin θ · cot D_f` is order preserving: since the mass
time decreases when the profile increases, and `cot` is decreasing on
`(0, π/2)`, we get `𝒫f ≤ 𝒫h`. -/
theorem translator_operator_mono {Df Dh θ : ℝ}
    (hθ : θ ∈ Ioo (0:ℝ) π) (hDh : 0 < Dh) (hDf : Df < π / 2) (hle : Dh ≤ Df) :
    Real.sin θ * (Real.cos Df / Real.sin Df) ≤ Real.sin θ * (Real.cos Dh / Real.sin Dh) := by
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hpi := Real.pi_pos
  have hDf0 : 0 < Df := lt_of_lt_of_le hDh hle
  have hsDh : 0 < Real.sin Dh := Real.sin_pos_of_pos_of_lt_pi hDh (by linarith)
  have hsDf : 0 < Real.sin Df := Real.sin_pos_of_pos_of_lt_pi hDf0 (by linarith)
  have hcos : Real.cos Df ≤ Real.cos Dh :=
    Real.cos_le_cos_of_nonneg_of_le_pi hDh.le (by linarith) hle
  have hsin : Real.sin Dh ≤ Real.sin Df :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hDf.le hle
  have hcosDh : 0 < Real.cos Dh := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have key : Real.cos Df / Real.sin Df ≤ Real.cos Dh / Real.sin Dh := by
    rw [div_le_div_iff₀ hsDf hsDh]
    nlinarith
  exact mul_le_mul_of_nonneg_left key hsθ.le

end Monotone

end Translator
