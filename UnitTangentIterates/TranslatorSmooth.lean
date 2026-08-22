import Mathlib

/-!
# Smoothness of the translator profile

The theorem *Translating hairpin* of the paper *A Noncircular Oval with Convex
Unit-Tangent Iterates* asserts that the profile solving the translator equation
is `C^∞` on `(0, π)`.  This file contains the bootstrap that proves it.

The two structural facts are:

* the mass time `U` is differentiable with `U' = (f + cos θ)/(f ∘ U)`
  (`TranslatorShift.hasDerivAt_shift`), so `U` is one derivative better than
  `f`;
* the fixed-point identity `f = sin θ · cot (U − θ)` makes `f` exactly as
  smooth as `U`.

Alternating the two gives `f, U ∈ C^n` for every `n`:

* `contDiffOn_of_fixedPoint` — `∀ n, f ∈ C^n(0, π)` and `U ∈ C^{n+1}(0, π)`.
-/

noncomputable section

open Real Set

namespace TranslatorSmooth

variable {f U : ℝ → ℝ}

/-- The fixed-point identity `f = sin θ · cot (U − θ)` transfers the regularity
of the mass time to the profile. -/
theorem contDiffOn_profile_of_shift {n : ℕ} (hUc : ContDiffOn ℝ n U (Ioo 0 π))
    (hsin : ∀ θ ∈ Ioo (0:ℝ) π, Real.sin (U θ - θ) ≠ 0)
    (hfix : ∀ θ ∈ Ioo (0:ℝ) π,
      f θ = Real.sin θ * (Real.cos (U θ - θ) / Real.sin (U θ - θ))) :
    ContDiffOn ℝ n f (Ioo 0 π) := by
  have hD : ContDiffOn ℝ n (fun θ => U θ - θ) (Ioo 0 π) := hUc.sub contDiffOn_id
  have hcos : ContDiffOn ℝ n (fun θ => Real.cos (U θ - θ)) (Ioo 0 π) :=
    Real.contDiff_cos.comp_contDiffOn hD
  have hsn : ContDiffOn ℝ n (fun θ => Real.sin (U θ - θ)) (Ioo 0 π) :=
    Real.contDiff_sin.comp_contDiffOn hD
  have hquot : ContDiffOn ℝ n
      (fun θ => Real.cos (U θ - θ) / Real.sin (U θ - θ)) (Ioo 0 π) :=
    hcos.div hsn hsin
  exact ((Real.contDiff_sin.contDiffOn).mul hquot).congr hfix

/-- The differential equation `U' = (f + cos θ)/(f ∘ U)` makes the mass time
one derivative smoother than the profile. -/
theorem contDiffOn_shift_succ {n : ℕ} (hf : ContDiffOn ℝ n f (Ioo 0 π))
    (hUc : ContDiffOn ℝ n U (Ioo 0 π))
    (hderiv : ∀ θ ∈ Ioo (0:ℝ) π,
      HasDerivAt U ((f θ + Real.cos θ) / f (U θ)) θ)
    (hmaps : MapsTo U (Ioo 0 π) (Ioo 0 π)) (hfne : ∀ t ∈ Ioo (0:ℝ) π, f t ≠ 0) :
    ContDiffOn ℝ (n + 1 : ℕ) U (Ioo 0 π) := by
  have hdiff : DifferentiableOn ℝ U (Ioo 0 π) := fun θ hθ =>
    ((hderiv θ hθ).differentiableAt).differentiableWithinAt
  have hcomp : ContDiffOn ℝ n (fun θ => f (U θ)) (Ioo 0 π) := hf.comp hUc hmaps
  have hnum : ContDiffOn ℝ n (fun θ => f θ + Real.cos θ) (Ioo 0 π) :=
    hf.add Real.contDiff_cos.contDiffOn
  have hne : ∀ θ ∈ Ioo (0:ℝ) π, f (U θ) ≠ 0 := fun θ hθ => hfne _ (hmaps hθ)
  have hg : ContDiffOn ℝ n (fun θ => (f θ + Real.cos θ) / f (U θ)) (Ioo 0 π) :=
    hnum.div hcomp hne
  have hderivEq : ContDiffOn ℝ n (deriv U) (Ioo 0 π) :=
    hg.congr fun θ hθ => (hderiv θ hθ).deriv
  have := (contDiffOn_succ_iff_deriv_of_isOpen (n := (n : WithTop ℕ∞)) (f := U)
    (s := Ioo (0:ℝ) π) isOpen_Ioo).mpr ⟨hdiff, by simp, hderivEq⟩
  exact_mod_cast this

/-- **The translator profile is `C^∞` on `(0, π)`.**  A continuous fixed point
`f = sin θ · cot (U − θ)` of the translator operator, whose mass time `U`
satisfies `U' = (f + cos θ)/(f ∘ U)`, is smooth of every order, and the mass
time is one order smoother. -/
theorem contDiffOn_of_fixedPoint (hcont : ContinuousOn f (Ioo 0 π))
    (hderiv : ∀ θ ∈ Ioo (0:ℝ) π,
      HasDerivAt U ((f θ + Real.cos θ) / f (U θ)) θ)
    (hmaps : MapsTo U (Ioo 0 π) (Ioo 0 π)) (hfne : ∀ t ∈ Ioo (0:ℝ) π, f t ≠ 0)
    (hsin : ∀ θ ∈ Ioo (0:ℝ) π, Real.sin (U θ - θ) ≠ 0)
    (hfix : ∀ θ ∈ Ioo (0:ℝ) π,
      f θ = Real.sin θ * (Real.cos (U θ - θ) / Real.sin (U θ - θ))) :
    ∀ n : ℕ, ContDiffOn ℝ n f (Ioo 0 π) ∧ ContDiffOn ℝ (n + 1 : ℕ) U (Ioo 0 π) := by
  intro n
  induction n with
  | zero =>
    have hf0 : ContDiffOn ℝ (0:ℕ) f (Ioo 0 π) := by
      simpa using (contDiffOn_zero (𝕜 := ℝ)).mpr hcont
    have hU0 : ContDiffOn ℝ (0:ℕ) U (Ioo 0 π) := by
      have hUcont : ContinuousOn U (Ioo 0 π) := fun θ hθ =>
        ((hderiv θ hθ).continuousAt).continuousWithinAt
      simpa using (contDiffOn_zero (𝕜 := ℝ)).mpr hUcont
    exact ⟨hf0, contDiffOn_shift_succ hf0 hU0 hderiv hmaps hfne⟩
  | succ n ih =>
    have hfn : ContDiffOn ℝ (n + 1 : ℕ) f (Ioo 0 π) :=
      contDiffOn_profile_of_shift ih.2 hsin hfix
    exact ⟨hfn, contDiffOn_shift_succ hfn ih.2 hderiv hmaps hfne⟩

end TranslatorSmooth
