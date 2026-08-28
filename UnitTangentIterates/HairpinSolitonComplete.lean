import Mathlib
import UnitTangentIterates.TranslatorOperator
import UnitTangentIterates.TranslatorTranslation

/-!
# Complete translating hairpin soliton operator and horizontal translation

This file formalizes the unified statement of Definition 3.1 (*Hairpin Profile Equation*),
Lemma 3.2 (*Explicit Barrier Construction*), Proposition 3.3 (*Monotone Iteration*),
and the translation law from Section 3 of *A Noncircular Oval with Convex Unit-Tangent Iterates*:

1. **Monotone Operator & Profile Existence** (`TranslatorOperator.lean`, `TranslatorTranslation.lean`):
   The translator operator `(𝒫f)(θ) = sin θ · cot D_f(θ)` is monotone in `f`.
   Starting from the explicit lower barrier `f_ε^-`, the iterates converge monotonically
   to a fixed point `f = 𝒫f` satisfying:
   ```
     ∫_θ^{g(θ)} f = sin θ,      g(θ) = θ + arctan(sin θ / f(θ))
   ```

2. **Horizontal Soliton Translation & Smoothness** (`TranslatorTranslation.exists_translating_hairpin_translation`):
   The associated plane curve `(X, Z)` with `X' = f cot θ`, `Z' = f` is smooth
   on `(0, π)` and translates rigidly by `V > 0` under the unit-tangent transformation:
   ```
     (X(θ) + cos θ, Z(θ) + sin θ) = (X(g(θ)) + V, Z(g(θ)))
   ```
-/

noncomputable section

open Real Set Filter Topology TranslatorTranslation

namespace HairpinSolitonComplete

/-- **The complete translating soliton theorem.** -/
theorem hairpin_soliton_complete {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    ∃ f : ℝ → ℝ, ∃ V : ℝ, 0 < V ∧
      (∀ t, Barriers.fMinus ε t ≤ f t) ∧ (∀ t, f t ≤ Barriers.fPlus ε t) ∧
      ContinuousOn f (Ioo 0 π) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, Translator.next f θ ∈ Ioo θ π) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, (∫ t in θ..(Translator.next f θ), f t) = Real.sin θ) ∧
      (∀ n : ℕ, ContDiffOn ℝ n f (Ioo 0 π)) ∧
      (∀ θ ∈ Ioo (0:ℝ) π,
        (Hairpin.hairpinX f θ + Real.cos θ, Hairpin.hairpinZ f θ + Real.sin θ)
          = (Hairpin.hairpinX f (Translator.next f θ) + V,
             Hairpin.hairpinZ f (Translator.next f θ))) :=
  by
    obtain ⟨f, V, hV, hfl, hfu, hc, hm, hU, hs, -, -, htrans⟩ :=
      exists_translating_hairpin_translation hε hε'
    exact ⟨f, V, hV, hfl, hfu, hc, hm, hU, hs, htrans⟩

end HairpinSolitonComplete
