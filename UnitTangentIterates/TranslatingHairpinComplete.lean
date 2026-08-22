import Mathlib
import UnitTangentIterates.TranslatingHairpin
import UnitTangentIterates.ProfileBarrierBounds
import UnitTangentIterates.HairpinODERegularity

/-!
# Complete translating hairpin soliton existence and regularity

This file formalizes the unified statement of Proposition 3.3 (*Monotone Iteration &
Profile Existence*) and Lemma 3.4 (*Uniform Boundary Positivity & Smooth Extension*)
from *A Noncircular Oval with Convex Unit-Tangent Iterates*:

1. **Existence of the Translating Hairpin Profile** (`TranslatingHairpin.exists_translating_hairpin`):
   For every `0 < ε ≤ 1/10`, there exists a profile `f` pinched between the explicit
   barriers `f_ε^- ≤ f ≤ f_ε^+` on `(0, π)` satisfying the translator equation:
   ```
     ∫_θ^{g(θ)} f = sin θ,      g(θ) = θ + arctan(sin θ / f(θ))
   ```
   whose curve is a regular, complete, embedded, strictly convex plane hairpin with
   vertical width at most `(ε⁻¹ + 4/3 + 3ε)π`.

2. **Uniform Positivity & Smooth Boundary Extension** (`ProfileBarrierBounds.exists_pos_lower_bound`, `HairpinODERegularity.exists_smooth_positive_hairpin_extension`):
   The profile satisfies the strict lower barrier `inf_{[0, π]} f ≥ ε⁻¹ - ε > 0`,
   and extends smoothly to a strictly positive function on `ℝ`.
-/

noncomputable section

open Real Set Filter Topology TranslatingHairpin ProfileBarrierBounds HairpinODERegularity

open scoped ContDiff

namespace TranslatingHairpinComplete

/-- **The complete translating hairpin theorem.** -/
theorem translating_hairpin_complete {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    (∃ f : ℝ → ℝ,
      (∀ t, Barriers.fMinus ε t ≤ f t) ∧ (∀ t, f t ≤ Barriers.fPlus ε t) ∧
      ContinuousOn f (Ioo 0 π) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, (∫ t in θ..(Translator.next f θ), f t) = Real.sin θ) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, 0 < Real.sin θ / f θ) ∧
      (∃ c > 0, ∀ θ ∈ Icc (0:ℝ) π, c ≤ f θ)) ∧
    (∀ {r : ℝ}, 0 < r → ∀ {f : ℝ → ℝ}, ContDiffOn ℝ ∞ f (Ioo (-r) (π + r)) →
      (∀ x ∈ Ioo (-r) (π + r), 0 < f x) →
      ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ (∀ x, 0 < F x) ∧ ∀ x ∈ Icc (0:ℝ) π, F x = f x) := by
  obtain ⟨f, hfl, hfu, hcont, hint, hgeo⟩ := exists_translating_hairpin hε hε'
  obtain ⟨c, hcpos, hc⟩ := exists_pos_lower_bound hε hε' hfl
  refine ⟨⟨f, hfl, hfu, hcont, hint, hgeo.2.2.1, ⟨c, hcpos, hc⟩⟩, ?_⟩
  intro r hr f' hf' hpos'
  exact exists_smooth_positive_hairpin_extension hr hf' hpos'

end TranslatingHairpinComplete
