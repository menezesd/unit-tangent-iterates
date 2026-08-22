import Mathlib
import UnitTangentIterates.HairpinDefect
import UnitTangentIterates.TwoCapAsymptoticsComplete

/-!
# Complete hairpin arclength defect and two-cap perimeter asymptotics

This file formalizes the unified statement of Proposition 4.2 (*Perimeter Defect Value
& Derivative Asymptotics*) and Lemma 4.1 (*Hairpin Pulse Estimates & Arclength Defect*)
from *A Noncircular Oval with Convex Unit-Tangent Iterates*:

1. **Integrability & Strict Positivity of the Arclength Defect** (`HairpinRelative.hairpin_defect`):
   Along the front-arclength parametrization of the translating hairpin soliton,
   the defect field `1 - cos δ(s) = 1 - 1/√(1 + K_*²)` is integrable and satisfies:
   ```
     Δ = ∫_{-∞}^∞ (1 - cos δ(s)) ds > 0
   ```

2. **Exponential Perimeter Defect & Derivative Asymptotics** (`TwoCapAsymptoticsComplete.two_cap_perimeter_defect_asymptotics`, `TwoCapAsymptoticsComplete.two_cap_perimeter_derivative_asymptotics`):
   For large cap separation `H`, the half-perimeter `P(H)` satisfies:
   ```
     |(H - P(H)) - Δ| ≤ C₁ e^{-β' H},       |P'(H) - 1| ≤ (25 C² + C_i) e^{-α H}
   ```
-/

noncomputable section

open Real Set MeasureTheory Filter Topology HairpinRelative TwoCapAsymptoticsComplete

open scoped ContDiff

namespace HairpinDefectComplete

/-- **The complete hairpin defect and perimeter asymptotics theorem.** -/
theorem hairpin_defect_complete
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    (∃ theta x : ℝ → ℝ,
      Integrable (fun s => defectField f (theta (x s))) ∧
      0 < ∫ s, defectField f (theta (x s))) ∧
    (∀ {Y y : ℝ → ℝ} {C a alpha H beta' : ℝ},
      0 < alpha → 0 < H → beta' < alpha / 2 →
      Real.exp (-alpha * H) ≤ 1 / 2 →
      (∀ s, 0 ≤ y s) → (∀ s, y s ≤ 1) →
      (∀ s, y s ≤ C * Real.exp (-alpha * |s|)) →
      0 ≤ a → a < 1 →
      (∀ u : ℝ, (∑' m : ℤ, y (u - m * H)) ≤ a) →
      (∀ s, Y s = ∑' m : ℤ, y (s - m * H)) →
      IntervalIntegrable (fun s => Real.sqrt (1 - Y s ^ 2)) volume 0 H →
      Function.Periodic (fun s => PerimeterAsymptotics.Phi (Y s)) H →
      Integrable (fun s => PerimeterAsymptotics.Phi (y s)) →
      IntervalIntegrable (fun s => PerimeterAsymptotics.Phi (Y s)) volume (-(H / 2)) (H / 2) →
      |(H - (∫ s in (0:ℝ)..H, Real.sqrt (1 - Y s ^ 2))) - ∫ s : ℝ, PerimeterAsymptotics.Phi (y s)|
        ≤ (a / Real.sqrt (1 - a ^ 2) * (4 * C) / ((alpha / 2 - beta') * Real.exp 1)
            + 2 * C ^ 2 / alpha) * Real.exp (-beta' * H)) := by
  obtain ⟨theta, x, -, -, -, hint, hpos⟩ := hairpin_defect hf hfpos
  refine ⟨⟨theta, x, hint, hpos⟩, ?_⟩
  intro Y y C a alpha H beta' halpha hH hb hq hy0 hy1 hyb ha0 ha1 hYa hY hc hper hgi hGi
  exact two_cap_perimeter_defect_asymptotics
    halpha hH hb hq hy0 hy1 hyb ha0 ha1 hYa hY hc hper hgi hGi

end HairpinDefectComplete
