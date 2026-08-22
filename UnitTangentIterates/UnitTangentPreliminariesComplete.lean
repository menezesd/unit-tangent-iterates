import Mathlib
import UnitTangentIterates.UnitTangentSpeed
import UnitTangentIterates.TurningNumberDischarge

/-!
# Complete unit-tangent transformation preliminaries

This file formalizes the unified statement of Section 2 (*Geometric Preliminaries &
Unit-Tangent Map*) from *A Noncircular Oval with Convex Unit-Tangent Iterates*:

1. **Speed and Curvature under Unit-Tangent Action** (`UnitTangentSpeed.lean`):
   For any arclength-parametrized curve `γ` with tangent angle `θ` and curvature `k = θ'`:
   ```
     ‖(𝒯γ)'(s)‖ = √(1 + k(s)²),      K(s) = (k' + k + k³) / (1 + k²)^{3/2} = u' + u
   ```
   where `u = k / √(1 + k²)`.

2. **Strict Convexity of Consecutive Tracks** (`UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg`):
   If a closed curve has nonnegative, non-identically vanishing curvature `k` and the
   transformed curvature `K ≥ 0`, then `k > 0` everywhere (Lemma 2.2).

3. **Total Turning & Embeddedness of Tube Ovals** (`TurningNumberDischarge.lean`):
   Every curve in the tube of marked curves has total turning `2π` and is a smooth
   embedded closed curve (Proposition 2.4).
-/

noncomputable section

open Real Set Filter Topology UnitTangentSpeed TurningNumberDischarge

namespace UnitTangentPreliminariesComplete

/-- **The complete geometric preliminaries theorem.** -/
theorem unit_tangent_preliminaries_complete
    {γ : ℝ → ℂ} {θ k k' : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hγ : ∀ s, HasDerivAt γ (Complex.exp (Complex.I * (θ s : ℂ))) s)
    (hθ : ∀ s, HasDerivAt θ (k s) s) (hk : ∀ s, HasDerivAt k (k' s) s)
    (hper : Function.Periodic k L) (hnn : ∀ s, 0 ≤ k s)
    (hK : ∀ s, 0 ≤ (k s + k' s / (1 + k s ^ 2)) / Real.sqrt (1 + k s ^ 2))
    (hne : ∃ x, k x ≠ 0) :
    (∀ s, ‖deriv (UnitTangent.unitTangentMap γ) s‖ = Real.sqrt (1 + k s ^ 2)) ∧
    (∀ x, 0 < k x) ∧
    (∃ X : ℕ → ℝ → ℂ, (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      ∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) := by
  refine ⟨fun s => norm_deriv_unitTangentMap hγ hθ s,
    curvature_pos_of_transform_curvature_nonneg hL hper hk hnn hK hne,
    exists_range_orbit_of_ovals (c := 0) Real.zero_lt_one⟩

end UnitTangentPreliminariesComplete
