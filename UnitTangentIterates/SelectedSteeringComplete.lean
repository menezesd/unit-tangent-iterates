import Mathlib
import UnitTangentIterates.SteeringExistence

/-!
# Complete periodic steering solution on the closed strip

This file formalizes the complete statement of Lemma 6.1 (*Selected inverse on the closed strip*)
from *A Noncircular Oval with Convex Unit-Tangent Iterates*:

For any continuous `S`-periodic front curvature `K` with `0 ≤ K ≤ κ̂ < 1`:

1. **Existence & Uniqueness** (`SteeringExistence.existsUnique_periodic_steering`):
   There is a unique `S`-periodic steering angle `δ` with values in `[0, arcsin κ̂]`
   solving the nonlinear ODE:
   ```
     δ'(s) = K(s) - sin(δ(s))
   ```

2. **Strict Speed Lower Bound** (`SteeringExistence.exists_periodic_steering`):
   The rear speed is bounded away from zero:
   ```
     cos(δ(s)) ≥ √(1 - κ̂²) > 0
   ```
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace SelectedSteeringComplete

open SteeringExistence

/-- **The complete periodic steering existence and uniqueness package.** -/
theorem selected_steering_complete
    {K : ℝ → ℝ} {S kap : ℝ} (hS : 0 < S) (hK : Continuous K)
    (hKper : Function.Periodic K S) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hK0 : ∀ s, 0 ≤ K s) (hKk : ∀ s, K s ≤ kap) :
    ∃! delta : ℝ → ℝ, Function.Periodic delta S ∧
      (∀ s, delta s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta s)) ∧
      (∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s) := by
  obtain ⟨d, hper, hrange, hcos, hode⟩ :=
    exists_periodic_steering hS hK hKper hkap0 hkap1.le hK0 hKk
  have hstrip : ∀ (e : ℝ → ℝ), (∀ s, e s ∈ Icc 0 (Real.arcsin kap)) →
      ∀ s, e s ∈ Icc (-(π / 2)) (π / 2) := by
    intro e he s
    have h := he s
    exact ⟨by linarith [h.1, Real.pi_pos], le_trans h.2 (Real.arcsin_le_pi_div_two kap)⟩
  refine ⟨d, ⟨hper, hrange, hcos, hode⟩, ?_⟩
  rintro e ⟨hpere, hrangee, -, hodee⟩
  exact Shadowing.steering_unique hS hodee hode hpere hper (hstrip e hrangee) (hstrip d hrange)

end SelectedSteeringComplete
