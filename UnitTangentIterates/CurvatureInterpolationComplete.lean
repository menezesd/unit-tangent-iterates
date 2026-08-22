import Mathlib
import UnitTangentIterates.CurvatureInterpolation

/-!
# Complete curvature interpolation of Lemma 6.2

This file formalizes the complete statement of Lemma 6.2 (*Curvature Interpolation*)
from *A Noncircular Oval with Convex Unit-Tangent Iterates*:

For any continuous `L`-periodic intrinsic curvature `κ` with `∫₀ᴸ κ = π` and marked
tangent angle `θ₀`, the explicit curve:
```
  X(s) = ∫₀ˢ e^{i θ(r)} dr - ½ ∫₀ᴸ e^{i θ(r)} dr,      θ(s) = θ₀ + ∫₀ˢ κ
```
satisfies:
1. **Central Symmetry & Closure** (`CurvatureInterpolation.interpCurve_add_halfPeriod`):
   ```
     X(s + L) = -X(s),       X(s + 2L) = X(s)
   ```

2. **Unit Speed & Tangent Geometry** (`CurvatureInterpolation.hasDerivAt_interpCurve`):
   ```
     X'(s) = e^{i θ(s)},     θ'(s) = κ(s)
   ```

3. **Quantitative L¹ Metric Stability** (`CurvatureInterpolation.norm_interpCurve_interp_sub`):
   Linear interpolation `κ_t = (1-t)κ⁰ + tκ¹` moves the curves by at most:
   ```
     ‖X_t(s) - X_{t'}(s)‖ ≤ (3/2) L |t - t'| ‖κ¹ - κ⁰‖_{L¹(0, L)}
   ```
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral CurvatureInterpolation

namespace CurvatureInterpolationComplete

/-- **The complete curvature interpolation theorem.** -/
theorem curvature_interpolation_complete
    {k0 k1 : ℝ → ℝ} {θ₀ L : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Function.Periodic k0 L) (hper1 : Function.Periodic k1 L)
    (hint0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (hint1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi) :
    (∀ t ∈ Icc (0:ℝ) 1, ∀ s,
      interpCurve (kappaInterp k0 k1 t) θ₀ L (s + L) = -interpCurve (kappaInterp k0 k1 t) θ₀ L s) ∧
    (∀ t ∈ Icc (0:ℝ) 1, ∀ s,
      interpCurve (kappaInterp k0 k1 t) θ₀ L (s + 2 * L) = interpCurve (kappaInterp k0 k1 t) θ₀ L s) ∧
    (∀ t ∈ Icc (0:ℝ) 1, ∀ s,
      HasDerivAt (interpCurve (kappaInterp k0 k1 t) θ₀ L)
        (tau (tangentAngle (kappaInterp k0 k1 t) θ₀ s)) s) ∧
    (∀ t ∈ Icc (0:ℝ) 1, ∀ t' ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) L,
      ‖interpCurve (kappaInterp k0 k1 t) θ₀ L s - interpCurve (kappaInterp k0 k1 t') θ₀ L s‖
        ≤ (3/2) * L * (|t - t'| * ∫ r in (0:ℝ)..L, |k1 r - k0 r|)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht s
    exact interpCurve_add_halfPeriod (continuous_kappaInterp hk0 hk1)
      (periodic_kappaInterp hper0 hper1) (integral_kappaInterp hk0 hk1 hint0 hint1) s
  · intro t ht s
    exact interpCurve_periodic (continuous_kappaInterp hk0 hk1)
      (periodic_kappaInterp hper0 hper1) (integral_kappaInterp hk0 hk1 hint0 hint1) s
  · intro t ht s
    exact hasDerivAt_interpCurve (continuous_kappaInterp hk0 hk1) s
  · intro t ht t' ht' s hs
    exact norm_interpCurve_interp_sub hk0 hk1 hs

end CurvatureInterpolationComplete
