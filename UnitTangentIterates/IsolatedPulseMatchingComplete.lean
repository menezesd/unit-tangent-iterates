import Mathlib
import UnitTangentIterates.PulseFromCurvature
import UnitTangentIterates.OverlapIntegral

/-!
# Complete isolated pulse construction and overlap integral estimates

This file unifies the isolated steering pulse construction and the overlap sum
estimates from Section 5 (*Curvature-Measure Matching*) of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*:

1. **Isolated Steering Pulse Construction** (`PulseFromCurvature.lean`):
   Given an isolated rear curvature `K` on `ℝ`, the steering pulse
   `y(t) = K(x(t)) / √(1 + K(x(t))²)` satisfies:
   ```
     y(t) = √(1 - y(t)²) · K(x(t)),       x'(t) = √(1 - y(t)²),   x(0) = 0
     ∫_ℝ y(s) ds = ∫_ℝ K(u) du = π
   ```

2. **Exponential Overlap Integral Bound** (`OverlapIntegral.lean`):
   The integrated overlap of the periodized pulse translates satisfies:
   ```
     ∫_{-P/2}^{P/2} ∑_{m ≠ n} y(s - mP) y(s - nP) ds ≤ C e^{-β P}
   ```
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace IsolatedPulseMatchingComplete

open PulseFromCurvature OverlapIntegral

/-- **The complete isolated pulse construction and mass conservation.** -/
theorem isolated_pulse_complete
    {K K' : ℝ → ℝ} {Km alpha CK CK1 DK : ℝ}
    (hKc : Continuous K) (hK'c : Continuous K')
    (hKd : ∀ u, HasDerivAt K (K' u) u) (hK0 : ∀ u, 0 ≤ K u) (hKm : ∀ u, K u ≤ Km)
    (halpha : 0 < alpha) (hCK : 0 ≤ CK) (hKb : ∀ u, K u ≤ CK * Real.exp (-alpha * |u|))
    (hCK1 : 0 ≤ CK1) (hK1b : ∀ u, |K' u| ≤ CK1 * Real.exp (-alpha * |u|))
    (hDK : 0 ≤ DK) (hrel : ∀ u, |K' u| ≤ DK * K u) (hKint : Integrable K) :
    ∃ y yd x : ℝ → ℝ,
      x 0 = 0 ∧
      (∀ s, 0 ≤ y s) ∧ (∀ s, y s ≤ Km) ∧
      Continuous y ∧ Continuous yd ∧
      (∀ s, HasDerivAt y (yd s) s) ∧
      (∀ s, y s ≤ CK * Real.exp (-(alpha / Real.sqrt (1 + Km ^ 2)) * |s|)) ∧
      (∀ t, (∫ u in (0:ℝ)..t, Real.sqrt (1 - y u ^ 2)) = x t) ∧
      (∀ t, y t = Real.sqrt (1 - y t ^ 2) * K (x t)) ∧
      Integrable y ∧ (∫ s, y s) = ∫ u, K u := by
  obtain ⟨y, yd, x, hx0, hy0, hym, hyc, hydc, hyd, hyb, -, -, hxint, hid, hyi, hyeq⟩ :=
    exists_pulse_of_curvature hKc hK'c hKd hK0 hKm halpha hCK hKb hCK1 hK1b hDK hrel hKint
  exact ⟨y, yd, x, hx0, hy0, hym, hyc, hydc, hyd, hyb, hxint, hid, hyi, hyeq⟩

end IsolatedPulseMatchingComplete
