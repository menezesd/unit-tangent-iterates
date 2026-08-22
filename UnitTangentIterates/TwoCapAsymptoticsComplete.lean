import Mathlib
import UnitTangentIterates.PerimeterAsymptoticsProduced
import UnitTangentIterates.PerimeterDerivativeProduced

/-!
# Complete two-cap perimeter asymptotics and derivative bounds

This file formalizes the combined perimeter defect and derivative estimates
for exact two-cap pairs from Section 4 of *A Noncircular Oval with Convex
Unit-Tangent Iterates*:

1. **Perimeter Defect Value Asymptotics** (`PerimeterAsymptoticsProduced.lean`):
   ```
     |H - P(H) - Δ| ≤ (C_approx + C_tail) e^{-β' H}
   ```
   with `Δ = ∫_ℝ (1 - √(1 - y(s)²)) ds > 0`.

2. **Perimeter Derivative Bounds** (`PerimeterDerivativeProduced.lean`):
   ```
     |P'(H) - 1| ≤ (25 C² + C_i) e^{-α H}
   ```
-/

noncomputable section

open Real Set MeasureTheory

namespace TwoCapAsymptoticsComplete

open PerimeterAsymptotics

/-- **The perimeter defect value asymptotics for an exponentially localized pulse.**
For a localized pulse `y` bounded by `C e^{-α|s|}` whose periodization `Y` stays in `[-a, a]`,
the half-perimeter defect `H - P(H)` approximates `Δ = ∫_ℝ Φ(y)` with exponential error
`O(e^{-β' H})`. -/
theorem two_cap_perimeter_defect_asymptotics {Y y : ℝ → ℝ} {C a alpha H beta' : ℝ}
    (halpha : 0 < alpha) (hH : 0 < H) (hb : beta' < alpha / 2)
    (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s) (hy1 : ∀ s, y s ≤ 1)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ u : ℝ, (∑' m : ℤ, y (u - m * H)) ≤ a)
    (hY : ∀ s, Y s = ∑' m : ℤ, y (s - m * H))
    (hc : IntervalIntegrable (fun s => Real.sqrt (1 - Y s ^ 2)) volume 0 H)
    (hper : Function.Periodic (fun s => Phi (Y s)) H)
    (hgi : Integrable (fun s => Phi (y s)))
    (hGi : IntervalIntegrable (fun s => Phi (Y s)) volume (-(H / 2)) (H / 2)) :
    |(H - (∫ s in (0:ℝ)..H, Real.sqrt (1 - Y s ^ 2))) - ∫ s : ℝ, Phi (y s)|
      ≤ (a / Real.sqrt (1 - a ^ 2) * (4 * C) / ((alpha / 2 - beta') * Real.exp 1)
          + 2 * C ^ 2 / alpha) * Real.exp (-beta' * H) :=
  PerimeterAsymptoticsProduced.abs_defect_sub_delta_le_pulse
    halpha hH hb hq hy0 hy1 hyb ha0 ha1 hYa hY hc hper hgi hGi

/-- **The perimeter derivative asymptotics for a localized pulse.**
The derivative of the half-perimeter `P'(H)` differs from `1` by at most
`(25 C² + C_i) e^{-α H}`. -/
theorem two_cap_perimeter_derivative_asymptotics {y : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {gH : ℝ → ℝ}
    {C a alpha H Ci : ℝ} {P : ℝ → ℝ}
    (halpha : 0 < alpha) (hH : 0 < H) (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (ha1 : a < 1)
    (hYa : ∀ u : ℝ, (∑' m : ℤ, y (u - m * H)) ≤ a)
    (hg : ∀ H' s, g H' s = Phi (∑' m : ℤ, y (s - m * H')))
    (hid : ∀ H', H' - P H' = ∫ s in (-(H'/2))..(H'/2), g H' s)
    (hderiv : HasDerivAt (fun H' => ∫ s in (-(H'/2))..(H'/2), g H' s)
      (g H (H/2) / 2 + g H (-(H/2)) / 2 + ∫ s in (-(H/2))..(H/2), gH s) H)
    (hint : |∫ s in (-(H/2))..(H/2), gH s| ≤ Ci * Real.exp (-alpha * H)) :
    ∃ p : ℝ, HasDerivAt P p H ∧ |p - 1| ≤ (25 * C ^ 2 + Ci) * Real.exp (-alpha * H) :=
  PerimeterDerivativeProduced.hasDerivAt_perimeter_of_pulse
    halpha hH hq hy0 hyb (fun u => (hYa u).trans ha1.le) hg hid hderiv hint

end TwoCapAsymptoticsComplete
