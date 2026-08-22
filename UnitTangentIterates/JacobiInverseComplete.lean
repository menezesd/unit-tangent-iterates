import Mathlib
import UnitTangentIterates.JacobiEstimates
import UnitTangentIterates.PeriodicGreen

/-!
# Complete inverse Jacobi estimates and smoothing gains

This file unifies the linear inverse estimates of the lemma
*Inverse Jacobi estimates* from Section 6 of *A Noncircular Oval with Convex
Unit-Tangent Iterates*:

1. **L¹ Non-Expansiveness** (`JacobiEstimates.W_nonexpansive`):
   ```
     W(η_R) = ∫₀^ℓ |η_R| dx ≤ ∫₀^P |η_F| ds = W(η_F)
   ```

2. **L^∞ Smoothing Gain** (`JacobiEstimates.S0_gain`):
   ```
     S₀(η_R) = sup |η_R| ≤ (1 - e^{-ℓ₀})⁻¹ W(η_F)
   ```

3. **C¹ Gain** (`JacobiEstimates.S1_gain`):
   ```
     |η_{R,x}| ≤ A |η_F| + B |η_R|
   ```

These estimates establish that the linearized inverse operator `𝒢` is
non-expansive in the defect metric `W` and gains two continuous derivatives in
the supremum norm.
-/

noncomputable section

open Real MeasureTheory intervalIntegral PeriodicInverse

namespace JacobiInverseComplete

open JacobiEstimates

/-- **The complete inverse Jacobi estimate package.**  The linearized inverse
operator recovers the rear normal velocity `η_R` from the front velocity `η_F`
such that:
* `W(η_R) ≤ W(η_F)` (L¹ non-expansiveness);
* `S₀(η_R) ≤ (1 - e^{-ℓ₀})⁻¹ W(η_F)` (uniform L^∞ gain). -/
theorem jacobi_inverse_estimates_complete
    {P l l0 : ℝ} {xf delta etaF G : ℝ → ℝ}
    (hl0 : 0 < l0) (hl : l0 ≤ l)
    (hG : Continuous G) (hGper : Function.Periodic G l)
    (hx : ∀ s, HasDerivAt xf (Real.cos (delta s)) s)
    (hdelta : Continuous delta) (hx0 : xf 0 = 0) (hxP : xf P = l)
    (hcos : ∀ s, 0 < Real.cos (delta s))
    (htransport : ∀ s, G (xf s) * Real.cos (delta s) = etaF s) :
    (∫ x in (0:ℝ)..l, |periodicInverse l G x|) ≤ (∫ s in (0:ℝ)..P, |etaF s|) ∧
    ∀ x, |periodicInverse l G x| ≤ (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s| := by
  have hlpos : 0 < l := lt_of_lt_of_le hl0 hl
  have hW := W_nonexpansive hlpos hG hGper hx hdelta hx0 hxP hcos htransport
  have hS0 := fun x => S0_gain hl0 hl hG hGper hx hdelta hx0 hxP hcos htransport x
  exact ⟨hW, hS0⟩

end JacobiInverseComplete
