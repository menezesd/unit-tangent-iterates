import Mathlib
import UnitTangentIterates.PulseHigherDerivativeBridge

/-!
# The relative pulse derivative bounds at orders three and four

The lemma *Hairpin pulse estimates* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* asserts

```
  |y^{(j)}(s)| ≤ D_j y(s)          (eq:relative-y-derivatives)
```

for every order `j`, where `y = sin δ` is the steering pulse in front
arclength.  Crucially, the paper's proof of this does **not** use any
regularity of the hairpin profile at the endpoints of `(0,π)`: it runs the
induction on the shifted curvature identity

```
  K_*' = (1+K_*²)^{3/2} (K_* ∘ σ) − K_* − K_*³
```

together with the bounded-shift Harnack estimate, which come from the barrier
enclosure `m ≤ f ≤ M` alone.

`PulseHigherDerivativeBridge` carries out the two remaining differentiations,
producing the third and fourth front-arclength pulse derivatives with explicit
relative majorants — but stated against the *curvature* `K ∘ x` rather than
against the pulse `y`.  This file converts them, giving
`eq:relative-y-derivatives` at `j = 3, 4` in the paper's own form.

The conversion is the elementary inequality `K ≤ √(1+B²) · y`, valid whenever
`0 ≤ K ≤ B`, since `y = K/√(1+K²)`.

Main results: `curv_le_sqrt_mul_pulse`, `rel_pulse_third`, `rel_pulse_fourth`.
-/

noncomputable section

open ShiftedCurvatureJetMajorant PulseHigherDerivativeBridge

namespace PulseRelativeHigherOrder

/-- **The curvature is controlled by the pulse.**  Since `y = K/√(1+K²)` and
`0 ≤ K ≤ B`, one has `K ≤ √(1+B²) · y`.  This is the inequality that turns a
bound relative to `K` into a bound relative to `y`. -/
theorem curv_le_sqrt_mul_pulse {k B : ℝ} (hk0 : 0 ≤ k) (hkB : k ≤ B) :
    k ≤ Real.sqrt (1 + B ^ 2) * (k / Real.sqrt (1 + k ^ 2)) := by
  have hkpos : (0:ℝ) < Real.sqrt (1 + k ^ 2) := by
    have : (0:ℝ) < 1 + k ^ 2 := by positivity
    exact Real.sqrt_pos.2 this
  have hmono : Real.sqrt (1 + k ^ 2) ≤ Real.sqrt (1 + B ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rw [mul_div_assoc', le_div_iff₀ hkpos]
  nlinarith [hk0, hkpos]

/-- **`eq:relative-y-derivatives` at order three.**  The third front-arclength
derivative of the steering pulse is bounded by a constant multiple of the pulse
itself, with the constant depending only on the curvature ceiling and the
relative curvature constants. -/
theorem rel_pulse_third {K K1 K2 K3 x : ℝ → ℝ} {B D1 D2 D3 : ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1d : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2d : ∀ u, HasDerivAt K2 (K3 u) u)
    (hx : ∀ s, HasDerivAt x (1 / Real.sqrt (1 + K (x s) ^ 2)) s)
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B) (hB : 0 ≤ B)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hRK1 : RelMajorant K K1 D1) (hRK2 : RelMajorant K K2 D2)
    (hRK3 : RelMajorant K K3 D3) (s : ℝ) :
    |pulseDDD K K1 K2 x s|
      ≤ (pulseThirdConstant B D1 D2 D3 * Real.sqrt (1 + B ^ 2)) *
          PulseFromCurvature.pulse K x s := by
  have hrel := PulseHigherDerivativeBridge.rel_pulseDDD hK hK1d hK2d hx hK0 hKB
    hB hD1 hD2 hD3 hRK1 hRK2 hRK3 s
  have hC : 0 ≤ pulseThirdConstant B D1 D2 D3 :=
    pulseThirdConstant_nonneg hB hD1 hD2 hD3
  refine hrel.trans ?_
  have hcurv := curv_le_sqrt_mul_pulse (hK0 (x s)) (hKB (x s))
  calc pulseThirdConstant B D1 D2 D3 * K (x s)
      ≤ pulseThirdConstant B D1 D2 D3 *
          (Real.sqrt (1 + B ^ 2) * (K (x s) / Real.sqrt (1 + K (x s) ^ 2))) :=
        mul_le_mul_of_nonneg_left hcurv hC
    _ = (pulseThirdConstant B D1 D2 D3 * Real.sqrt (1 + B ^ 2)) *
          PulseFromCurvature.pulse K x s := by
        simp [PulseFromCurvature.pulse, mul_assoc]

/-- **`eq:relative-y-derivatives` at order four.** -/
theorem rel_pulse_fourth {K K1 K2 K3 K4 x : ℝ → ℝ} {B D1 D2 D3 D4 : ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1d : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2d : ∀ u, HasDerivAt K2 (K3 u) u)
    (hK3d : ∀ u, HasDerivAt K3 (K4 u) u)
    (hx : ∀ s, HasDerivAt x (1 / Real.sqrt (1 + K (x s) ^ 2)) s)
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B) (hB : 0 ≤ B)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3) (hD4 : 0 ≤ D4)
    (hRK1 : RelMajorant K K1 D1) (hRK2 : RelMajorant K K2 D2)
    (hRK3 : RelMajorant K K3 D3) (hRK4 : RelMajorant K K4 D4)
    (hC4 : 0 ≤ pulseFourthConstant B D1 D2 D3 D4) (s : ℝ) :
    |pulseDDDD K K1 K2 x s|
      ≤ (pulseFourthConstant B D1 D2 D3 D4 * Real.sqrt (1 + B ^ 2)) *
          PulseFromCurvature.pulse K x s := by
  have hrel := PulseHigherDerivativeBridge.rel_pulseDDDD hK hK1d hK2d hK3d hx
    hK0 hKB hB hD1 hD2 hD3 hD4 hRK1 hRK2 hRK3 hRK4 s
  refine hrel.trans ?_
  have hcurv := curv_le_sqrt_mul_pulse (hK0 (x s)) (hKB (x s))
  calc pulseFourthConstant B D1 D2 D3 D4 * K (x s)
      ≤ pulseFourthConstant B D1 D2 D3 D4 *
          (Real.sqrt (1 + B ^ 2) * (K (x s) / Real.sqrt (1 + K (x s) ^ 2))) :=
        mul_le_mul_of_nonneg_left hcurv hC4
    _ = (pulseFourthConstant B D1 D2 D3 D4 * Real.sqrt (1 + B ^ 2)) *
          PulseFromCurvature.pulse K x s := by
        simp [PulseFromCurvature.pulse, mul_assoc]

end PulseRelativeHigherOrder
