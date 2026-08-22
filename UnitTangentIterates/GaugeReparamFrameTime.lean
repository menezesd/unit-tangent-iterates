import Mathlib

/-!
# Differentiating a jointly `C¹` function of two variables along a flow line

The variable-speed hypotheses of `GaugeFlowVariableSpeedFamily.lean` ask for the
time derivatives of the tangent angle and of the curvature of the slices *read
along the flow line*, `t ↦ f(t, Φ(t,u))`.  Everywhere else in the project those
data are available as the two partial derivatives `∂_t f` and `∂_x f`
separately.  This file supplies the chain rule that connects them:

```
  d/dt f(t, Φ(t,u)) = ∂_t f(t, Φ(t,u)) + ∂_x f(t, Φ(t,u)) · R(t, Φ(t,u)) ,
```

for a jointly `C¹` function `f` and a flow line of the field `R`, together with
the bound `|·| ≤ |∂_t f| + |∂_x f|·|R|` it gives.

Joint regularity is genuinely needed: the two partial derivatives alone do not
determine the derivative along a curve.

Main results: `hasDerivAt_along_flow`, `abs_deriv_along_flow_le`.
-/

noncomputable section

open Function

namespace GaugeReparamFrameTime

variable {f ft fx R Phi : ℝ → ℝ → ℝ}

/-- The total derivative of a jointly `C¹` function, evaluated on the two
coordinate directions, is the pair of its partial derivatives. -/
private theorem fderiv_apply_eq (hfC1 : ContDiff ℝ 1 (uncurry f))
    (hft : ∀ t x, HasDerivAt (fun r => f r x) (ft t x) t)
    (hfx : ∀ t x, HasDerivAt (f t) (fx t x) x) (t x : ℝ) :
    fderiv ℝ (uncurry f) (t, x) (1, 0) = ft t x ∧
      fderiv ℝ (uncurry f) (t, x) (0, 1) = fx t x := by
  have hF : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) (t, x)) (t, x) :=
    (hfC1.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  constructor
  · have hcurve : HasDerivAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    have h := hF.comp_hasDerivAt t hcurve
    exact (h.unique (hft t x)).symm ▸ rfl
  · have hcurve : HasDerivAt (fun y : ℝ => (t, y)) ((0 : ℝ), (1 : ℝ)) x :=
      (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
    have h := hF.comp_hasDerivAt x hcurve
    exact (h.unique (hfx t x)).symm ▸ rfl

/-- **The chain rule along a flow line.**  If `f` is jointly `C¹` with partial
derivatives `∂_t f = ft` and `∂_x f = fx`, and `Φ(·,u)` is a flow line of the
field `R`, then `t ↦ f(t, Φ(t,u))` is differentiable with derivative
`ft + fx · R` evaluated at `(t, Φ(t,u))`. -/
theorem hasDerivAt_along_flow (hfC1 : ContDiff ℝ 1 (uncurry f))
    (hft : ∀ t x, HasDerivAt (fun r => f r x) (ft t x) t)
    (hfx : ∀ t x, HasDerivAt (f t) (fx t x) x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (R t (Phi t u)) t) (u t : ℝ) :
    HasDerivAt (fun r => f r (Phi r u))
      (ft t (Phi t u) + fx t (Phi t u) * R t (Phi t u)) t := by
  set x := Phi t u with hx
  have hF : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) (t, x)) (t, x) :=
    (hfC1.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hcurve : HasDerivAt (fun r : ℝ => (r, Phi r u)) ((1 : ℝ), R t x) t :=
    (hasDerivAt_id t).prodMk (hPhid u t)
  have h := hF.comp_hasDerivAt t hcurve
  refine h.congr_deriv ?_
  obtain ⟨h1, h2⟩ := fderiv_apply_eq hfC1 hft hfx t x
  have hsplit : ((1 : ℝ), R t x) = ((1 : ℝ), (0 : ℝ)) + R t x • ((0 : ℝ), (1 : ℝ)) := by
    simp
  rw [hsplit, map_add, map_smul, h1, h2, smul_eq_mul, mul_comm]

/-- The bound the variable-speed hypotheses ask for: the derivative along a flow
line is at most the sum of the two partial contributions. -/
theorem abs_deriv_along_flow_le {a b c : ℝ} (t x : ℝ)
    (hft : |ft t x| ≤ a) (hfx : |fx t x| ≤ b) (hR : |R t x| ≤ c) (hb : 0 ≤ b) :
    |ft t x + fx t x * R t x| ≤ a + b * c := by
  calc |ft t x + fx t x * R t x| ≤ |ft t x| + |fx t x * R t x| := abs_add_le _ _
    _ = |ft t x| + |fx t x| * |R t x| := by rw [abs_mul]
    _ ≤ a + b * c := add_le_add hft (mul_le_mul hfx hR (abs_nonneg _) hb)

end GaugeReparamFrameTime
