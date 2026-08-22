import Mathlib
import UnitTangentIterates.GaugeFlowTimeDerivative
import UnitTangentIterates.GaugeReparamVariableSpeed

/-!
# The family of unit-speed curves read in a gauge flow is a variable-speed family

`GaugeReparamVariableSpeed.lean` reduces `IsVariableSpeedFamily` for the family

```
  X t u = Y t (Φ t u)
```

to statements about the marking `Φ` and about the geometry of the slices, and
`GaugeFlowTimeDerivative.lean` supplies those statements for a marking that is
the flow of a scalar field: the first two parameter derivatives of the flow are
`flowDeriv` and `flowDeriv2` (`FlowDerivative.lean`), and their time derivatives
obey the variational equations, hence are bounded by `C t · P₁` and
`C t · G₁ + C₂ t · P₁²` for pointwise bounds `C`, `C₂` on the first two space
derivatives of the field.

This file puts the two together.  What is left as a hypothesis is exactly the
part that is not about the flow: the time derivatives of the tangent angle and
of the curvature of the slices read along the flow line, which are frame data of
the moving family of curves and not of the marking.

Main result: `isVariableSpeedFamily_of_gauge_flow`.
-/

noncomputable section

open Set Function

namespace GaugeFlowVariableSpeedFamily

open FlowDerivative GaugeFlowTimeDerivative GaugeReparamVariableSpeed
  NormalPathC2IncrementVariableSpeed

/-- **The family of unit-speed curves read in a gauge flow is a variable-speed
family.**

`Y t` is parametrized by arclength with tangent angle `α t` and curvature `k t`,
and `Φ` is the flow of the scalar field `h` started at the affine marking
`u ↦ ℓ·u`.  If the first two space derivatives of the field are bounded by `C t`
and `C₂ t`, if the flow derivative stays below `P₁` and the second flow
derivative below `G₁` in absolute value, and if the two products `C t · P₁` and
`C t · G₁ + C₂ t · P₁²` are bounded by the multiples `κ̂ P₁ · m t` and
`C_g · m t` of the cost density, then `X t u = Y t (Φ t u)` is a variable-speed
family — provided the time derivatives of the tangent angle and of the curvature
along the flow line obey their own bounds. -/
theorem isVariableSpeedFamily_of_gauge_flow
    {Y : ℝ → ℝ → ℂ} {alpha k h hx hxx Phi : ℝ → ℝ → ℝ}
    {alphat kappat : ℝ → ℝ → ℝ} {C C2 m : ℝ → ℝ} {K K2 : NNReal} {ell : ℝ}
    {P0 P1 khat G1 Cg : ℝ}
    -- the slices, parametrized by their own arclength
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    -- the field and its flow
    (hlip : ∀ t, LipschitzWith K (h t)) (hcont : Continuous (uncurry h))
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (hxcont : Continuous (uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x) (hxxcont : Continuous (uncurry hxx))
    (hxxK : ∀ s x, |hxx s x| ≤ (K2 : ℝ))
    -- the uniform bounds on the two flow derivatives
    (hP1 : ∀ t u, flowDeriv hx Phi ell t u ≤ P1)
    (hG1 : ∀ t u, |flowDeriv2 hx hxx Phi ell t u| ≤ G1)
    (hk : ∀ t u, |k t (Phi t u)| ≤ khat)
    -- the pointwise bounds on the two space derivatives of the field
    (hC : ∀ t x, |hx t x| ≤ C t) (hC2 : ∀ t x, |hxx t x| ≤ C2 t)
    (hCnn : ∀ t, 0 ≤ C t) (hC2nn : ∀ t, 0 ≤ C2 t)
    -- and their comparison with the cost density
    (hcost : ∀ t, C t * P1 ≤ khat * P1 * m t)
    (hcost2 : ∀ t, C t * G1 + C2 t * P1 ^ 2 ≤ Cg * m t)
    -- the frame data of the slices along the flow line
    (hthetat : ∀ t u, HasDerivAt (fun r => alpha r (Phi r u)) (alphat t u) t)
    (hthetatc : ∀ u, Continuous fun t => alphat t u)
    (hthetatbd : ∀ t u, |alphat t u| ≤ 1 / P0 * m t)
    (hkappat : ∀ t u, HasDerivAt (fun r => k r (Phi r u)) (kappat t u) t)
    (hkappatc : ∀ u, Continuous fun t => kappat t u)
    (hkappatbd : ∀ t u, |kappat t u| ≤ (1 / P0 ^ 2 + khat ^ 2) * m t) :
    IsVariableSpeedFamily P0 P1 khat G1 Cg (fun t u => Y t (Phi t u)) m := by
  -- the two parameter derivatives of the flow
  have hPhiu : ∀ t u, HasDerivAt (Phi t) (flowDeriv hx Phi ell t u) u := fun t u =>
    hasDerivAt_flow_initial hlip hcont hPhid hell hPhi0 hxd u t
  have hPhiuu : ∀ t u, HasDerivAt (fun u' => flowDeriv hx Phi ell t u')
      (flowDeriv2 hx hxx Phi ell t u) u := fun t u =>
    hasDerivAt_flowDeriv hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxK u t
  -- their time derivatives, from the variational equations
  have hgt : ∀ t u, HasDerivAt (fun r => flowDeriv hx Phi ell r u)
      (hx t (Phi t u) * flowDeriv hx Phi ell t u) t := fun t u =>
    hasDerivAt_flowDeriv_time hPhid hxcont u t
  have hgut : ∀ t u, HasDerivAt (fun r => flowDeriv2 hx hxx Phi ell r u)
      (hx t (Phi t u) * flowDeriv2 hx hxx Phi ell t u
        + hxx t (Phi t u) * flowDeriv hx Phi ell t u ^ 2) t := fun t u =>
    hasDerivAt_flowDeriv2_time hPhid hxcont hxxcont u t
  refine isVariableSpeedFamily_of_reparam (alpha := alpha) (k := k)
    (Phiu := flowDeriv hx Phi ell) (Phiuu := flowDeriv2 hx hxx Phi ell)
    (Phiut := fun t u => hx t (Phi t u) * flowDeriv hx Phi ell t u)
    (Phiuut := fun t u => hx t (Phi t u) * flowDeriv2 hx hxx Phi ell t u
      + hxx t (Phi t u) * flowDeriv hx Phi ell t u ^ 2)
    hY halpha hPhiu hPhiuu (fun t u => (flowDeriv_pos hell t u).le) hP1 hG1 hk
    hgt ?_ ?_ hgut ?_ ?_ hthetat hthetatc hthetatbd hkappat hkappatc hkappatbd
  · exact fun u => continuous_flowDeriv_time_deriv hPhid hxcont u
  · exact fun t u => le_trans
      (abs_flowDeriv_time_le hell (hC t (Phi t u)) (hP1 t u) (hCnn t)) (hcost t)
  · exact fun u => continuous_flowDeriv2_time_deriv hPhid hxcont hxxcont u
  · exact fun t u => le_trans
      (abs_flowDeriv2_time_le hell (hC t (Phi t u)) (hC2 t (Phi t u)) (hG1 t u) (hP1 t u)
        (hCnn t) (hC2nn t)) (hcost2 t)

end GaugeFlowVariableSpeedFamily
