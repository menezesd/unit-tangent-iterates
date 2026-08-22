import Mathlib
import UnitTangentIterates.GaugeFlowVariableSpeedFamily
import UnitTangentIterates.GaugeReparamFrameTime

/-!
# The variable-speed assembly with the frame data given by partial derivatives

`GaugeFlowVariableSpeedFamily.isVariableSpeedFamily_of_gauge_flow` still asks
for the time derivatives of the tangent angle and of the curvature of the slices
*along the flow line*.  Everywhere else the frame data of a moving family are
available as partial derivatives in the two variables separately.  The chain
rule of `GaugeReparamFrameTime.lean` converts one into the other,

```
  d/dt α(t, Φ(t,u)) = ∂_tα(t,Φ) + k(t,Φ)·h(t,Φ) ,
  d/dt k(t, Φ(t,u)) = ∂_t k(t,Φ) + ∂_x k(t,Φ)·h(t,Φ) ,
```

so that the two remaining hypotheses become bounds on the partial derivatives of
the frame data and on the field of the gauge flow.

Main result: `isVariableSpeedFamily_of_gauge_flow_partials`.
-/

noncomputable section

open Set Function

namespace GaugeFlowVariableSpeedPartials

open FlowDerivative GaugeFlowTimeDerivative GaugeFlowVariableSpeedFamily
  GaugeReparamFrameTime NormalPathC2IncrementVariableSpeed

/-- **The variable-speed assembly with the frame data given by partial
derivatives.**  Same as `isVariableSpeedFamily_of_gauge_flow`, with the two time
derivatives along the flow line replaced by the partial derivatives `∂_tα`,
`∂_t k`, `∂_x k` of the frame data of the slices and by the field `h` of the
gauge flow, and their bounds combined by the chain rule. -/
theorem isVariableSpeedFamily_of_gauge_flow_partials
    {Y : ℝ → ℝ → ℂ} {alpha k h hx hxx Phi : ℝ → ℝ → ℝ}
    {alphaT kT kX : ℝ → ℝ → ℝ} {C C2 A Kt Kx Rb m : ℝ → ℝ} {K K2 : NNReal} {ell : ℝ}
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
    (hk : ∀ t x, |k t x| ≤ khat)
    -- the pointwise bounds on the two space derivatives of the field
    (hC : ∀ t x, |hx t x| ≤ C t) (hC2 : ∀ t x, |hxx t x| ≤ C2 t)
    (hCnn : ∀ t, 0 ≤ C t) (hC2nn : ∀ t, 0 ≤ C2 t)
    -- and their comparison with the cost density
    (hcost : ∀ t, C t * P1 ≤ khat * P1 * m t)
    (hcost2 : ∀ t, C t * G1 + C2 t * P1 ^ 2 ≤ Cg * m t)
    -- the frame data of the slices, as partial derivatives
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    -- their bounds, and the bound on the field itself
    (hAbd : ∀ t x, |alphaT t x| ≤ A t) (hKtbd : ∀ t x, |kT t x| ≤ Kt t)
    (hKxbd : ∀ t x, |kX t x| ≤ Kx t) (hRbd : ∀ t x, |h t x| ≤ Rb t)
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (hcostA : ∀ t, A t + khat * Rb t ≤ 1 / P0 * m t)
    (hcostK : ∀ t, Kt t + Kx t * Rb t ≤ (1 / P0 ^ 2 + khat ^ 2) * m t) :
    IsVariableSpeedFamily P0 P1 khat G1 Cg (fun t u => Y t (Phi t u)) m := by
  have hkhat : 0 ≤ khat := le_trans (abs_nonneg _) (hk 0 0)
  have hflowc : ∀ u, Continuous fun t => Phi t u := fun u =>
    GaugeFlowTimeDerivative.continuous_flow_time hPhid u
  refine isVariableSpeedFamily_of_gauge_flow (alphat := fun t u =>
      alphaT t (Phi t u) + k t (Phi t u) * h t (Phi t u))
    (kappat := fun t u => kT t (Phi t u) + kX t (Phi t u) * h t (Phi t u))
    hY halpha hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxK hP1 hG1
    (fun t u => hk t (Phi t u)) hC hC2 hCnn hC2nn hcost hcost2
    (fun t u => hasDerivAt_along_flow halphaC1 halphaT halpha hPhid u t)
    (fun u => ((halphaTc.comp (continuous_id.prodMk (hflowc u))).add
      ((hkc.comp (continuous_id.prodMk (hflowc u))).mul
        (hcont.comp (continuous_id.prodMk (hflowc u))))))
    (fun t u => le_trans (abs_deriv_along_flow_le (ft := alphaT) (fx := k) (R := h)
      t (Phi t u) (hAbd t (Phi t u)) (hk t (Phi t u)) (hRbd t (Phi t u)) hkhat) (hcostA t))
    (fun t u => hasDerivAt_along_flow hkC1 hkT hkX hPhid u t)
    (fun u => ((hkTc.comp (continuous_id.prodMk (hflowc u))).add
      ((hkXc.comp (continuous_id.prodMk (hflowc u))).mul
        (hcont.comp (continuous_id.prodMk (hflowc u))))))
    (fun t u => le_trans (abs_deriv_along_flow_le (ft := kT) (fx := kX) (R := h)
      t (Phi t u) (hKtbd t (Phi t u)) (hKxbd t (Phi t u)) (hRbd t (Phi t u)) (hKxnn t))
      (hcostK t))

end GaugeFlowVariableSpeedPartials
