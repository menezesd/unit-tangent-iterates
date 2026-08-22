import Mathlib
import UnitTangentIterates.GaugeFlowPathFundamental
import UnitTangentIterates.GaugeMarkedDataOfNormalRate

/-!
# The comparison path from the normal rate, with the bounds on one period only

`GaugeMarkedDataOfNormalRate.exists_variableSpeed_normalPath_of_normal_rate`
builds the normal path with slices of variable speed of a family carried in its
own arclength out of the motion of that family: the two time derivatives of its
frame data are expressed by the normal-flow relations

```
  ∂_tα = ∂_sη + k ξ ,        ∂_t k = ∂_s²η + k² η + ξ ∂_s k ,
```

and bounded through bounds `S₀, S₁, S₂` for the normal rate and its first two
arclength derivatives and a bound `R_b` for the tangential rate.

All of those bounds are asked there globally in the arclength, which for a
family whose arclength period moves is impossible for `R_b` — and hence for the
angle rate too.  `GaugeFlowPathFundamental.lean` removes that restriction at the
level of the marking; this file carries it through the normal-rate form: every
bound is asked only on one period `[0, Q t]`, the closing structure of the
family being given in exchange.

Main result: `exists_variableSpeed_normalPath_of_normal_rate_fundamental`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeNormalRateFundamental

open GaugeFlowVariableSpeedPath GaugeFrameTimeBounds GaugeFrameTangentialRate
  NormalPathC2IncrementVariableSpeed GaugeMarkedDataOfNormalRate
  GaugeFlowPathFundamental

variable {a b : Data} {Y : ℝ → ℝ → ℂ}
  {alpha k en enS enSS h hx hxx Phi alphaT kT kX : ℝ → ℝ → ℝ}
  {C C2 Kx Rb S0 S1 S2 m Q Q' : ℝ → ℝ} {K K2 : NNReal} {turn T : ℝ}
  {P0 P1 khat G1 Cg c0 c1 c2 r kx : ℝ}

/-- **The normal path with slices of variable speed of a family given by its
normal rate, with every bound asked on one period only.**

The hypotheses are those of
`GaugeMarkedDataOfNormalRate.exists_variableSpeed_normalPath_of_normal_rate`,
with the pointwise bounds on the curvature, on the two space derivatives of the
field, on the arclength derivative of the curvature, on the field itself and on
the normal rate and its two arclength derivatives asked only for
`x ∈ [0, Q t]`, and with the closing structure of the family given in exchange.
Nothing is assumed about the motion of the arclength period. -/
theorem exists_variableSpeed_normalPath_of_normal_rate_fundamental
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      (((-h t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hlip : ∀ t, LipschitzWith K (h t)) (hcont : Continuous (uncurry h))
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (hxcont : Continuous (uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x) (hxxcont : Continuous (uncurry hxx))
    (hxxK : ∀ s x, |hxx s x| ≤ (K2 : ℝ))
    (hP1 : ∀ t u, FlowDerivative.flowDeriv hx Phi (Q 0) t u ≤ P1)
    (hG1 : ∀ t u, |GaugeFlowTimeDerivative.flowDeriv2 hx hxx Phi (Q 0) t u| ≤ G1)
    (hCnn : ∀ t, 0 ≤ C t) (hC2nn : ∀ t, 0 ≤ C2 t)
    (hcost : ∀ t, C t * P1 ≤ khat * P1 * m t)
    (hcost2 : ∀ t, C t * G1 + C2 t * P1 ^ 2 ≤ Cg * m t)
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => ((-h t x : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    -- the closing structure of the family
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hqp : ∀ t x, h t (x + Q t) = h t x + Q' t)
    (hkper : ∀ t, Function.Periodic (k t) (Q t))
    (halphaper : ∀ t x, alpha t (x + Q t) = alpha t x + turn)
    (hbase : ∀ t, Phi t 0 = 0)
    -- the bounds, on one period only
    (hk : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |k t x| ≤ khat)
    (hC : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |hx t x| ≤ C t)
    (hC2 : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |hxx t x| ≤ C2 t)
    (hKxbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |kX t x| ≤ Kx t)
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |h t x| ≤ Rb t)
    (hS0bd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |en t x| ≤ S0 t)
    (hS1bd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |enS t x| ≤ S1 t)
    (hS2bd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |enSS t x| ≤ S2 t)
    -- the comparisons with the cost density and the numerical conditions
    (hS0m : ∀ t, S0 t ≤ c0 * m t) (hS1m : ∀ t, S1 t ≤ c1 * m t) (hS2m : ∀ t, S2 t ≤ c2 * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : c1 + 2 * khat * r ≤ 1 / P0)
    (hnumK : c2 + khat ^ 2 * c0 + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    -- the path data
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hstart : ∀ u, Y 0 (Phi 0 u) = a.1 u) (hfinish : ∀ u, Y T (Phi T u) = b.1 u)
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0)
    (hmbd : ∀ t u, |en t (Phi t u)| ≤ m t)
    (hmsup : ∀ t, ∀ j ≤ 2,
      MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) :
    ∃ Γ : NormalPath a b, Γ.T = T ∧ (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
      Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ := by
  -- the two normal-flow relations, valid at every arclength
  have hxiS : ∀ t x, HasDerivAt (fun s => -h t s) (k t x * en t x) x :=
    hasDerivAt_xi_of_mixed halpha henS hxd halphaT hmixed
  have hrel : ∀ t x, alphaT t x = enS t x + k t x * (-h t x) :=
    angleRate_rel halpha henS hxiS halphaT hmixed
  have hrelk : ∀ t s, kT t s = enSS t s + k t s ^ 2 * en t s + (-h t s) * kX t s :=
    curvRate_rel hrel henSS hkX hxiS halphaTS
  -- and the two bounds they give, on one period
  have hAbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |alphaT t x| ≤ angleRateBound S1 Rb khat t := by
    intro t x hx
    refine abs_angleRate_le (alphaT := alphaT) (etaS := enS) (k := k)
      (xi := fun t s => -h t s) t x (hrel t x) (hS1bd t x hx) (hk t x hx) ?_
    simpa using hRbd t x hx
  have hKtbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |kT t x| ≤ curvRateBound S0 S2 Rb Kx khat t := by
    intro t x hx
    refine abs_curvRate_le (kT := kT) (etaSS := enSS) (eta := en) (k := k)
      (xi := fun t s => -h t s) (kX := kX) t x (hrelk t x) (hS2bd t x hx) (hS0bd t x hx)
      (hk t x hx) ?_ (hKxbd t x hx)
    simpa using hRbd t x hx
  have hkhat : 0 ≤ khat := le_trans (abs_nonneg _) (hk 0 0 ⟨le_rfl, (hQpos 0).le⟩)
  exact exists_variableSpeed_normalPath_of_gauge_marking_fundamental
    (A := angleRateBound S1 Rb khat) (Kt := curvRateBound S0 S2 Rb Kx khat)
    hYC1 hY hYt halpha hlip hcont hPhid hPhi0 hxd hxcont hxxd hxxcont hxxK hP1 hG1
    hCnn hC2nn hcost hcost2 halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc hkc hKxnn
    (fun t => angleRate_le_cost hS1m hRbm hm0 hkhat hnumA t)
    (fun t => curvRate_le_cost hS0m hS2m hRbm hKxm hKxnn hm0 hr hnumK t)
    hQpos hQd hqp hkper halphaper hbase hk hC hC2 hAbd hKtbd hKxbd hRbd
    hT hencont hstart hfinish hmc hm0 hmstop hmbd hmsup

end GaugeNormalRateFundamental
