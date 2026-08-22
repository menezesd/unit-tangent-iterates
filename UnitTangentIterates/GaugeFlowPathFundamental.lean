import Mathlib
import UnitTangentIterates.GaugeFlowFundamentalDomain
import UnitTangentIterates.GaugeFlowVariableSpeedPath

/-!
# The normal path of a gauge marking, with the bounds asked on one period only

`GaugeFlowVariableSpeedPath.exists_variableSpeed_normalPath_of_gauge_marking`
produces the normal path with slices of variable speed of a family of closed
curves read in its gauge marking, asking its pointwise bounds *globally in the
arclength*.  `GaugeFlowFundamentalDomain.lean` shows that this is more than the
estimate needs: only the fundamental domain `[0, Q t]` of the slice at time `t`
is visited by the marking, and the quantities that drift with the period cancel
in the composites the assembly uses.

This file carries that improvement to the path: the same normal path is produced
with every pointwise bound asked only on one period, in exchange for the closing
structure of the family, and with no constraint on the motion of the arclength
period.

Main result: `exists_variableSpeed_normalPath_of_gauge_marking_fundamental`.
-/

noncomputable section

open Set Function MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeFlowPathFundamental

open FlowDerivative GaugeFlowTimeDerivative GaugeFlowNormalPath
  NormalPathC2IncrementVariableSpeed GaugeFlowFundamentalDomain
  GaugeFlowVariableSpeedPath

/-- **The variable-speed normal path of a family read in a gauge marking, with
every bound asked on one period only.**

The hypotheses are those of
`GaugeFlowVariableSpeedPath.exists_variableSpeed_normalPath_of_gauge_marking`,
with the pointwise bounds on the curvature, on the two space derivatives of the
field, on the two time derivatives of the frame data and on the field itself
asked only for `x ∈ [0, Q t]`, and with the closing structure of the family
given in exchange: the field is quasi-periodic with the current period, the
curvature is periodic, the tangent angle increases by a constant over one
period, and the marking starts at the affine marking of period `Q 0` and fixes
the base point.  Nothing is assumed about the motion of the period. -/
theorem exists_variableSpeed_normalPath_of_gauge_marking_fundamental
    {a b : Data} {Y : ℝ → ℝ → ℂ} {alpha k en h hx hxx Phi : ℝ → ℝ → ℝ}
    {alphaT kT kX : ℝ → ℝ → ℝ} {C C2 A Kt Kx Rb m Q Q' : ℝ → ℝ} {K K2 : NNReal}
    {turn T P0 P1 khat G1 Cg : ℝ}
    -- the slices, parametrized by their own arclength, and their motion
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      (((-h t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    -- the field and its flow
    (hlip : ∀ t, LipschitzWith K (h t)) (hcont : Continuous (uncurry h))
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (hxcont : Continuous (uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x) (hxxcont : Continuous (uncurry hxx))
    (hxxK : ∀ s x, |hxx s x| ≤ (K2 : ℝ))
    -- the uniform bounds on the two flow derivatives
    (hP1 : ∀ t u, flowDeriv hx Phi (Q 0) t u ≤ P1)
    (hG1 : ∀ t u, |flowDeriv2 hx hxx Phi (Q 0) t u| ≤ G1)
    (hCnn : ∀ t, 0 ≤ C t) (hC2nn : ∀ t, 0 ≤ C2 t)
    (hcost : ∀ t, C t * P1 ≤ khat * P1 * m t)
    (hcost2 : ∀ t, C t * G1 + C2 t * P1 ^ 2 ≤ Cg * m t)
    -- the frame data of the slices, as partial derivatives
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (hcostA : ∀ t, A t + khat * Rb t ≤ 1 / P0 * m t)
    (hcostK : ∀ t, Kt t + Kx t * Rb t ≤ (1 / P0 ^ 2 + khat ^ 2) * m t)
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
    (hAbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |alphaT t x| ≤ A t)
    (hKtbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |kT t x| ≤ Kt t)
    (hKxbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |kX t x| ≤ Kx t)
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |h t x| ≤ Rb t)
    -- the path data
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hstart : ∀ u, Y 0 (Phi 0 u) = a.1 u) (hfinish : ∀ u, Y T (Phi T u) = b.1 u)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0)
    (hmbd : ∀ t u, |en t (Phi t u)| ≤ m t)
    (hmsup : ∀ t, ∀ j ≤ 2,
      MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) :
    ∃ Γ : NormalPath a b, Γ.T = T ∧ (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
      Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ := by
  -- the family read in the marking is a variable-speed family
  have hfam : IsVariableSpeedFamily P0 P1 khat G1 Cg (fun t u => Y t (Phi t u)) m :=
    isVariableSpeedFamily_of_gauge_flow_fundamental hY halpha hlip hcont hPhid hPhi0
      hxd hxcont hxxd hxxcont hxxK hP1 hG1 hCnn hC2nn hcost hcost2 halphaC1 hkC1
      halphaT hkT hkX halphaTc hkTc hkXc hkc hKxnn hcostA hcostK hQpos hQd hqp hkper
      halphaper hbase hk hC hC2 hAbd hKtbd hKxbd hRbd
  -- and it is a normal path
  obtain ⟨Γ, hΓT, hΓX, -, -, hΓm, hΓcost⟩ :=
    exists_normalPath_of_gauge_marking (a := a) (b := b) (xi := fun t s => -h t s)
      (en := en) (alpha := alpha) (m := m) hT hYC1 hY hYt
      (fun u t => by simpa using hPhid u t)
      (fun t => continuous_flow_initial hlip hPhid hPhi0 t)
      hencont halphaC1.continuous hstart hfinish hmc hm0 hmstop hmbd hmsup
  refine ⟨Γ, hΓT, hΓX, hΓm, by rw [hΓcost], ?_⟩
  have hX : Γ.X = fun t u => Y t (Phi t u) := funext fun t => funext fun u => hΓX t u
  show IsVariableSpeedFamily P0 P1 khat G1 Cg Γ.X Γ.m
  rw [hX, hΓm]
  exact hfam

end GaugeFlowPathFundamental
