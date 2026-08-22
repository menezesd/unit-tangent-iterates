import Mathlib
import UnitTangentIterates.GaugeNormalRateFundamental
import UnitTangentIterates.GaugeMarkedDataOfJacobi

/-!
# The comparison path from the inverse Jacobi ODE, with the bounds on one period

`GaugeMarkedDataOfJacobi.exists_variableSpeed_normalPath_of_jacobi` produces the
comparison path of a family of rears from the inverse Jacobi ODE `∂_sη = g − η`
satisfied by its normal rate, asking its bounds globally in the arclength.

This file is its fundamental-domain form: every pointwise bound — on the
curvature, on the two space derivatives of the field of the marking, on the
arclength derivative of the curvature, on the field itself, and on `η`, `g`,
`∂_s g` — is asked only for `x ∈ [0, Q t]`, the closing structure of the family
being given in exchange, and nothing being assumed about the motion of the
arclength period.

Main result: `exists_variableSpeed_normalPath_of_jacobi_fundamental`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeJacobiFundamental

open GaugeFlowVariableSpeedPath JacobiNormalRateBounds
  NormalPathC2IncrementVariableSpeed GaugeNormalRateFundamental

variable {a b : Data} {Y : ℝ → ℝ → ℂ}
  {alpha k en enS enSS g gS h hx hxx Phi alphaT kT kX : ℝ → ℝ → ℝ}
  {C C2 Kx Rb S0 D m Q Q' : ℝ → ℝ} {K K2 : NNReal} {turn T : ℝ}
  {P0 P1 khat G1 Cg c d r kx : ℝ}

/-- **The comparison path of a family of rears, with every bound asked on one
period only.**

The hypotheses are those of
`GaugeMarkedDataOfJacobi.exists_variableSpeed_normalPath_of_jacobi`, with all its
pointwise bounds asked only for `x ∈ [0, Q t]` and with the closing structure of
the family given in exchange. -/
theorem exists_variableSpeed_normalPath_of_jacobi_fundamental
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
    -- the inverse Jacobi ODE
    (hgSd : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
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
    (hgbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |g t x| ≤ S0 t)
    (henbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |en t x| ≤ S0 t)
    (hgSbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |gS t x| ≤ D t)
    -- the comparisons with the cost density and the numerical conditions
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, D t ≤ d * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : 2 * c + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2 * c) + khat ^ 2 * c + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
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
  -- the two derived bounds of the Jacobi ODE, on one period
  have hb1 : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |enS t x| ≤ 2 * S0 t := by
    intro t x hx
    rw [enS_eq hjacobi henS t x]
    calc |g t x - en t x| ≤ |g t x| + |en t x| := abs_sub _ _
      _ ≤ S0 t + S0 t := add_le_add (hgbd t x hx) (henbd t x hx)
      _ = 2 * S0 t := by ring
  have hb2 : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |enSS t x| ≤ D t + 2 * S0 t := by
    intro t x hx
    rw [enSS_eq hgSd hjacobi henS henSS t x]
    calc |gS t x - enS t x| ≤ |gS t x| + |enS t x| := abs_sub _ _
      _ ≤ D t + 2 * S0 t := add_le_add (hgSbd t x hx) (hb1 t x hx)
  obtain ⟨hm0', hm1, hm2⟩ := jacobi_cost_constants (S0 := S0) (D := D) (m := m) hS0m hDm
  exact exists_variableSpeed_normalPath_of_normal_rate_fundamental
    (S0 := S0) (S1 := fun t => 2 * S0 t) (S2 := fun t => D t + 2 * S0 t)
    (c0 := c) (c1 := 2 * c) (c2 := d + 2 * c)
    hYC1 hY hYt halpha hlip hcont hPhid hPhi0 hxd hxcont hxxd hxxcont hxxK hP1 hG1
    hCnn hC2nn hcost hcost2 halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc hkc hKxnn
    henS henSS halphaTS hmixed hQpos hQd hqp hkper halphaper hbase hk hC hC2 hKxbd hRbd
    henbd hb1 hb2 hm0' hm1 hm2 hRbm hKxm hr hm0 hnumA hnumK hT hencont hstart hfinish
    hmc hmstop hmbd hmsup

end GaugeJacobiFundamental
