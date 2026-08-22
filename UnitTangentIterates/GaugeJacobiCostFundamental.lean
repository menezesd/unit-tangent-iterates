import Mathlib
import UnitTangentIterates.GaugeJacobiFundamental
import UnitTangentIterates.GaugeMarkedDataOfJacobiCost

/-!
# The comparison path with the flow constants from the cost, on one period

`GaugeMarkedDataOfJacobiCost.exists_variableSpeed_normalPath_of_jacobi_cost`
produces the comparison path of a family of rears with the Lipschitz constant of
the field of the gauge marking and the two bounds on its flow derivatives read
off the *cost* of the path, as the explicit constants `costP1 ℓ κ̂ M` and
`costG1 ℓ κ̂ κ₂ M`.

This file is its fundamental-domain form.  The two space derivatives of the
field are periodic in the arclength — they carry no drift, however the period
moves (`GaugeFlowFundamentalDomain.periodic_deriv_of_quasiPeriodic`) — so their
bounds may be asked on one period and hold everywhere; every other pointwise
bound of the statement, including the one on the field itself, is asked on the
fundamental domain `[0, Q t]` only.

Main result: `exists_variableSpeed_normalPath_of_jacobi_cost_fundamental`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeJacobiCostFundamental

open GaugeFlowVariableSpeedPath GaugeFlowDerivCost NormalPathC2IncrementVariableSpeed
  GaugeFlowFundamentalDomain GaugeJacobiFundamental

variable {a b : Data} {Y : ℝ → ℝ → ℂ}
  {alpha k en enS enSS g gS h hx hxx Phi alphaT kT kX : ℝ → ℝ → ℝ}
  {C C2 Kx Rb S0 D m Q Q' : ℝ → ℝ} {turn T : ℝ}
  {P0 khat kappa2 c d r kx : ℝ}

/-- **The comparison path of a family of rears, with the constants of the
marking produced by the cost and every bound asked on one period only.**

The hypotheses are those of
`GaugeMarkedDataOfJacobiCost.exists_variableSpeed_normalPath_of_jacobi_cost`,
with all its pointwise bounds asked only for `x ∈ [0, Q t]` and with the closing
structure of the family given in exchange.  Nothing is assumed about the motion
of the arclength period. -/
theorem exists_variableSpeed_normalPath_of_jacobi_cost_fundamental
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      (((-h t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hcont : Continuous (uncurry h))
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (hxcont : Continuous (uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x) (hxxcont : Continuous (uncurry hxx))
    (hkappa2 : 0 ≤ kappa2)
    (hCc : Continuous C) (hC2c : Continuous C2)
    (hCm : ∀ t, C t ≤ khat * m t) (hC2m : ∀ t, C2 t ≤ kappa2 * m t)
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
      IsVariableSpeedNormalPath P0 (costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t)) khat
        (costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t))
        (khat * costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t)
          + kappa2 * costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t) ^ 2) Γ := by
  set M : ℝ := ∫ t in (0 : ℝ)..T, m t with hMdef
  set P1 : ℝ := costP1 (Q 0) khat M with hP1def
  set G1 : ℝ := costG1 (Q 0) khat kappa2 M with hG1def
  have hell : (0 : ℝ) < Q 0 := hQpos 0
  ------------------------------------------------------------------
  -- the two space derivatives of the field are periodic, so their bounds
  -- on one period are bounds everywhere
  ------------------------------------------------------------------
  have hxper : ∀ t, Function.Periodic (hx t) (Q t) :=
    periodic_deriv_of_quasiPeriodic hxd hqp
  have hxxper : ∀ t, Function.Periodic (hxx t) (Q t) :=
    periodic_deriv_of_periodic hxxd hxper
  have hCg : ∀ t x, |hx t x| ≤ C t := fun t x =>
    bound_of_periodic (hQpos t) (hxper t) (hC t) x
  have hC2g : ∀ t x, |hxx t x| ≤ C2 t := fun t x =>
    bound_of_periodic (hQpos t) (hxxper t) (hC2 t) x
  ------------------------------------------------------------------
  -- the constants of the marking, produced by the cost
  ------------------------------------------------------------------
  have hCnn : ∀ t, 0 ≤ C t := fun t => (abs_nonneg _).trans (hCg t 0)
  have hC2nn : ∀ t, 0 ≤ C2 t := fun t => (abs_nonneg _).trans (hC2g t 0)
  have hCstop : ∀ s ∉ Ioo (0 : ℝ) T, C s = 0 := by
    intro s hs
    have := (hCm s).trans_eq (by rw [hmstop s hs, mul_zero])
    exact le_antisymm this (hCnn s)
  have hC2stop : ∀ s ∉ Ioo (0 : ℝ) T, C2 s = 0 := by
    intro s hs
    have := (hC2m s).trans_eq (by rw [hmstop s hs, mul_zero])
    exact le_antisymm this (hC2nn s)
  obtain ⟨B, hBnn, hB⟩ := exists_bound_of_stop hCc hCnn hCstop hT
  obtain ⟨B2, hB2nn, hB2⟩ := exists_bound_of_stop hC2c hC2nn hC2stop hT
  have hlip : ∀ t, LipschitzWith (Real.toNNReal B) (h t) :=
    lipschitzWith_of_deriv_bound hBnn hxd (fun s x => (hCg s x).trans (hB s))
  have hxxK : ∀ s x, |hxx s x| ≤ ((Real.toNNReal B2 : NNReal) : ℝ) := by
    intro s x
    rw [Real.coe_toNNReal _ hB2nn]
    exact (hC2g s x).trans (hB2 s)
  have hP1 : ∀ t u, FlowDerivative.flowDeriv hx Phi (Q 0) t u ≤ P1 := fun t u =>
    flowDeriv_le_costP1 hPhid hxcont hell hCg hCc hCstop hmc hCm hT t u
  have hG1 : ∀ t u, |GaugeFlowTimeDerivative.flowDeriv2 hx hxx Phi (Q 0) t u| ≤ G1 :=
    fun t u => abs_flowDeriv2_le_costG1 hPhid hxcont hxxcont hell hCg hCc hCstop hC2g
      hC2c hC2stop hmc hCm hC2m hT t u
  ------------------------------------------------------------------
  -- the two numerical comparisons
  ------------------------------------------------------------------
  have hMnn : 0 ≤ M := intervalIntegral.integral_nonneg hT.le fun s _ => hm0 s
  have hP1nn : 0 ≤ P1 := (costP1_pos hell).le
  have hG1nn : 0 ≤ G1 := by
    have : 0 ≤ kappa2 * M := mul_nonneg hkappa2 hMnn
    exact mul_nonneg (by positivity) this
  have hcost : ∀ t, C t * P1 ≤ khat * P1 * m t := by
    intro t
    calc C t * P1 ≤ (khat * m t) * P1 := mul_le_mul_of_nonneg_right (hCm t) hP1nn
      _ = khat * P1 * m t := by ring
  have hcost2 : ∀ t, C t * G1 + C2 t * P1 ^ 2
      ≤ (khat * G1 + kappa2 * P1 ^ 2) * m t := by
    intro t
    have h1 : C t * G1 ≤ khat * m t * G1 := mul_le_mul_of_nonneg_right (hCm t) hG1nn
    have h2 : C2 t * P1 ^ 2 ≤ kappa2 * m t * P1 ^ 2 :=
      mul_le_mul_of_nonneg_right (hC2m t) (by positivity)
    nlinarith [h1, h2]
  exact exists_variableSpeed_normalPath_of_jacobi_fundamental (K := Real.toNNReal B)
    (K2 := Real.toNNReal B2) (C := C) (C2 := C2) (Cg := khat * G1 + kappa2 * P1 ^ 2)
    hYC1 hY hYt halpha hlip hcont hPhid hPhi0 hxd hxcont hxxd hxxcont hxxK hP1 hG1
    hCnn hC2nn hcost hcost2 halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc hkc hKxnn
    henS henSS halphaTS hmixed hgSd hjacobi hQpos hQd hqp hkper halphaper hbase hk hC
    hC2 hKxbd hRbd hgbd henbd hgSbd hS0m hDm hRbm hKxm hr hm0 hnumA hnumK hT hencont
    hstart hfinish hmc hmstop hmbd hmsup

end GaugeJacobiCostFundamental
