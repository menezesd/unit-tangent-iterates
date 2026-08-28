import Mathlib
import UnitTangentIterates.GaugeJacobiCostFundamental
import UnitTangentIterates.GaugeMarkedDataOfFrameBundle
import UnitTangentIterates.GaugeBaseFlow

/-!
# The comparison path of a bundle of frame data, with the bounds on one period

`GaugeMarkedDataOfFrameBundle.exists_variableSpeed_normalPath_of_frameBundle`
produces the marking itself — the gauge flow of the tangential rate of a bundle
of unit-speed frame data — together with the comparison path of the `C²`
estimate, asking its bounds globally in the arclength.

This file is its fundamental-domain form.  For a family of closed curves whose
arclength period `Q t` moves, the tangential component drifts,
`ξ(t, x + Q t) = ξ(t, x) − Q'(t)`, so a global bound on it is available only
when the period stands still; here the bound is asked on one period `[0, Q t]`
only, and the drift relation is given instead.  The base point of the marking is
fixed by `GaugeBaseFlow.gaugeFlow_base_fixed`, from the vanishing of the
tangential component there.

Main result: `exists_variableSpeed_normalPath_of_frameBundle_fundamental`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeFrameBundleFundamental

open GaugeFlowDerivCost GaugeFlowVariableSpeedPath GaugePathRearFamily
  NormalPathC2IncrementVariableSpeed UniformFrameBounds GaugeJacobiCostFundamental

variable {Y : ℝ → ℝ → ℂ}
  {alpha k en enS enSS g gS alphaT kT kX : ℝ → ℝ → ℝ}
  {C C2 Kx Rb S0 Dd m Q Q' : ℝ → ℝ} {turn T : ℝ} {P0 khat kappa2 c d r kx : ℝ}

/-- **The comparison path of a family carried by a bundle of frame data, with
every bound asked on one period only.**

The hypotheses are those of
`GaugeMarkedDataOfFrameBundle.exists_variableSpeed_normalPath_of_frameBundle`,
with all its pointwise bounds asked only for `x ∈ [0, Q t]`, and with the
closing structure of the family — the drift relation of the tangential
component, the periodicity of the curvature, the increment of the tangent angle
over one period and the vanishing of the tangential component at the base
point — given in exchange.  Nothing is assumed about the motion of the
arclength period. -/
theorem exists_variableSpeed_normalPath_of_frameBundle_fundamental_with_eta_c2flow
    (D : GaugeFrameData) (hv1 : ∀ t x, D.v t x = 1)
    -- the family, in its own arclength, and its motion
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      ((D.xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hkappa2 : 0 ≤ kappa2)
    (hCc : Continuous C) (hC2c : Continuous C2)
    (hCm : ∀ t, C t ≤ khat * m t) (hC2m : ∀ t, C2 t ≤ kappa2 * m t)
    -- the frame data of the slices
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
      HasDerivAt (fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    -- the inverse Jacobi ODE
    (hgSd : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    -- the closing structure of the family
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hxiqp : ∀ t x, D.xi t (x + Q t) = D.xi t x - Q' t)
    (hkper : ∀ t, Function.Periodic (k t) (Q t))
    (halphaper : ∀ t x, alpha t (x + Q t) = alpha t x + turn)
    (hxi0 : ∀ t, D.xi t 0 = 0)
    -- the bounds, on one period only
    (hk : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |k t x| ≤ khat)
    (hC : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1 t x| ≤ C t)
    (hC2 : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2 t x| ≤ C2 t)
    (hKxbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |kX t x| ≤ Kx t)
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |D.xi t x| ≤ Rb t)
    (hgbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |g t x| ≤ S0 t)
    (henbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |en t x| ≤ S0 t)
    (hgSbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |gS t x| ≤ Dd t)
    -- the comparisons with the cost density and the numerical conditions
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : 2 * c + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2 * c) + khat ^ 2 * c + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Q 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, Y 0 (Phi 0 u) = a.1 u) → (∀ u, Y T (Phi T u) = b.1 u) →
        (∀ t u, |en t (Phi t u)| ≤ m t) →
        (∀ t, ∀ j ≤ 2,
          MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) →
        ∃ Γ : NormalPath a b, Γ.T = T ∧ (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
          (∀ t u, Γ.eta t u = en t (Phi t u)) ∧
          (∀ t u, Phi t (u + 1) = Phi t u + Q t) ∧
          (∀ t u, HasDerivAt (Phi t)
            (FlowDerivative.flowDeriv (GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1) Phi
              (Q 0) t u) u) ∧
          (∀ t u, HasDerivAt (fun v => FlowDerivative.flowDeriv
            (GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1) Phi (Q 0) t v)
            (GaugeFlowTimeDerivative.flowDeriv2
              (GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
              (GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2) Phi
              (Q 0) t u) u) ∧
          (∀ t, Continuous (fun u => FlowDerivative.flowDeriv
            (GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1) Phi (Q 0) t u)) ∧
          (∀ t, Continuous (fun u => GaugeFlowTimeDerivative.flowDeriv2
            (GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
            (GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2) Phi (Q 0) t u)) ∧
          (∀ t u, FlowDerivative.flowDeriv (GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
            Phi (Q 0) t u ≤ costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t)) ∧
          (∀ t u, |GaugeFlowTimeDerivative.flowDeriv2
            (GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
            (GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2) Phi (Q 0) t u| ≤
              costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t)) ∧
          Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
          IsVariableSpeedNormalPath P0 (costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t)) khat
            (costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t))
            (khat * costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t)
              + kappa2 * costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t) ^ 2) Γ := by
  have hell : (0 : ℝ) < Q 0 := hQpos 0
  -- the field of the marking is the tangential rate of the bundle
  have hgr : ∀ t x, GaugeRate.gaugeRate D.xi D.v t x = -D.xi t x := by
    intro t x
    rw [GaugeRate.gaugeRate, hv1 t x, div_one]
  -- the analytic hypotheses of the marking, from the bundle
  obtain ⟨-, hcont, hxd, hxcont, hxxd, hxxcont, -⟩ :=
    GaugeRate.gaugeRate_flow_hypotheses_of_bounds (L := D.rateLip) (K2 := D.rateBound2)
      D.rateLip_nonneg D.hxi D.hxi1 D.hv D.hv1 D.hvne D.hxic D.hxi1c D.hxi2c D.hvc D.hv1c
      D.hv2c D.hrate1 D.hrate2
  -- the marking itself, and its base point
  obtain ⟨Phi, hPhi0, hPhid⟩ := exists_gaugeFlow_of_frameData D hell
  have hbase : ∀ t, Phi t 0 = 0 := fun t =>
    GaugeBaseFlow.gaugeFlow_base_fixed D (fun r => hPhid 0 r) (by rw [hPhi0 0, mul_zero])
      hxi0 t
  refine ⟨Phi, hPhi0, hbase, hPhid, ?_⟩
  intro a b hstart hfinish hmbd hmsup
  -- the motion, written with the field of the marking
  have hYt' : ∀ t s, HasDerivAt (fun r => Y r s)
      (((-GaugeRate.gaugeRate D.xi D.v t s : ℝ) : ℂ)
          * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t := by
    intro t s
    simpa only [hgr t s, neg_neg] using hYt t s
  have hmixed' : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => ((-GaugeRate.gaugeRate D.xi D.v t x : ℝ) : ℂ)
          * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s := by
    intro t s
    obtain ⟨W, hW1, hW2⟩ := hmixed t s
    refine ⟨W, hW1, ?_⟩
    have hfun : (fun x => ((-GaugeRate.gaugeRate D.xi D.v t x : ℝ) : ℂ)
        * Complex.exp (Complex.I * (alpha t x : ℂ))
      + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))))
        = fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
          + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))) := by
      funext x
      rw [hgr t x, neg_neg]
    rw [hfun]
    exact hW2
  -- the bound on the field, and its quasi-periodicity
  have hRbd' : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |GaugeRate.gaugeRate D.xi D.v t x| ≤ Rb t := by
    intro t x hx
    rw [hgr t x, abs_neg]
    exact hRbd t x hx
  have hqp : ∀ t x, GaugeRate.gaugeRate D.xi D.v t (x + Q t)
      = GaugeRate.gaugeRate D.xi D.v t x + Q' t := by
    intro t x
    rw [hgr t (x + Q t), hgr t x, hxiqp t x]
    ring
  exact exists_variableSpeed_normalPath_of_jacobi_cost_fundamental_with_eta_c2flow (Y := Y)
    (alpha := alpha) (k := k) (en := en) (enS := enS) (enSS := enSS) (g := g) (gS := gS)
    (h := GaugeRate.gaugeRate D.xi D.v) (hx := GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
    (hxx := GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2) (Phi := Phi)
    (alphaT := alphaT) (kT := kT) (kX := kX) (C := C) (C2 := C2) (Kx := Kx) (Rb := Rb)
    (S0 := S0) (D := Dd) (m := m) (Q := Q) (Q' := Q') (turn := turn) (T := T) (P0 := P0)
    (khat := khat) (kappa2 := kappa2) (c := c) (d := d) (r := r) (kx := kx)
    hYC1 hY hYt' halpha hcont (fun u t => hPhid u t) hPhi0 hxd hxcont hxxd hxxcont
    hkappa2 hCc hC2c hCm hC2m halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc hkc
    hKxnn henS henSS halphaTS hmixed' hgSd hjacobi hQpos hQd hqp hkper halphaper hbase
    hk hC hC2 hKxbd hRbd' hgbd henbd hgSbd hS0m hDm hRbm hKxm hr hm0 hnumA hnumK hT
    hencont hstart hfinish hmc hmstop hmbd hmsup



theorem exists_variableSpeed_normalPath_of_frameBundle_fundamental_with_eta
    (D : GaugeFrameData) (hv1 : ∀ t x, D.v t x = 1)
    -- the family, in its own arclength, and its motion
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      ((D.xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hkappa2 : 0 ≤ kappa2)
    (hCc : Continuous C) (hC2c : Continuous C2)
    (hCm : ∀ t, C t ≤ khat * m t) (hC2m : ∀ t, C2 t ≤ kappa2 * m t)
    -- the frame data of the slices
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
      HasDerivAt (fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    -- the inverse Jacobi ODE
    (hgSd : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    -- the closing structure of the family
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hxiqp : ∀ t x, D.xi t (x + Q t) = D.xi t x - Q' t)
    (hkper : ∀ t, Function.Periodic (k t) (Q t))
    (halphaper : ∀ t x, alpha t (x + Q t) = alpha t x + turn)
    (hxi0 : ∀ t, D.xi t 0 = 0)
    -- the bounds, on one period only
    (hk : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |k t x| ≤ khat)
    (hC : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1 t x| ≤ C t)
    (hC2 : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2 t x| ≤ C2 t)
    (hKxbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |kX t x| ≤ Kx t)
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |D.xi t x| ≤ Rb t)
    (hgbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |g t x| ≤ S0 t)
    (henbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |en t x| ≤ S0 t)
    (hgSbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |gS t x| ≤ Dd t)
    -- the comparisons with the cost density and the numerical conditions
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : 2 * c + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2 * c) + khat ^ 2 * c + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Q 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, Y 0 (Phi 0 u) = a.1 u) → (∀ u, Y T (Phi T u) = b.1 u) →
        (∀ t u, |en t (Phi t u)| ≤ m t) →
        (∀ t, ∀ j ≤ 2,
          MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) →
        ∃ Γ : NormalPath a b, Γ.T = T ∧ (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
          (∀ t u, Γ.eta t u = en t (Phi t u)) ∧ Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
          IsVariableSpeedNormalPath P0 (costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t)) khat
            (costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t))
            (khat * costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t)
              + kappa2 * costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t) ^ 2) Γ := by
  have hell : (0 : ℝ) < Q 0 := hQpos 0
  -- the field of the marking is the tangential rate of the bundle
  have hgr : ∀ t x, GaugeRate.gaugeRate D.xi D.v t x = -D.xi t x := by
    intro t x
    rw [GaugeRate.gaugeRate, hv1 t x, div_one]
  -- the analytic hypotheses of the marking, from the bundle
  obtain ⟨-, hcont, hxd, hxcont, hxxd, hxxcont, -⟩ :=
    GaugeRate.gaugeRate_flow_hypotheses_of_bounds (L := D.rateLip) (K2 := D.rateBound2)
      D.rateLip_nonneg D.hxi D.hxi1 D.hv D.hv1 D.hvne D.hxic D.hxi1c D.hxi2c D.hvc D.hv1c
      D.hv2c D.hrate1 D.hrate2
  -- the marking itself, and its base point
  obtain ⟨Phi, hPhi0, hPhid⟩ := exists_gaugeFlow_of_frameData D hell
  have hbase : ∀ t, Phi t 0 = 0 := fun t =>
    GaugeBaseFlow.gaugeFlow_base_fixed D (fun r => hPhid 0 r) (by rw [hPhi0 0, mul_zero])
      hxi0 t
  refine ⟨Phi, hPhi0, hbase, hPhid, ?_⟩
  intro a b hstart hfinish hmbd hmsup
  -- the motion, written with the field of the marking
  have hYt' : ∀ t s, HasDerivAt (fun r => Y r s)
      (((-GaugeRate.gaugeRate D.xi D.v t s : ℝ) : ℂ)
          * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t := by
    intro t s
    simpa only [hgr t s, neg_neg] using hYt t s
  have hmixed' : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => ((-GaugeRate.gaugeRate D.xi D.v t x : ℝ) : ℂ)
          * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s := by
    intro t s
    obtain ⟨W, hW1, hW2⟩ := hmixed t s
    refine ⟨W, hW1, ?_⟩
    have hfun : (fun x => ((-GaugeRate.gaugeRate D.xi D.v t x : ℝ) : ℂ)
        * Complex.exp (Complex.I * (alpha t x : ℂ))
      + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))))
        = fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
          + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))) := by
      funext x
      rw [hgr t x, neg_neg]
    rw [hfun]
    exact hW2
  -- the bound on the field, and its quasi-periodicity
  have hRbd' : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |GaugeRate.gaugeRate D.xi D.v t x| ≤ Rb t := by
    intro t x hx
    rw [hgr t x, abs_neg]
    exact hRbd t x hx
  have hqp : ∀ t x, GaugeRate.gaugeRate D.xi D.v t (x + Q t)
      = GaugeRate.gaugeRate D.xi D.v t x + Q' t := by
    intro t x
    rw [hgr t (x + Q t), hgr t x, hxiqp t x]
    ring
  exact exists_variableSpeed_normalPath_of_jacobi_cost_fundamental_with_eta (Y := Y)
    (alpha := alpha) (k := k) (en := en) (enS := enS) (enSS := enSS) (g := g) (gS := gS)
    (h := GaugeRate.gaugeRate D.xi D.v) (hx := GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
    (hxx := GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2) (Phi := Phi)
    (alphaT := alphaT) (kT := kT) (kX := kX) (C := C) (C2 := C2) (Kx := Kx) (Rb := Rb)
    (S0 := S0) (D := Dd) (m := m) (Q := Q) (Q' := Q') (turn := turn) (T := T) (P0 := P0)
    (khat := khat) (kappa2 := kappa2) (c := c) (d := d) (r := r) (kx := kx)
    hYC1 hY hYt' halpha hcont (fun u t => hPhid u t) hPhi0 hxd hxcont hxxd hxxcont
    hkappa2 hCc hC2c hCm hC2m halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc hkc
    hKxnn henS henSS halphaTS hmixed' hgSd hjacobi hQpos hQd hqp hkper halphaper hbase
    hk hC hC2 hKxbd hRbd' hgbd henbd hgSbd hS0m hDm hRbm hKxm hr hm0 hnumA hnumK hT
    hencont hstart hfinish hmc hmstop hmbd hmsup


/-- Compatibility form retaining the historical result shape. -/
theorem exists_variableSpeed_normalPath_of_frameBundle_fundamental
    (D : GaugeFrameData) (hv1 : ∀ t x, D.v t x = 1)
    -- the family, in its own arclength, and its motion
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      ((D.xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hkappa2 : 0 ≤ kappa2)
    (hCc : Continuous C) (hC2c : Continuous C2)
    (hCm : ∀ t, C t ≤ khat * m t) (hC2m : ∀ t, C2 t ≤ kappa2 * m t)
    -- the frame data of the slices
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
      HasDerivAt (fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    -- the inverse Jacobi ODE
    (hgSd : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    -- the closing structure of the family
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hxiqp : ∀ t x, D.xi t (x + Q t) = D.xi t x - Q' t)
    (hkper : ∀ t, Function.Periodic (k t) (Q t))
    (halphaper : ∀ t x, alpha t (x + Q t) = alpha t x + turn)
    (hxi0 : ∀ t, D.xi t 0 = 0)
    -- the bounds, on one period only
    (hk : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |k t x| ≤ khat)
    (hC : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1 t x| ≤ C t)
    (hC2 : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2 t x| ≤ C2 t)
    (hKxbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |kX t x| ≤ Kx t)
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |D.xi t x| ≤ Rb t)
    (hgbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |g t x| ≤ S0 t)
    (henbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |en t x| ≤ S0 t)
    (hgSbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |gS t x| ≤ Dd t)
    -- the comparisons with the cost density and the numerical conditions
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : 2 * c + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2 * c) + khat ^ 2 * c + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Q 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, Y 0 (Phi 0 u) = a.1 u) → (∀ u, Y T (Phi T u) = b.1 u) →
        (∀ t u, |en t (Phi t u)| ≤ m t) →
        (∀ t, ∀ j ≤ 2,
          MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) →
        ∃ Γ : NormalPath a b, Γ.T = T ∧ (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
          Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
          IsVariableSpeedNormalPath P0 (costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t)) khat
            (costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t))
            (khat * costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t)
              + kappa2 * costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t) ^ 2) Γ := by
  have hell : (0 : ℝ) < Q 0 := hQpos 0
  -- the field of the marking is the tangential rate of the bundle
  have hgr : ∀ t x, GaugeRate.gaugeRate D.xi D.v t x = -D.xi t x := by
    intro t x
    rw [GaugeRate.gaugeRate, hv1 t x, div_one]
  -- the analytic hypotheses of the marking, from the bundle
  obtain ⟨-, hcont, hxd, hxcont, hxxd, hxxcont, -⟩ :=
    GaugeRate.gaugeRate_flow_hypotheses_of_bounds (L := D.rateLip) (K2 := D.rateBound2)
      D.rateLip_nonneg D.hxi D.hxi1 D.hv D.hv1 D.hvne D.hxic D.hxi1c D.hxi2c D.hvc D.hv1c
      D.hv2c D.hrate1 D.hrate2
  -- the marking itself, and its base point
  obtain ⟨Phi, hPhi0, hPhid⟩ := exists_gaugeFlow_of_frameData D hell
  have hbase : ∀ t, Phi t 0 = 0 := fun t =>
    GaugeBaseFlow.gaugeFlow_base_fixed D (fun r => hPhid 0 r) (by rw [hPhi0 0, mul_zero])
      hxi0 t
  refine ⟨Phi, hPhi0, hbase, hPhid, ?_⟩
  intro a b hstart hfinish hmbd hmsup
  -- the motion, written with the field of the marking
  have hYt' : ∀ t s, HasDerivAt (fun r => Y r s)
      (((-GaugeRate.gaugeRate D.xi D.v t s : ℝ) : ℂ)
          * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t := by
    intro t s
    simpa only [hgr t s, neg_neg] using hYt t s
  have hmixed' : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => ((-GaugeRate.gaugeRate D.xi D.v t x : ℝ) : ℂ)
          * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s := by
    intro t s
    obtain ⟨W, hW1, hW2⟩ := hmixed t s
    refine ⟨W, hW1, ?_⟩
    have hfun : (fun x => ((-GaugeRate.gaugeRate D.xi D.v t x : ℝ) : ℂ)
        * Complex.exp (Complex.I * (alpha t x : ℂ))
      + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))))
        = fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
          + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))) := by
      funext x
      rw [hgr t x, neg_neg]
    rw [hfun]
    exact hW2
  -- the bound on the field, and its quasi-periodicity
  have hRbd' : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t),
      |GaugeRate.gaugeRate D.xi D.v t x| ≤ Rb t := by
    intro t x hx
    rw [hgr t x, abs_neg]
    exact hRbd t x hx
  have hqp : ∀ t x, GaugeRate.gaugeRate D.xi D.v t (x + Q t)
      = GaugeRate.gaugeRate D.xi D.v t x + Q' t := by
    intro t x
    rw [hgr t (x + Q t), hgr t x, hxiqp t x]
    ring
  exact exists_variableSpeed_normalPath_of_jacobi_cost_fundamental (Y := Y)
    (alpha := alpha) (k := k) (en := en) (enS := enS) (enSS := enSS) (g := g) (gS := gS)
    (h := GaugeRate.gaugeRate D.xi D.v) (hx := GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
    (hxx := GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2) (Phi := Phi)
    (alphaT := alphaT) (kT := kT) (kX := kX) (C := C) (C2 := C2) (Kx := Kx) (Rb := Rb)
    (S0 := S0) (D := Dd) (m := m) (Q := Q) (Q' := Q') (turn := turn) (T := T) (P0 := P0)
    (khat := khat) (kappa2 := kappa2) (c := c) (d := d) (r := r) (kx := kx)
    hYC1 hY hYt' halpha hcont (fun u t => hPhid u t) hPhi0 hxd hxcont hxxd hxxcont
    hkappa2 hCc hC2c hCm hC2m halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc hkc
    hKxnn henS henSS halphaTS hmixed' hgSd hjacobi hQpos hQd hqp hkper halphaper hbase
    hk hC hC2 hKxbd hRbd' hgbd henbd hgSbd hS0m hDm hRbm hKxm hr hm0 hnumA hnumK hT
    hencont hstart hfinish hmc hmstop hmbd hmsup

end GaugeFrameBundleFundamental
