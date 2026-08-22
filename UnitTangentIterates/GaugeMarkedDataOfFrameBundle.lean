import Mathlib
import UnitTangentIterates.GaugeMarkedDataOfJacobiCost
import UnitTangentIterates.GaugePathRearFamily

/-!
# The variable-speed normal path of a family carried by a bundle of frame data

`GaugeMarkedDataOfJacobiCost.exists_variableSpeed_normalPath_of_jacobi_cost`
produces the comparison path `Γ'` of the `C²` estimate from a family written in
its own arclength together with a marking `Φ`, which it asks for as a datum:
the field `h` of the marking, its two space derivatives, and the flow equation
`∂_tΦ = h(t, Φ)`.

For the family of selected rears none of this has to be assumed.  The tangential
component `ξ` of the motion of the family, with the speed `v` of its slices, is
bundled together with its space derivatives and the bounds on the *rate*
`−ξ/v` in a `UniformFrameBounds.GaugeFrameData`, and

* `GaugeRate.gaugeRate_flow_hypotheses_of_bounds` turns the bundle into exactly
  the analytic hypotheses the marking needs — the rate is jointly continuous and
  has two jointly continuous space derivatives, `gaugeRate1` and `gaugeRate2`;
* `GaugePathRearFamily.exists_gaugeFlow_of_frameData` produces the marking
  itself, the flow of the rate started at the affine marking of period `ℓ`.

So the whole block about the marking is discharged by the bundle, and what
remains to be supplied about the field are the two *density* bounds — that
`gaugeRate1` and `gaugeRate2` are dominated by `κ̂` and by `κ₂` times the cost
density — which along a path of rears are the tangential estimates of
`RearOwnTangentialCost.lean` and `RearOwnTangentialCostC2.lean`.

For a family carried in its own arclength the speed is `1`, so the field of the
marking is `−ξ` and the velocity of the family is `∂_tY = ξ e^{iα} + η i e^{iα}`,
the form in which the motion is stated here.

Main result: `exists_variableSpeed_normalPath_of_frameBundle`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeMarkedDataOfFrameBundle

open GaugeFlowDerivCost GaugeFlowVariableSpeedPath GaugeMarkedDataOfJacobiCost
  GaugePathRearFamily NormalPathC2IncrementVariableSpeed UniformFrameBounds

variable {Y : ℝ → ℝ → ℂ}
  {alpha k en enS enSS g gS alphaT kT kX : ℝ → ℝ → ℝ}
  {C C2 Kx Rb S0 Dd m : ℝ → ℝ} {ell T : ℝ} {P0 khat kappa2 c d r kx : ℝ}

/-- **The comparison path of the `C²` estimate, for a family carried by a bundle
of frame data.**

The family `Y` is written in its own arclength, with tangent angle `α` and
curvature `k`, and moves with tangential component `ξ` — the one of the bundle
`D` — and normal rate `η` solving the inverse Jacobi ODE `∂_sη = g − η`.  The
marking is produced, not assumed: it is the gauge flow of the rate `−ξ` of the
bundle, started at the affine marking of period `ℓ`; its two derivatives in the
initial condition are bounded by the explicit constants `costP1 ℓ κ̂ M` and
`costG1 ℓ κ̂ κ₂ M` of the total cost `M = ∫₀^T m`. -/
theorem exists_variableSpeed_normalPath_of_frameBundle
    (D : GaugeFrameData) (hv1 : ∀ t x, D.v t x = 1) (hell : 0 < ell)
    -- the family, in its own arclength, and its motion
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      ((D.xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hk : ∀ t x, |k t x| ≤ khat) (hkappa2 : 0 ≤ kappa2)
    -- the two densities dominating the space derivatives of the rate
    (hC : ∀ t x, |GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1 t x| ≤ C t)
    (hC2 : ∀ t x, |GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2 t x| ≤ C2 t)
    (hCc : Continuous C) (hC2c : Continuous C2)
    (hCm : ∀ t, C t ≤ khat * m t) (hC2m : ∀ t, C2 t ≤ kappa2 * m t)
    -- the frame data of the slices
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxbd : ∀ t x, |kX t x| ≤ Kx t) (hRbd : ∀ t x, |D.xi t x| ≤ Rb t)
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    -- the inverse Jacobi ODE and the bounds it carries
    (hgSd : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    (hgbd : ∀ t x, |g t x| ≤ S0 t) (henbd : ∀ t x, |en t x| ≤ S0 t)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t)
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : 2 * c + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2 * c) + khat ^ 2 * c + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = ell * u) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, Y 0 (Phi 0 u) = a.1 u) → (∀ u, Y T (Phi T u) = b.1 u) →
        (∀ t u, |en t (Phi t u)| ≤ m t) →
        (∀ t, ∀ j ≤ 2,
          MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) →
        ∃ Γ : NormalPath a b, Γ.T = T ∧ Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
          IsVariableSpeedNormalPath P0 (costP1 ell khat (∫ t in (0 : ℝ)..T, m t)) khat
            (costG1 ell khat kappa2 (∫ t in (0 : ℝ)..T, m t))
            (khat * costG1 ell khat kappa2 (∫ t in (0 : ℝ)..T, m t)
              + kappa2 * costP1 ell khat (∫ t in (0 : ℝ)..T, m t) ^ 2) Γ := by
  -- the field of the marking is the tangential rate of the bundle
  have hgr : ∀ t x, GaugeRate.gaugeRate D.xi D.v t x = -D.xi t x := by
    intro t x
    rw [GaugeRate.gaugeRate, hv1 t x, div_one]
  -- the analytic hypotheses of the marking, from the bundle
  obtain ⟨-, hcont, hxd, hxcont, hxxd, hxxcont, -⟩ :=
    GaugeRate.gaugeRate_flow_hypotheses_of_bounds (L := D.rateLip) (K2 := D.rateBound2)
      D.rateLip_nonneg D.hxi D.hxi1 D.hv D.hv1 D.hvne D.hxic D.hxi1c D.hxi2c D.hvc D.hv1c
      D.hv2c D.hrate1 D.hrate2
  -- the marking itself
  obtain ⟨Phi, hPhi0, hPhid⟩ := exists_gaugeFlow_of_frameData D hell
  refine ⟨Phi, hPhi0, hPhid, ?_⟩
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
  have hRbd' : ∀ t x, |GaugeRate.gaugeRate D.xi D.v t x| ≤ Rb t := by
    intro t x
    rw [hgr t x, abs_neg]
    exact hRbd t x
  exact exists_variableSpeed_normalPath_of_jacobi_cost (Y := Y) (alpha := alpha) (k := k)
    (en := en) (enS := enS) (enSS := enSS) (g := g) (gS := gS)
    (h := GaugeRate.gaugeRate D.xi D.v) (hx := GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
    (hxx := GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2) (Phi := Phi)
    (alphaT := alphaT) (kT := kT) (kX := kX) (C := C) (C2 := C2) (Kx := Kx) (Rb := Rb)
    (S0 := S0) (D := Dd) (m := m) (ell := ell) (T := T) (P0 := P0) (khat := khat)
    (kappa2 := kappa2) (c := c) (d := d) (r := r) (kx := kx)
    hYC1 hY hYt' halpha hcont (fun u t => hPhid u t) hell hPhi0 hxd hxcont hxxd hxxcont
    hk hkappa2 hC hC2 hCc hC2c hCm hC2m halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc
    hkc hKxbd hRbd' hKxnn henS henSS halphaTS hmixed' hgSd hjacobi hgbd henbd hgSbd hS0m
    hDm hRbm hKxm hr hm0 hnumA hnumK hT hencont hstart hfinish hmc hmstop hmbd hmsup

end GaugeMarkedDataOfFrameBundle
