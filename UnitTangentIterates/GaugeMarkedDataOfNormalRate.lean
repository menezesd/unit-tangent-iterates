import Mathlib
import UnitTangentIterates.GaugeFlowVariableSpeedPath
import UnitTangentIterates.GaugeFrameTimeBounds
import UnitTangentIterates.GaugeFrameTangentialRate

/-!
# The gauge-marked data of a family, from its normal rate alone

`GaugeFlowVariableSpeedPath.GaugeMarkedData` asks, among its bounds, for a bound
`A` on the time derivative of the tangent angle of the slices and a bound `K_t`
on the time derivative of their curvature, together with the two comparisons

```
  A t + κ̂ · R_b t ≤ (1/P₀) · m t ,
  K_t t + K_x t · R_b t ≤ (1/P₀² + κ̂²) · m t .
```

These are not independent data: for a family carried in its own arclength the
normal-flow relations of `GaugeFrameTimeBounds` express both time derivatives
through the normal rate `η`, its first two arclength derivatives and the
tangential rate,

```
  ∂_tα = ∂_sη + k ξ ,        ∂_t k = ∂_s²η + k² η + ξ ∂_s k ,
```

so that the two bounds and the two comparisons follow from bounds `S₀, S₁, S₂`
on `η, ∂_sη, ∂_s²η` and the numerical conditions
`c₁ + 2κ̂ r ≤ 1/P₀` and `c₂ + κ̂² c₀ + 2 r k_x ≤ 1/P₀² + κ̂²`.  The identity
`∂_sξ = kη` these relations need is itself the other component of the same
equality of mixed partial derivatives (`hasDerivAt_xi_of_mixed`), so it is not
assumed either.

This file carries out that replacement: `gaugeMarkedData_of_normal_rate` builds
the whole packaged data out of the motion of the family, and
`exists_variableSpeed_normalPath_of_normal_rate` produces from it the normal
path with slices of variable speed — the path `Γ'` of the `C²` comparison —
without any hypothesis on the time derivatives of the frame data.

Main results: `gaugeMarkedData_of_normal_rate`,
`exists_variableSpeed_normalPath_of_normal_rate`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeMarkedDataOfNormalRate

open GaugeFlowVariableSpeedPath GaugeFrameTimeBounds GaugeFrameTangentialRate
  NormalPathC2IncrementVariableSpeed

variable {a b : Data} {Y : ℝ → ℝ → ℂ}
  {alpha k en enS enSS h hx hxx Phi alphaT kT kX : ℝ → ℝ → ℝ}
  {C C2 Kx Rb S0 S1 S2 m : ℝ → ℝ} {K K2 : NNReal} {ell T : ℝ}
  {P0 P1 khat G1 Cg c0 c1 c2 r kx : ℝ}

/-- **The arclength parametrization is preserved: `∂_sξ = kη`.**  Here the
tangential rate is `ξ = −h`, the field of the gauge flow taken with the opposite
sign, so the identity reads `−h_x = kη`; it is the component along the unit
tangent of the equality of the mixed partial derivatives, and hence is not an
extra hypothesis. -/
theorem hasDerivAt_xi_of_mixed
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x)
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => ((-h t x : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    (t x : ℝ) : HasDerivAt (fun s => -h t s) (k t x * en t x) x := by
  obtain ⟨W, hW1, hW2⟩ := hmixed t x
  have hrel := (tangentialRate_eq (alpha := alpha) (k := k) (xi := fun t s => -h t s)
    (xiS := fun t x => -hx t x) (eta := en) (etaS := enS) (alphaT := alphaT) t x
    (fun y => halpha t y) (fun y => henS t y) (fun y => (hxd t y).neg) (halphaT t x)
    hW1 hW2).1
  rw [← hrel]
  exact (hxd t x).neg

/-- **The tangent angle of a family carried in its own arclength turns at the
rate `∂_sη + kξ`.**  Here the tangential rate is `ξ = −h`, the field of the gauge
flow taken with the opposite sign. -/
theorem angleRate_rel
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (hxiS : ∀ t x, HasDerivAt (fun s => -h t s) (k t x * en t x) x)
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => ((-h t x : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    (t s : ℝ) : alphaT t s = enS t s + k t s * (-h t s) := by
  obtain ⟨W, hW1, hW2⟩ := hmixed t s
  exact angleRate_eq (alpha := alpha) (k := k) (xi := fun t s => -h t s) (eta := en)
    (etaS := enS) (alphaT := alphaT) t s (fun x => halpha t x) (fun x => henS t x)
    (fun x => hxiS t x) (halphaT t s) hW1 hW2

/-- **The curvature of such a family moves at the rate `∂_s²η + k²η + ξ ∂_s k`.** -/
theorem curvRate_rel
    (hrel : ∀ t x, alphaT t x = enS t x + k t x * (-h t x))
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (hxiS : ∀ t x, HasDerivAt (fun s => -h t s) (k t x * en t x) x)
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (t s : ℝ) : kT t s = enSS t s + k t s ^ 2 * en t s + (-h t s) * kX t s :=
  curvRate_eq (k := k) (xi := fun t s => -h t s) (eta := en) (etaS := enS) (etaSS := enSS)
    (kX := kX) (alphaT := alphaT) (kT := kT) t s (fun x => hrel t x) (fun x => henSS t x)
    (fun x => hkX t x) (fun x => hxiS t x) (halphaTS t s)

/-- **The gauge-marked data of a family, built from its normal rate.**

The bounds on the two time derivatives of the frame data, and the two
comparisons with the cost density that `GaugeMarkedData` asks for, are produced
from bounds `S₀, S₁, S₂` on the normal rate and on its first two arclength
derivatives, from the bound `R_b` on the field, and from the two numerical
conditions — through the normal-flow relations of `GaugeFrameTimeBounds`. -/
def gaugeMarkedData_of_normal_rate
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
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (hxcont : Continuous (uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x) (hxxcont : Continuous (uncurry hxx))
    (hxxK : ∀ s x, |hxx s x| ≤ (K2 : ℝ))
    (hP1 : ∀ t u, FlowDerivative.flowDeriv hx Phi ell t u ≤ P1)
    (hG1 : ∀ t u, |GaugeFlowTimeDerivative.flowDeriv2 hx hxx Phi ell t u| ≤ G1)
    (hk : ∀ t x, |k t x| ≤ khat)
    (hC : ∀ t x, |hx t x| ≤ C t) (hC2 : ∀ t x, |hxx t x| ≤ C2 t)
    (hCnn : ∀ t, 0 ≤ C t) (hC2nn : ∀ t, 0 ≤ C2 t)
    (hcost : ∀ t, C t * P1 ≤ khat * P1 * m t)
    (hcost2 : ∀ t, C t * G1 + C2 t * P1 ^ 2 ≤ Cg * m t)
    -- the frame data of the slices
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxbd : ∀ t x, |kX t x| ≤ Kx t) (hRbd : ∀ t x, |h t x| ≤ Rb t)
    (hKxnn : ∀ t, 0 ≤ Kx t)
    -- the normal rate, its two arclength derivatives, and the relations
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => ((-h t x : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    -- the bounds on the normal rate and the numerical conditions
    (hS0bd : ∀ t x, |en t x| ≤ S0 t) (hS1bd : ∀ t x, |enS t x| ≤ S1 t)
    (hS2bd : ∀ t x, |enSS t x| ≤ S2 t)
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
    GaugeMarkedData a b P0 P1 khat G1 Cg T m where
  Y := Y
  alpha := alpha
  k := k
  en := en
  h := h
  hx := hx
  hxx := hxx
  Phi := Phi
  alphaT := alphaT
  kT := kT
  kX := kX
  C := C
  C2 := C2
  A := angleRateBound S1 Rb khat
  Kt := curvRateBound S0 S2 Rb Kx khat
  Kx := Kx
  Rb := Rb
  K := K
  K2 := K2
  ell := ell
  hYC1 := hYC1
  hY := hY
  hYt := hYt
  halpha := halpha
  hlip := hlip
  hcont := hcont
  hPhid := hPhid
  hell := hell
  hPhi0 := hPhi0
  hxd := hxd
  hxcont := hxcont
  hxxd := hxxd
  hxxcont := hxxcont
  hxxK := hxxK
  hP1 := hP1
  hG1 := hG1
  hk := hk
  hC := hC
  hC2 := hC2
  hCnn := hCnn
  hC2nn := hC2nn
  hcost := hcost
  hcost2 := hcost2
  halphaC1 := halphaC1
  hkC1 := hkC1
  halphaT := halphaT
  hkT := hkT
  hkX := hkX
  halphaTc := halphaTc
  hkTc := hkTc
  hkXc := hkXc
  hkc := hkc
  hAbd := by
    intro t x
    refine abs_angleRate_le (alphaT := alphaT) (etaS := enS) (k := k)
      (xi := fun t s => -h t s) t x
      (angleRate_rel halpha henS (hasDerivAt_xi_of_mixed halpha henS hxd halphaT hmixed)
        halphaT hmixed t x) (hS1bd t x) (hk t x) ?_
    simpa using hRbd t x
  hKtbd := by
    intro t x
    refine abs_curvRate_le (kT := kT) (etaSS := enSS) (eta := en) (k := k)
      (xi := fun t s => -h t s) (kX := kX) t x
      (curvRate_rel
        (angleRate_rel halpha henS (hasDerivAt_xi_of_mixed halpha henS hxd halphaT hmixed)
          halphaT hmixed)
        henSS hkX (hasDerivAt_xi_of_mixed halpha henS hxd halphaT hmixed)
        halphaTS t x) (hS2bd t x) (hS0bd t x) (hk t x) ?_ (hKxbd t x)
    simpa using hRbd t x
  hKxbd := hKxbd
  hRbd := hRbd
  hKxnn := hKxnn
  hcostA := fun t =>
    angleRate_le_cost hS1m hRbm hm0 (le_trans (abs_nonneg _) (hk 0 0)) hnumA t
  hcostK := fun t =>
    curvRate_le_cost hS0m hS2m hRbm hKxm hKxnn hm0 hr hnumK t
  hT := hT
  hencont := hencont
  hstart := hstart
  hfinish := hfinish
  hmc := hmc
  hm0 := hm0
  hmstop := hmstop
  hmbd := hmbd
  hmsup := hmsup

/-- **The normal path with slices of variable speed produced by a family whose
motion is given by its normal rate.**  The two hypotheses of `GaugeMarkedData`
about the time derivatives of the frame data are replaced by the normal-flow
relations and by bounds on the normal rate and on its first two arclength
derivatives. -/
theorem exists_variableSpeed_normalPath_of_normal_rate_with_eta_X
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      (((-h t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hlip : ∀ t, LipschitzWith K (h t)) (hcont : Continuous (uncurry h))
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (hxcont : Continuous (uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x) (hxxcont : Continuous (uncurry hxx))
    (hxxK : ∀ s x, |hxx s x| ≤ (K2 : ℝ))
    (hP1 : ∀ t u, FlowDerivative.flowDeriv hx Phi ell t u ≤ P1)
    (hG1 : ∀ t u, |GaugeFlowTimeDerivative.flowDeriv2 hx hxx Phi ell t u| ≤ G1)
    (hk : ∀ t x, |k t x| ≤ khat)
    (hC : ∀ t x, |hx t x| ≤ C t) (hC2 : ∀ t x, |hxx t x| ≤ C2 t)
    (hCnn : ∀ t, 0 ≤ C t) (hC2nn : ∀ t, 0 ≤ C2 t)
    (hcost : ∀ t, C t * P1 ≤ khat * P1 * m t)
    (hcost2 : ∀ t, C t * G1 + C2 t * P1 ^ 2 ≤ Cg * m t)
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxbd : ∀ t x, |kX t x| ≤ Kx t) (hRbd : ∀ t x, |h t x| ≤ Rb t)
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => ((-h t x : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    (hS0bd : ∀ t x, |en t x| ≤ S0 t) (hS1bd : ∀ t x, |enS t x| ≤ S1 t)
    (hS2bd : ∀ t x, |enSS t x| ≤ S2 t)
    (hS0m : ∀ t, S0 t ≤ c0 * m t) (hS1m : ∀ t, S1 t ≤ c1 * m t) (hS2m : ∀ t, S2 t ≤ c2 * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : c1 + 2 * khat * r ≤ 1 / P0)
    (hnumK : c2 + khat ^ 2 * c0 + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hstart : ∀ u, Y 0 (Phi 0 u) = a.1 u) (hfinish : ∀ u, Y T (Phi T u) = b.1 u)
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0)
    (hmbd : ∀ t u, |en t (Phi t u)| ≤ m t)
    (hmsup : ∀ t, ∀ j ≤ 2,
      MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) :
    ∃ Γ : NormalPath a b, Γ.T = T ∧
      (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
      (∀ t u, Γ.eta t u = en t (Phi t u)) ∧
      Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ :=
  exists_variableSpeed_normalPath_of_data_with_eta_X
    (gaugeMarkedData_of_normal_rate hYC1 hY hYt halpha hlip hcont hPhid hell hPhi0 hxd
      hxcont hxxd hxxcont hxxK hP1 hG1 hk hC hC2 hCnn hC2nn hcost hcost2 halphaC1 hkC1
      halphaT hkT hkX halphaTc hkTc hkXc hkc hKxbd hRbd hKxnn henS henSS halphaTS
      hmixed hS0bd hS1bd hS2bd hS0m hS1m hS2m hRbm hKxm hr hm0 hnumA hnumK hT hencont
      hstart hfinish hmc hmstop hmbd hmsup)

/-- **The normal path with slices of variable speed produced by a family whose
motion is given by its normal rate.**  The two hypotheses of `GaugeMarkedData`
about the time derivatives of the frame data are replaced by the normal-flow
relations and by bounds on the normal rate and on its first two arclength
derivatives. -/
theorem exists_variableSpeed_normalPath_of_normal_rate
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      (((-h t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hlip : ∀ t, LipschitzWith K (h t)) (hcont : Continuous (uncurry h))
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (hxcont : Continuous (uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x) (hxxcont : Continuous (uncurry hxx))
    (hxxK : ∀ s x, |hxx s x| ≤ (K2 : ℝ))
    (hP1 : ∀ t u, FlowDerivative.flowDeriv hx Phi ell t u ≤ P1)
    (hG1 : ∀ t u, |GaugeFlowTimeDerivative.flowDeriv2 hx hxx Phi ell t u| ≤ G1)
    (hk : ∀ t x, |k t x| ≤ khat)
    (hC : ∀ t x, |hx t x| ≤ C t) (hC2 : ∀ t x, |hxx t x| ≤ C2 t)
    (hCnn : ∀ t, 0 ≤ C t) (hC2nn : ∀ t, 0 ≤ C2 t)
    (hcost : ∀ t, C t * P1 ≤ khat * P1 * m t)
    (hcost2 : ∀ t, C t * G1 + C2 t * P1 ^ 2 ≤ Cg * m t)
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxbd : ∀ t x, |kX t x| ≤ Kx t) (hRbd : ∀ t x, |h t x| ≤ Rb t)
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => ((-h t x : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    (hS0bd : ∀ t x, |en t x| ≤ S0 t) (hS1bd : ∀ t x, |enS t x| ≤ S1 t)
    (hS2bd : ∀ t x, |enSS t x| ≤ S2 t)
    (hS0m : ∀ t, S0 t ≤ c0 * m t) (hS1m : ∀ t, S1 t ≤ c1 * m t) (hS2m : ∀ t, S2 t ≤ c2 * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : c1 + 2 * khat * r ≤ 1 / P0)
    (hnumK : c2 + khat ^ 2 * c0 + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hstart : ∀ u, Y 0 (Phi 0 u) = a.1 u) (hfinish : ∀ u, Y T (Phi T u) = b.1 u)
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0)
    (hmbd : ∀ t u, |en t (Phi t u)| ≤ m t)
    (hmsup : ∀ t, ∀ j ≤ 2,
      MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) :
    ∃ Γ : NormalPath a b, Γ.T = T ∧ Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ :=
  exists_variableSpeed_normalPath_of_data
    (gaugeMarkedData_of_normal_rate hYC1 hY hYt halpha hlip hcont hPhid hell hPhi0 hxd
      hxcont hxxd hxxcont hxxK hP1 hG1 hk hC hC2 hCnn hC2nn hcost hcost2 halphaC1 hkC1
      halphaT hkT hkX halphaTc hkTc hkXc hkc hKxbd hRbd hKxnn henS henSS halphaTS
      hmixed hS0bd hS1bd hS2bd hS0m hS1m hS2m hRbm hKxm hr hm0 hnumA hnumK hT hencont
      hstart hfinish hmc hmstop hmbd hmsup)

end GaugeMarkedDataOfNormalRate
