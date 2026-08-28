import Mathlib
import UnitTangentIterates.GaugeFlowNormalPath
import UnitTangentIterates.GaugeFlowVariableSpeedPartials

/-!
# The variable-speed normal path of a family of curves read in a gauge marking

`GaugeFlowNormalPath.exists_normalPath_of_gauge_marking` produces the normal
path of a family read in a gauge marking, and
`GaugeFlowVariableSpeedPartials.isVariableSpeedFamily_of_gauge_flow_partials`
shows that such a family is a family of slices of variable speed.  Both speak
about the same moving curve `X(t,u) = Y(t, Φ(t,u))`, so they combine into a
single statement: **the path is a normal path with slices of variable speed**,
which is exactly the hypothesis `Γ'` of the `C²` comparison of the two marked
selected inverses in `SelInvMarkingDefectClosedC2.lean`.

The tangential rate of the family and the field of the marking are the same
datum up to sign: the marking is the flow of `h`, and the slices move with the
velocity

```
  ∂_t Y = (−h) · e^{iα} + η · i e^{iα} ,
```

so the tangential component is cancelled in the marked parameter.

The whole hypothesis block is also packaged as a structure `GaugeMarkedData`, so
that the production of such a path can be assumed in one word downstream.

Main results: `exists_variableSpeed_normalPath_of_gauge_marking`,
`exists_variableSpeed_normalPath_of_data`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeFlowVariableSpeedPath

open FlowDerivative GaugeFlowTimeDerivative GaugeFlowNormalPath
  GaugeFlowVariableSpeedPartials NormalPathC2IncrementVariableSpeed

/-- **The normal path of a family read in a gauge marking has slices of variable
speed.**

The slices `Y t` are parametrized by their own arclength, with tangent angle `α`
and curvature `k`, and move with tangential rate `−h` and normal rate `η`; the
marking `Φ` is the flow of the field `h`, started at the affine marking of
period `ℓ`.  Under the bounds of
`GaugeFlowVariableSpeedPartials.isVariableSpeedFamily_of_gauge_flow_partials`
for the field, for the flow derivatives and for the frame data of the slices,
and for a cost density `m` dominating the normal rate and the sup norms of its
first two derivatives, the family is a normal path from `a` to `b` whose slices
have variable speed — with cost `∫₀^T m`. -/
theorem exists_variableSpeed_normalPath_of_gauge_marking_with_eta
    {a b : Data} {Y : ℝ → ℝ → ℂ} {alpha k en h hx hxx Phi : ℝ → ℝ → ℝ}
    {alphaT kT kX : ℝ → ℝ → ℝ} {C C2 A Kt Kx Rb m : ℝ → ℝ} {K K2 : NNReal} {ell T : ℝ}
    {P0 P1 khat G1 Cg : ℝ}
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
    -- the uniform bounds on the two flow derivatives
    (hP1 : ∀ t u, flowDeriv hx Phi ell t u ≤ P1)
    (hG1 : ∀ t u, |flowDeriv2 hx hxx Phi ell t u| ≤ G1)
    (hk : ∀ t x, |k t x| ≤ khat)
    -- the pointwise bounds on the two space derivatives of the field
    (hC : ∀ t x, |hx t x| ≤ C t) (hC2 : ∀ t x, |hxx t x| ≤ C2 t)
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
    (hAbd : ∀ t x, |alphaT t x| ≤ A t) (hKtbd : ∀ t x, |kT t x| ≤ Kt t)
    (hKxbd : ∀ t x, |kX t x| ≤ Kx t) (hRbd : ∀ t x, |h t x| ≤ Rb t)
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (hcostA : ∀ t, A t + khat * Rb t ≤ 1 / P0 * m t)
    (hcostK : ∀ t, Kt t + Kx t * Rb t ≤ (1 / P0 ^ 2 + khat ^ 2) * m t)
    -- the path data
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hstart : ∀ u, Y 0 (Phi 0 u) = a.1 u) (hfinish : ∀ u, Y T (Phi T u) = b.1 u)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0)
    (hmbd : ∀ t u, |en t (Phi t u)| ≤ m t)
    (hmsup : ∀ t, ∀ j ≤ 2,
      MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) :
    ∃ Γ : NormalPath a b, Γ.T = T ∧ (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
      (∀ t u, Γ.eta t u = en t (Phi t u)) ∧
      Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ := by
  -- the family read in the marking is a variable-speed family
  have hfam : IsVariableSpeedFamily P0 P1 khat G1 Cg (fun t u => Y t (Phi t u)) m :=
    isVariableSpeedFamily_of_gauge_flow_partials hY halpha hlip hcont hPhid hell hPhi0
      hxd hxcont hxxd hxxcont hxxK hP1 hG1 hk hC hC2 hCnn hC2nn hcost hcost2
      halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc hkc hAbd hKtbd hKxbd hRbd hKxnn
      hcostA hcostK
  -- and it is a normal path
  obtain ⟨Γ, hΓT, hΓX, hΓeta, -, hΓm, hΓcost⟩ :=
    exists_normalPath_of_gauge_marking (a := a) (b := b) (xi := fun t s => -h t s)
      (en := en) (alpha := alpha) (m := m) hT hYC1 hY hYt
      (fun u t => by simpa using hPhid u t)
      (fun t => continuous_flow_initial hlip hPhid hPhi0 t)
      hencont halphaC1.continuous hstart hfinish hmc hm0 hmstop hmbd hmsup
  refine ⟨Γ, hΓT, hΓX, hΓeta, hΓm, by rw [hΓcost], ?_⟩
  have hX : Γ.X = fun t u => Y t (Phi t u) := funext fun t => funext fun u => hΓX t u
  show IsVariableSpeedFamily P0 P1 khat G1 Cg Γ.X Γ.m
  rw [hX, hΓm]
  exact hfam

/-- Backwards-compatible projection of
`exists_variableSpeed_normalPath_of_gauge_marking_with_eta`. -/
theorem exists_variableSpeed_normalPath_of_gauge_marking
    {a b : Data} {Y : ℝ → ℝ → ℂ} {alpha k en h hx hxx Phi : ℝ → ℝ → ℝ}
    {alphaT kT kX : ℝ → ℝ → ℝ} {C C2 A Kt Kx Rb m : ℝ → ℝ} {K K2 : NNReal} {ell T : ℝ}
    {P0 P1 khat G1 Cg : ℝ}
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
    (hP1 : ∀ t u, flowDeriv hx Phi ell t u ≤ P1)
    (hG1 : ∀ t u, |flowDeriv2 hx hxx Phi ell t u| ≤ G1)
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
    (hAbd : ∀ t x, |alphaT t x| ≤ A t) (hKtbd : ∀ t x, |kT t x| ≤ Kt t)
    (hKxbd : ∀ t x, |kX t x| ≤ Kx t) (hRbd : ∀ t x, |h t x| ≤ Rb t)
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (hcostA : ∀ t, A t + khat * Rb t ≤ 1 / P0 * m t)
    (hcostK : ∀ t, Kt t + Kx t * Rb t ≤ (1 / P0 ^ 2 + khat ^ 2) * m t)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hstart : ∀ u, Y 0 (Phi 0 u) = a.1 u) (hfinish : ∀ u, Y T (Phi T u) = b.1 u)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0)
    (hmbd : ∀ t u, |en t (Phi t u)| ≤ m t)
    (hmsup : ∀ t, ∀ j ≤ 2,
      MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) :
    ∃ Γ : NormalPath a b, Γ.T = T ∧ (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
      Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ := by
  obtain ⟨Γ, hΓT, hΓX, -, hΓm, hΓcost, hΓvar⟩ :=
    exists_variableSpeed_normalPath_of_gauge_marking_with_eta hYC1 hY hYt halpha
      hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxK hP1 hG1 hk hC hC2
      hCnn hC2nn hcost hcost2 halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc hkc
      hAbd hKtbd hKxbd hRbd hKxnn hcostA hcostK hT hencont hstart hfinish hmc hm0
      hmstop hmbd hmsup
  exact ⟨Γ, hΓT, hΓX, hΓm, hΓcost, hΓvar⟩

/-- **The data of a family of curves read in a gauge marking**, joining the two
marked data `a` and `b` over the time `T` with cost density `m` and with the
bounds that make its slices of variable speed: the hypothesis block of
`exists_variableSpeed_normalPath_of_gauge_marking`, packaged. -/
structure GaugeMarkedData (a b : Data) (P0 P1 khat G1 Cg T : ℝ) (m : ℝ → ℝ) where
  /-- the moving curve, in its own arclength. -/
  Y : ℝ → ℝ → ℂ
  /-- the tangent angle of the slices. -/
  alpha : ℝ → ℝ → ℝ
  /-- the curvature of the slices. -/
  k : ℝ → ℝ → ℝ
  /-- the normal rate of the motion. -/
  en : ℝ → ℝ → ℝ
  /-- the field of the gauge flow; the tangential rate is its negative. -/
  h : ℝ → ℝ → ℝ
  /-- the space derivative of the field. -/
  hx : ℝ → ℝ → ℝ
  /-- the second space derivative of the field. -/
  hxx : ℝ → ℝ → ℝ
  /-- the marking. -/
  Phi : ℝ → ℝ → ℝ
  /-- the time derivative of the tangent angle. -/
  alphaT : ℝ → ℝ → ℝ
  /-- the time derivative of the curvature. -/
  kT : ℝ → ℝ → ℝ
  /-- the arclength derivative of the curvature. -/
  kX : ℝ → ℝ → ℝ
  /-- a bound for the space derivative of the field. -/
  C : ℝ → ℝ
  /-- a bound for the second space derivative of the field. -/
  C2 : ℝ → ℝ
  /-- a bound for the time derivative of the tangent angle. -/
  A : ℝ → ℝ
  /-- a bound for the time derivative of the curvature. -/
  Kt : ℝ → ℝ
  /-- a bound for the arclength derivative of the curvature. -/
  Kx : ℝ → ℝ
  /-- a bound for the field itself. -/
  Rb : ℝ → ℝ
  /-- the Lipschitz constant of the field. -/
  K : NNReal
  /-- a bound for the second space derivative of the field. -/
  K2 : NNReal
  /-- the period of the affine marking the flow starts at. -/
  ell : ℝ
  hYC1 : ContDiff ℝ 1 (uncurry Y)
  hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s
  hYt : ∀ t s, HasDerivAt (fun r => Y r s)
    (((-h t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
      + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t
  halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s
  hlip : ∀ t, LipschitzWith K (h t)
  hcont : Continuous (uncurry h)
  hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t
  hell : 0 < ell
  hPhi0 : ∀ u, Phi 0 u = ell * u
  hxd : ∀ s x, HasDerivAt (h s) (hx s x) x
  hxcont : Continuous (uncurry hx)
  hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x
  hxxcont : Continuous (uncurry hxx)
  hxxK : ∀ s x, |hxx s x| ≤ (K2 : ℝ)
  hP1 : ∀ t u, FlowDerivative.flowDeriv hx Phi ell t u ≤ P1
  hG1 : ∀ t u, |GaugeFlowTimeDerivative.flowDeriv2 hx hxx Phi ell t u| ≤ G1
  hk : ∀ t x, |k t x| ≤ khat
  hC : ∀ t x, |hx t x| ≤ C t
  hC2 : ∀ t x, |hxx t x| ≤ C2 t
  hCnn : ∀ t, 0 ≤ C t
  hC2nn : ∀ t, 0 ≤ C2 t
  hcost : ∀ t, C t * P1 ≤ khat * P1 * m t
  hcost2 : ∀ t, C t * G1 + C2 t * P1 ^ 2 ≤ Cg * m t
  halphaC1 : ContDiff ℝ 1 (uncurry alpha)
  hkC1 : ContDiff ℝ 1 (uncurry k)
  halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t
  hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t
  hkX : ∀ t x, HasDerivAt (k t) (kX t x) x
  halphaTc : Continuous (uncurry alphaT)
  hkTc : Continuous (uncurry kT)
  hkXc : Continuous (uncurry kX)
  hkc : Continuous (uncurry k)
  hAbd : ∀ t x, |alphaT t x| ≤ A t
  hKtbd : ∀ t x, |kT t x| ≤ Kt t
  hKxbd : ∀ t x, |kX t x| ≤ Kx t
  hRbd : ∀ t x, |h t x| ≤ Rb t
  hKxnn : ∀ t, 0 ≤ Kx t
  hcostA : ∀ t, A t + khat * Rb t ≤ 1 / P0 * m t
  hcostK : ∀ t, Kt t + Kx t * Rb t ≤ (1 / P0 ^ 2 + khat ^ 2) * m t
  hT : 0 < T
  hencont : Continuous (uncurry en)
  hstart : ∀ u, Y 0 (Phi 0 u) = a.1 u
  hfinish : ∀ u, Y T (Phi T u) = b.1 u
  hmc : Continuous m
  hm0 : ∀ t, 0 ≤ m t
  hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0
  hmbd : ∀ t u, |en t (Phi t u)| ≤ m t
  hmsup : ∀ t, ∀ j ≤ 2,
    MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t

/-- Strengthened packaged-data constructor retaining the two defining fields
of the gauge-marked path. -/
theorem exists_variableSpeed_normalPath_of_data_with_eta_X
    {a b : Data} {P0 P1 khat G1 Cg T : ℝ}
    {m : ℝ → ℝ} (D : GaugeMarkedData a b P0 P1 khat G1 Cg T m) :
    ∃ Γ : NormalPath a b, Γ.T = T ∧
      (∀ t u, Γ.X t u = D.Y t (D.Phi t u)) ∧
      (∀ t u, Γ.eta t u = D.en t (D.Phi t u)) ∧
      Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ := by
  obtain ⟨Γ, hΓT, hΓX, hΓeta, hΓm, hΓcost, hΓvar⟩ :=
    exists_variableSpeed_normalPath_of_gauge_marking_with_eta (a := a) (b := b)
      (Y := D.Y) (alpha := D.alpha) (k := D.k) (en := D.en) (h := D.h) (hx := D.hx)
      (hxx := D.hxx) (Phi := D.Phi) (alphaT := D.alphaT) (kT := D.kT) (kX := D.kX)
      (C := D.C) (C2 := D.C2) (A := D.A) (Kt := D.Kt) (Kx := D.Kx) (Rb := D.Rb)
      (K := D.K) (K2 := D.K2) (ell := D.ell) (m := m) (P0 := P0) (P1 := P1)
      (khat := khat) (G1 := G1) (Cg := Cg)
      D.hYC1 D.hY D.hYt D.halpha D.hlip D.hcont D.hPhid D.hell D.hPhi0 D.hxd D.hxcont
      D.hxxd D.hxxcont D.hxxK D.hP1 D.hG1 D.hk D.hC D.hC2 D.hCnn D.hC2nn D.hcost
      D.hcost2 D.halphaC1 D.hkC1 D.halphaT D.hkT D.hkX D.halphaTc D.hkTc D.hkXc D.hkc
      D.hAbd D.hKtbd D.hKxbd D.hRbd D.hKxnn D.hcostA D.hcostK D.hT D.hencont D.hstart
      D.hfinish D.hmc D.hm0 D.hmstop D.hmbd D.hmsup
  exact ⟨Γ, hΓT, hΓX, hΓeta, hΓm, hΓcost, hΓvar⟩

/-- Backwards-compatible projection of the strengthened packaged result. -/
theorem exists_variableSpeed_normalPath_of_data
    {a b : Data} {P0 P1 khat G1 Cg T : ℝ}
    {m : ℝ → ℝ} (D : GaugeMarkedData a b P0 P1 khat G1 Cg T m) :
    ∃ Γ : NormalPath a b, Γ.T = T ∧ Γ.m = m ∧
      cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ := by
  obtain ⟨Γ, hT, -, -, hm, hcost, hvar⟩ :=
    exists_variableSpeed_normalPath_of_data_with_eta_X D
  exact ⟨Γ, hT, hm, hcost, hvar⟩

end GaugeFlowVariableSpeedPath
