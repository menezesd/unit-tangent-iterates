import Mathlib
import UnitTangentIterates.SelInvFrontStripFundamentalDriftC2
import UnitTangentIterates.SelInvFrontVelocityC2
import UnitTangentIterates.SelInvFrontRegularityC2
import UnitTangentIterates.RearOwnHigherRegularity
import UnitTangentIterates.FrontFromPath
import UnitTangentIterates.RearBaseDrift

/-!
# The `C²` estimate with the tangential drift at the marked point discharged

`SelInvFrontStripFundamentalDriftC2.dist_selInv_le_of_front_strip_fundamental_drift_C2`
asks of the family of selected rears only one thing: that its tangential drift
`ξ(t,x) = ⟨∂_t Y(t,x), e^{iΨ(t,x)}⟩` vanish at the marked point `x = 0`.  That
condition is not an extra assumption on the rears: `RearBaseDrift` identifies
`ξ(t,0)` with the base drift `Re(Ḟ(t,0) · conj e^{i(Θ−δ)(t,0)})` of the front,
and the front of a normal path does not move at its marked point as soon as the
path does not — the marked point of the front being the marked point of the
slice, and the path moving in normal gauge with speed `η`.  So the hypothesis
`∀ t, Γ.eta t 0 = 0`, which the statement already carries, discharges it.

Main result: `dist_selInv_le_of_front_base_drift_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvFrontBaseDriftC2

open SelInvFrontStripFundamentalC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed GaugeFlowVariableSpeedPath GaugeFlowDerivCost
  GaugeMarkedDataOfRearFamily GaugeFlowUniqueness FlowDerivative
  GaugeFlowTimeDerivative GaugeFlowSupJacobi SelInvFrontCostC2 RearJacobiSourceCost
  SelInvFrontSourceC2 RearOwnTangential SelInvFrontStripC2 SelInvFrontVelocityC2
  SelInvFrontRegularityC2

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, with the
tangential drift of the selected rears at the marked point discharged.**  The
hypotheses are those of
`SelInvFrontStripFundamentalDriftC2.dist_selInv_le_of_front_strip_fundamental_drift_C2`
with the vanishing of the drift at the marked point removed: it follows from the
rest of the marked point of the path, `∀ t, Γ.eta t 0 = 0`. -/
theorem dist_selInv_le_of_front_base_drift_C2 {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq Md MP CK CP : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ' dl) (Ico 0 (perim p)))
    (hcq : 0 < cq) (hkminq : 0 < kminq) (hq : IsTubeMember cq kminq dltq q)
    (hubq : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kh * ‖q.2.1 u‖ ^ 3)
    (hinjRq : ∀ Θ' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl (perim q) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev q) Θ' dl) (Ico 0 (perim q)))
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1) (hVper : ∀ t, Periodic (V t) 1)
    (hAper : ∀ t, Periodic (A t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * (V t u / (P t : ℂ)))
    (hdelta : ∀ t s, δ t s = dn t (s / P t))
    (hKeq : ∀ t s, curvOfPath V A P t s = Kn t (s / P t))
    (hsol : ∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ)
    (hstrip : ∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh))
    (hdnper : ∀ t, Function.Periodic (dn t) 1) (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hKnbd : ∀ t σ, |Kn t σ| ≤ kh) (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md)
    (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)))
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath V A P)))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hmark : ∀ t, Γ.eta t 0 = 0)
    -- the tangent-angle lift of the terminal marked selected inverse
    {kb kL : ℝ} {Θb kb' : ℝ → ℝ}
    (hevd : ∀ s, HasDerivAt (ev (SelectedInverseMap.selInv kh q))
      (Complex.exp (Complex.I * (Θb s : ℂ))) s)
    (hΘb : ∀ s, HasDerivAt Θb (kb' s) s) (hkbd : ∀ s, |kb' s| ≤ kb)
    (hklip : ∀ s t, |kb' s - kb' t| ≤ kL * |s - t|)
    -- the motion of the family of selected rears, in its own arclength
    {Ydot : ℝ → ℝ → ℂ} {etaF alphaT kT : ℝ → ℝ → ℝ}
    {Pv0 khat : ℝ}
    (hYt : ∀ t x, HasDerivAt
      (fun r => rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf r x) (Ydot t x) t)
    (hδC : ContDiff ℝ 1 (uncurry δ)) (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hYdotC : ContDiff ℝ (3 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (3 : ℕ)
      (uncurry (rearOwnAngle (angleOfPath V A P) δ sf)))
    (hkC1 : ContDiff ℝ 1 (uncurry fun t x => Real.tan (δ t (sf t x))))
    (hper : ∀ t, Function.Periodic
      (frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t)
      (rearArclength (δ t) (P t)))
    (hjac : ∀ t x, HasDerivAt
      (fun x' => frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x')
      (etaF t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x) x)
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hkappa1 : rearKappa1 kh ≤ khat)
    (halphaT : ∀ t x, HasDerivAt
      (fun r => rearOwnAngle (angleOfPath V A P) δ sf r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => Real.tan (δ r (sf r x))) (kT t x) t)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I *
          (rearOwnAngle (angleOfPath V A P) δ sf r s : ℂ))) W t ∧
      HasDerivAt (fun x =>
          (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x : ℂ)
            * Complex.exp (Complex.I *
              (rearOwnAngle (angleOfPath V A P) δ sf t x : ℂ))
          + (frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x : ℂ)
            * (Complex.I * Complex.exp (Complex.I *
              (rearOwnAngle (angleOfPath V A P) δ sf t x : ℂ)))) W s)
    -- the parameter derivative of the normal speed of the path
    {etaU : ℝ → ℝ → ℝ} (hetaU : ∀ t u, HasDerivAt (Γ.eta t) (etaU t u) u)
    (hetaUbd : ∀ t u, |etaU t u| ≤ Γ.m t)
    (hnumA : 2 + 2 * khat * (P1 * (kh / (1 - kh ^ 2))) ≤ 1 / Pv0)
    (hnumK : (jacobiSourceConst kh P0 + 2) + khat ^ 2 + 2 * (P1 * (kh / (1 - kh ^ 2))) * stripCurvConst kh
      ≤ 1 / Pv0 ^ 2 + khat ^ 2)
    -- the total cost of the family of selected rears, with the density chosen
    -- proportional to that of the fronts, is at most one
    (hsmall : RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
      (rearArclength (δ 0) (P 0)) (jacobiSourceConst kh P0) * cost Γ ≤ 1) :
    perim (SelectedInverseMap.selInv kh p) = rearArclength (δ 0) (P 0) ∧
      perim (SelectedInverseMap.selInv kh q) = rearArclength (δ Γ.T) (P Γ.T) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
        (∀ t, Phi t 0 = 0) ∧
        (∀ u t, HasDerivAt (fun r => Phi r u)
          (-frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t (Phi t u)) t) ∧
        dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
            ≤ markingC2Bound (2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ)
                (flowDefectC1Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ))
                (flowDefectC2Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ)
                  (gaugeGrowth2 kh * cost Γ))
                (rearArclength (δ Γ.T) (P Γ.T)) kb kL
              + c2ConstVar Pv0
                  (costP1 (rearArclength (δ 0) (P 0)) khat
                    (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                      (rearArclength (δ 0) (P 0))
                    (jacobiSourceConst kh P0) * cost Γ)) khat
                  (costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
                    (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                    (rearArclength (δ 0) (P 0))
                    (jacobiSourceConst kh P0) * cost Γ))
                  (khat * costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
                      (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                    (rearArclength (δ 0) (P 0))
                    (jacobiSourceConst kh P0) * cost Γ)
                    + rearKappa2 kh * costP1 (rearArclength (δ 0) (P 0)) khat
                      (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                    (rearArclength (δ 0) (P 0))
                    (jacobiSourceConst kh P0) * cost Γ) ^ 2)
                * (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                    (rearArclength (δ 0) (P 0))
                    (jacobiSourceConst kh P0) * cost Γ) := by
  classical
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hslice : ∀ t, Function.Periodic (δ t) (P t) ∧
      (∀ s, HasDerivAt (δ t) (curvOfPath V A P t s - Real.sin (δ t s)) s) ∧
      (∀ s, δ t s ∈ Icc (0 : ℝ) (Real.arcsin kh)) := fun t =>
    SelectedInverseRearOwnTerminal.delta_slice_of_normalized (t := t) (hPpos t) hdelta
      hKeq hsol hstrip hdnper
  have hsteer : ∀ t s, HasDerivAt (δ t) (curvOfPath V A P t s - Real.sin (δ t s)) s :=
    fun t => (hslice t).2.1
  have hstrip0 : ∀ t s, 0 ≤ δ t s := fun t s => ((hslice t).2.2 s).1
  have hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh := fun t s => ((hslice t).2.2 s).2
  have hδcont : Continuous (uncurry δ) := hδC.continuous
  have hle14 : ((1 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (1 : ℕ) ≤ 4)
  have hFc1 : ContDiff ℝ (1 : ℕ) (uncurry (frontOfPath Γ.X P)) := by
    simpa using hFc4.of_le hle14
  have hΘc1 : ContDiff ℝ (1 : ℕ) (uncurry (angleOfPath V A P)) := by
    simpa using hΘc4.of_le hle14
  have hVcont : ∀ t, Continuous (V t) := fun t =>
    Differentiable.continuous fun u => (hA t u).differentiableAt
  -- the front is unit speed with tangent angle `angleOfPath`
  have hFtangent : ∀ t s, HasDerivAt (frontOfPath Γ.X P t)
      (Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ))) s := by
    intro t s
    have h := hasDerivAt_frontOfPath_tangent (hV t) (hPpos t) s
    rwa [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s]
  have hΘd : ∀ t s, HasDerivAt (angleOfPath V A P t) (curvOfPath V A P t s) s :=
    fun t s => hasDerivAt_angleOfPath (continuous_curvOfPath (hVcont t) (hAcont t)) s
  -- the velocity of the family of rears splits
  have hYdot : ∀ t x, Ydot t x
      = trackVelocity (partialTime (frontOfPath Γ.X P))
          (partialTime (angleOfPath V A P)) (partialTime δ) (angleOfPath V A P) δ t (sf t x)
        + (partialTime sf t x) • ((Real.cos (δ t (sf t x)) : ℂ)
          * Complex.exp (Complex.I *
            (rearAngle (angleOfPath V A P t) (δ t) (sf t x) : ℂ))) := by
    intro t x
    have hEq : Ydot t x = rearOwnVelocity Γ.X V A P δ sf t x :=
      (hYt t x).unique (hasDerivAt_rearOwnVelocity hFc1 hΘc1 hδC hsfC t x)
    rw [hEq]
    exact rearOwnVelocity_eq_trackVelocity hFc1 hΘc1 hδC hsfC hFtangent hΘd hsteer t x
  have hsft : ∀ t x, HasDerivAt (fun r => sf r x) (partialTime sf t x) t :=
    hasDerivAt_partialTime (hsfC.differentiable (by norm_num))
  -- the front does not move at the marked point
  have hFdiff : Differentiable ℝ (uncurry (frontOfPath Γ.X P)) :=
    hFc1.differentiable (by norm_num)
  have hbase : ∀ t, partialTime (frontOfPath Γ.X P) t 0 = 0 := by
    intro t
    have hfun : (fun r => frontOfPath Γ.X P r 0) = fun r => Γ.X r 0 := by
      funext r; simp [frontOfPath]
    have hd : HasDerivAt (fun r => Γ.X r 0) ((Γ.eta t 0 : ℂ) * Γ.nu t 0) t :=
      Γ.hasDerivAt_time t 0
    have hd0 : HasDerivAt (fun r => Γ.X r 0) 0 t := by
      simpa [hmark t] using hd
    have h := hasDerivAt_partialTime hFdiff t 0
    rw [hfun] at h
    exact h.unique hd0
  have hxi0 : ∀ t,
      frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t 0 = 0 := fun t =>
    (RearBaseDrift.frameTangential_rearOwn_base (kh := kh) hkh0 hkh1
      (fun r => hδcont.comp (continuous_const.prodMk continuous_id)) hstrip0 hstrip1
      hsfinv hsft hYdot t).trans
      (RearBaseDrift.frontBaseDrift_eq_zero_of_velocity_zero (hbase t))
  exact SelInvFrontStripFundamentalDriftC2.dist_selInv_le_of_front_strip_fundamental_drift_C2
    Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont
    hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper hKnbd
    hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4
    hsfinv hmark hevd hΘb hkbd hklip hYt hδC hsfC hYdotC hangC hkC1 hper hjac hlink hkappa1
    halphaT hkT halphaTc hkTc halphaTS hmixed hxi0 hetaU hetaUbd hnumA hnumK hsmall

end SelInvFrontBaseDriftC2
