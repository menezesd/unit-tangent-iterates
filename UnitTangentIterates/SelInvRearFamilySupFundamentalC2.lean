import Mathlib
import UnitTangentIterates.SelInvRearFamilyFundamentalC2
import UnitTangentIterates.GaugeSupDensities
import UnitTangentIterates.GaugeFlowSupJacobi
import UnitTangentIterates.GaugeFlowMarkedData

/-!
# The sup densities of the family of selected rears in the gauge marking

`SelInvRearFamilyFundamentalC2.dist_selInv_le_of_rear_family_fundamental_C2`
bounds the
marked (`C²`) distance of the two marked selected inverses of the ends of a
normal path of fronts, with the comparison path produced from the family of
selected rears.  One hypothesis of that statement is still about the marking
`Φ` it produces: the cost density `m` of the family of rears has to dominate the
three sup norms

`supNorm (η∘Φ_t)`, `supNorm ∂_u(η∘Φ_t)`, `supNorm ∂²_u(η∘Φ_t)`

of its normal rate read in that marking — the condition
`PathMetric.NormalPath.le_m_sup` of a normal path.

This file discharges it.  The marking is the flow of minus the tangential
component `ξ` of the motion of the rears — the flow equation is a conclusion of
the statement above — so its two derivatives in the parameter are bounded by the
explicit constants of `GaugeFlowDerivCost.lean`,

`|∂_uΦ| ≤ costP1 ℓ κ̂ M` ,  `|∂²_uΦ| ≤ costG1 ℓ κ̂ κ₂ M` ,

because `|∂ₓξ| ≤ rearKappa1 κ̂ · m` and `|∂²ₓξ| ≤ rearKappa2 κ̂ · m`
(`RearOwnTangentialCost.lean`, `RearOwnTangentialCostC2.lean`).  On the other
side the inverse Jacobi ODE `∂ₓη = g − η` gives the two arclength derivatives of
the normal rate from the maximum principle: with
`S₀ = m_F/√(1−κ̂²)` the bound of `η` and of `g`,

`|∂ₓη| ≤ 2S₀` ,  `|∂²ₓη| ≤ D + 2S₀` ,

`D` being the bound of `∂ₓg`.  The chain rule of `GaugeSupDensities.lean` then
turns the two families of bounds into the three sup norms, so that all that is
asked of the cost density of the rears is that it dominate

`2S₀·costP1`  and  `(D + 2S₀)·costP1² + 2S₀·costG1` ,

two conditions on the *data of the path*, with no reference to the marking.

The comparison curve of the estimate — the terminal selected inverse read in
the gauge marking — is produced at the same time by
`GaugeFlowMarkedData.exists_data_of_flow_marking`, so that the conclusion is an
unconditional bound for the marked distance of the two selected inverses.

Main result: `dist_selInv_le_of_rear_family_sup_fundamental_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvRearFamilySupFundamentalC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed GaugeFlowVariableSpeedPath GaugeFlowDerivCost
  GaugeMarkedDataOfRearFamily GaugeFlowUniqueness FlowDerivative
  GaugeFlowTimeDerivative GaugeFlowSupJacobi

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, with the sup
densities of the family of selected rears discharged.**

The hypotheses are those of
`SelInvRearFamilyFundamentalC2.dist_selInv_le_of_rear_family_fundamental_C2`,
with the condition on the marking traded for two conditions on the cost density of the
family of rears; nothing is assumed about the marking itself.  The comparison
curve of that statement is built here as well
(`GaugeFlowMarkedData.exists_data_of_flow_marking`), so the estimate is an
unconditional bound for the marked distance of the two selected inverses. -/
theorem dist_selInv_le_of_rear_family_sup_fundamental_C2 {p q : Data} (Γ : NormalPath p q)
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
    {Ydot : ℝ → ℝ → ℂ} {etaF alphaT kT gS : ℝ → ℝ → ℝ} {m Kx Rb Dd : ℝ → ℝ}
    {Pv0 khat dd rr kx : ℝ}
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
    (hKxbd : ∀ t x, |(curvOfPath V A P t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3| ≤ Kx t)
    (hKxnn : ∀ t, 0 ≤ Kx t) (hKxm : ∀ t, Kx t ≤ kx)
    (hkXc : Continuous (uncurry fun t x =>
      (curvOfPath V A P t (sf t x) - Real.sin (δ t (sf t x)))
        / Real.cos (δ t (sf t x)) ^ 3))
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (rearArclength (δ t) (P t)),
      |frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x| ≤ Rb t)
    (hRbm : ∀ t, Rb t ≤ rr * m t) (hr : 0 ≤ rr)
    (hxi0 : ∀ t,
      frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t 0 = 0)
    (hgSd : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x')))
      (gS t x) x)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t) (hDm : ∀ t, Dd t ≤ dd * m t)
    (hmc : Continuous m) (hm0 : ∀ t, 0 ≤ m t)
    (hmstop : ∀ t ∉ Ioo (0 : ℝ) Γ.T, m t = 0)
    (hmge : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ m t)
    (hnumA : 2 + 2 * khat * rr ≤ 1 / Pv0)
    (hnumK : (dd + 2) + khat ^ 2 + 2 * rr * kx ≤ 1 / Pv0 ^ 2 + khat ^ 2)
    -- the cost density of the family of rears dominates the two derivative
    -- densities of its normal rate, read in the gauge marking
    (hsupA : ∀ t, 2 * (Γ.m t / Real.sqrt (1 - kh ^ 2))
      * costP1 (rearArclength (δ 0) (P 0)) khat (∫ s in (0 : ℝ)..Γ.T, m s) ≤ m t)
    (hsupB : ∀ t, (Dd t + 2 * (Γ.m t / Real.sqrt (1 - kh ^ 2)))
        * costP1 (rearArclength (δ 0) (P 0)) khat (∫ s in (0 : ℝ)..Γ.T, m s) ^ 2
      + 2 * (Γ.m t / Real.sqrt (1 - kh ^ 2))
        * costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
          (∫ s in (0 : ℝ)..Γ.T, m s) ≤ m t) :
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
                  (costP1 (rearArclength (δ 0) (P 0)) khat (∫ t in (0 : ℝ)..Γ.T, m t)) khat
                  (costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
                    (∫ t in (0 : ℝ)..Γ.T, m t))
                  (khat * costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
                      (∫ t in (0 : ℝ)..Γ.T, m t)
                    + rearKappa2 kh * costP1 (rearArclength (δ 0) (P 0)) khat
                      (∫ t in (0 : ℝ)..Γ.T, m t) ^ 2)
                * ∫ t in (0 : ℝ)..Γ.T, m t := by
  ------------------------------------------------------------------
  -- the front data of the path
  ------------------------------------------------------------------
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hVcont : ∀ t, Continuous (V t) := fun t =>
    continuous_iff_continuousAt.2 fun u => (hA t u).continuousAt
  have hcurvcont : ∀ t, Continuous (curvOfPath V A P t) := fun t =>
    continuous_curvOfPath (hVcont t) (hAcont t)
  have hF : ∀ t s, HasDerivAt (frontOfPath Γ.X P t)
      (Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ))) s := by
    intro t s
    rw [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s]
    exact hasDerivAt_frontOfPath_tangent (hV t) (hPpos t) s
  have hΘ : ∀ t s, HasDerivAt (angleOfPath V A P t) (curvOfPath V A P t s) s :=
    fun t s => hasDerivAt_angleOfPath (hcurvcont t) s
  have hslice : ∀ t, Function.Periodic (δ t) (P t) ∧
      (∀ s, HasDerivAt (δ t) (curvOfPath V A P t s - Real.sin (δ t s)) s) ∧
      (∀ s, δ t s ∈ Icc (0 : ℝ) (Real.arcsin kh)) := fun t =>
    delta_slice_of_normalized (t := t) (hPpos t) hdelta hKeq hsol hstrip hdnper
  have hsteer : ∀ t s, HasDerivAt (δ t) (curvOfPath V A P t s - Real.sin (δ t s)) s :=
    fun t => (hslice t).2.1
  have hstrip0 : ∀ t s, 0 ≤ δ t s := fun t s => ((hslice t).2.2 s).1
  have hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh := fun t s => ((hslice t).2.2 s).2
  have hK : ∀ t s, |curvOfPath V A P t s| ≤ kh := by
    intro t s
    rw [hKeq t s]
    exact hKnbd t _
  have hcos : ∀ t s, Real.cos (δ t s) ≠ 0 := fun t s =>
    ne_of_gt (SelectedPathData.cos_steering_pos hkh0 hkh1 (hstrip0 t) (hstrip1 t) s)
  have hδcont : Continuous (uncurry δ) := hδC.continuous
  have hsfspace : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x :=
    fun t x => SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hδcont hstrip0 hstrip1
      hsfinv t x
  have hQpos : ∀ t, 0 < rearArclength (δ t) (P t) := fun t =>
    SelectedPathData.rearPeriod_pos (hPpos t) hkh0 hkh1
      (hδcont.comp (continuous_const.prodMk continuous_id)) (hstrip0 t) (hstrip1 t)
  ------------------------------------------------------------------
  -- the bound, with the sup condition on the marking still to be checked
  ------------------------------------------------------------------
  obtain ⟨hperimp, hperimq, Phi, hPhi0, hbase, hPhiflow, hmain⟩ :=
    SelInvRearFamilyFundamentalC2.dist_selInv_le_of_rear_family_fundamental_C2
      Γ hc hkmin hp hub
      hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper
      hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd
      hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4
      hsfinv hmark hevd hΘb hkbd hklip hYt hδC hsfC hYdotC hangC hkC1 hper hjac hlink
      hkappa1 halphaT hkT halphaTc hkTc halphaTS hmixed hKxbd hKxnn hKxm hkXc hRbd hRbm
      hr hxi0 hgSd hgSbd hDm hmc hm0 hmstop hmge hnumA hnumK
  refine ⟨hperimp, hperimq, Phi, hPhi0, hbase, hPhiflow, ?_⟩
  ------------------------------------------------------------------
  -- the three sup densities of the rear normal rate in the marking
  ------------------------------------------------------------------
  have hellpos : 0 < rearArclength (δ 0) (P 0) := hQpos 0
  have hPhi0' : ∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u := by
    intro u
    rw [hPhi0 u, hperimp]
  -- the regularity of the tangential component of the motion of the rears
  have hxiC3 : ContDiff ℝ (3 : ℕ)
      (uncurry (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf))) :=
    RearOwnFrameData.contDiff_frameTangential hYdotC hangC
  have hxiC1 : ContDiff ℝ (1 : ℕ)
      (uncurry (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf))) :=
    hxiC3.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3))
  have hpxC2 : ContDiff ℝ (2 : ℕ)
      (uncurry (partialX
        (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf)))) :=
    contDiff_partialX (n := 2) (by exact_mod_cast hxiC3)
  have hpxC1 : ContDiff ℝ (1 : ℕ)
      (uncurry (partialX
        (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf)))) :=
    hpxC2.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
  have hpxxC1 : ContDiff ℝ (1 : ℕ)
      (uncurry (partialX (partialX
        (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf))))) :=
    contDiff_partialX (n := 1) (by exact_mod_cast hpxC2)
  -- the two tangential estimates, against the cost density of the rears
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hroot1 : Real.sqrt (1 - kh ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  have hcostle : ∀ t, Γ.m t ≤ m t := by
    intro t
    refine le_trans ?_ (hmge t)
    rw [le_div_iff₀ hroot]
    nlinarith [Γ.m_nonneg t]
  have hkhat : 0 ≤ khat := le_trans (rearKappa1_nonneg hkh0 hkh1) hkappa1
  have hCbd : ∀ t x, |partialX
      (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf)) t x| ≤ khat * m t := by
    intro t x
    refine le_trans (abs_partialX_frameTangential_le_rearKappa1 (K := curvOfPath V A P)
      (Q := fun t => rearArclength (δ t) (P t)) (etaF := etaF) (P := P) Γ hkh0 hkh1 hstrip0
      hstrip1 hF hΘ hsteer hsfspace hcos hYt (hYdotC.of_le (by norm_num))
      (hangC.of_le (by norm_num)) hQpos hper hjac hPpos hlink t x) ?_
    have h1 : rearKappa1 kh * Γ.m t ≤ rearKappa1 kh * m t :=
      mul_le_mul_of_nonneg_left (hcostle t) (rearKappa1_nonneg hkh0 hkh1)
    have h2 : rearKappa1 kh * m t ≤ khat * m t :=
      mul_le_mul_of_nonneg_right hkappa1 (hm0 t)
    linarith
  have hC2bd : ∀ t x, |partialX (partialX
      (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf))) t x|
        ≤ rearKappa2 kh * m t := by
    intro t x
    refine le_trans (abs_partialX_partialX_frameTangential_le_cost_density
      (K := curvOfPath V A P) (Q := fun t => rearArclength (δ t) (P t)) (etaF := etaF)
      (P := P) Γ hkh0 hkh1 hstrip0 hstrip1 hK hF hΘ hsteer hsfspace hcos hYt
      (hYdotC.of_le (by norm_num)) (hangC.of_le (by norm_num)) hQpos hper hjac hPpos hlink
      t x) ?_
    exact mul_le_mul_of_nonneg_left (hcostle t) (rearKappa2_nonneg hkh0 hkh1)
  -- the two bounds of the maximum principle
  have hetabd : ∀ t x,
      |frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x|
        ≤ Γ.m t / Real.sqrt (1 - kh ^ 2) := fun t x =>
    abs_frameNormal_le_cost (Q := fun t => rearArclength (δ t) (P t)) (etaF := etaF)
      (P := P) Γ hkh0 hkh1 hstrip0 hstrip1 hQpos hper hjac hPpos hlink t x
  have hgbd : ∀ t x, |etaF t (sf t x) / Real.cos (δ t (sf t x))|
      ≤ Γ.m t / Real.sqrt (1 - kh ^ 2) := fun t x =>
    abs_jacobiSource_le_cost (etaF := etaF) (P := P) (sf := sf) Γ hkh0 hkh1 hstrip0
      hstrip1 hPpos hlink t x
  ------------------------------------------------------------------
  -- the comparison curve: the terminal selected inverse read in the marking
  ------------------------------------------------------------------
  obtain ⟨_, _, hbmem, -, -, -⟩ :=
    SelectedInverseMap.selInv_spec hcq hkminq hkh1 hq hubq hinjRq
  have hLpos : 0 < perim (SelectedInverseMap.selInv kh q) := by
    rw [hperimq]; exact hQpos Γ.T
  obtain ⟨q', hq'0, hq'1, hq'2⟩ :=
    GaugeFlowMarkedData.exists_data_of_flow_marking
      (xi := frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf))
      (xiX := partialX (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf)))
      (xiXX := partialX (partialX
        (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf))))
      (Phi := Phi) (m := m) (ell := rearArclength (δ 0) (P 0)) (kappa := khat)
      (kappa2 := rearKappa2 kh) (T := Γ.T)
      (L := perim (SelectedInverseMap.selInv kh q)) (t0 := Γ.T)
      (b := SelectedInverseMap.selInv kh q)
      Γ.T_pos hellpos hLpos hxiC1.continuous
      (fun s x => hasDerivAt_partialX hxiC1 s x)
      hpxC1.continuous (fun s x => hasDerivAt_partialX hpxC1 s x) hpxxC1.continuous
      hCbd hC2bd hkhat (rearKappa2_nonneg hkh0 hkh1) hmc hm0 hmstop hPhi0' hPhiflow
      hbmem.hasDerivAt_curve hbmem.hasDerivAt_vel
  refine hmain q' hq'0 hq'1 hq'2 ?_
  ------------------------------------------------------------------
  -- the chain rule
  ------------------------------------------------------------------
  exact supNorm_le_of_flow_jacobi (xi := frameTangential Ydot
      (rearOwnAngle (angleOfPath V A P) δ sf))
    (xiX := partialX (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf)))
    (xiXX := partialX (partialX
      (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf))))
    (eta := frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf))
    (g := fun t x => etaF t (sf t x) / Real.cos (δ t (sf t x))) (gS := gS) (Phi := Phi)
    (m := m) (S0 := fun t => Γ.m t / Real.sqrt (1 - kh ^ 2)) (Dd := Dd)
    (ell := rearArclength (δ 0) (P 0)) (kappa := khat) (kappa2 := rearKappa2 kh)
    Γ.T_pos hellpos hxiC1.continuous
    (fun s x => hasDerivAt_partialX hxiC1 s x) hpxC1.continuous
    (fun s x => hasDerivAt_partialX hpxC1 s x) hpxxC1.continuous hCbd hC2bd hkhat
    (rearKappa2_nonneg hkh0 hkh1) hmc hm0 hmstop hPhi0' hPhiflow hjac hgSd hetabd hgbd
    hgSbd hmge hsupA hsupB
