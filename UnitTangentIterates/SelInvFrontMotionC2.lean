import Mathlib
import UnitTangentIterates.SelInvFrontStripC2
import UnitTangentIterates.MixedPartials

/-!
# The `C²` estimate with the time derivatives of the rear frame discharged

`SelInvFrontStripC2.dist_selInv_le_of_front_strip_C2` still asks the caller for
the parameter derivatives of the two data of the family of selected rears which
its own regularity hypotheses already determine: the derivative `alphaT` of the
rear tangent angle, the derivative `kT` of the rear curvature `tan δ`, their
joint continuity, and the relation `∂ₓ alphaT = kT`.

All four are consequences of the joint regularity already assumed.  The
parameter derivatives exist and are jointly continuous because the two families
are jointly `C³` and `C¹` respectively (`RearOwnHigherRegularity.partialTime`),
and the relation between them is Clairaut's theorem
(`MixedPartials.deriv_partial_comm`) combined with the identity
`∂ₓΨ = tan δ(sf)` for the rear tangent angle
(`RearOwnTangential.hasDerivAt_rearOwnAngle_space`).

Main results:

* `hasDerivAt_partialTime_arc` — for a jointly `C²` family whose arclength
  derivative is `fx`, the arclength derivative of the parameter derivative is
  the parameter derivative of `fx`;
* `dist_selInv_le_of_front_motion_C2` — the estimate with `alphaT`, `kT` and
  their four hypotheses removed.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvFrontMotionC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed GaugeFlowVariableSpeedPath GaugeFlowDerivCost
  GaugeMarkedDataOfRearFamily GaugeFlowUniqueness FlowDerivative
  GaugeFlowTimeDerivative GaugeFlowSupJacobi SelInvFrontCostC2 RearJacobiSourceCost
  SelInvFrontSourceC2 SelInvFrontStripC2 RearOwnTangential

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The arclength derivative of the parameter derivative.**  For a jointly
`C²` family `f` whose arclength derivative is `fx`, the parameter derivative
`∂_t f` is differentiable in the arclength, with derivative `∂_t fx`; this is
Clairaut's theorem. -/
theorem hasDerivAt_partialTime_arc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f fx : ℝ → ℝ → E} (hf : ContDiff ℝ 2 (uncurry f))
    (hfx : ∀ t s, HasDerivAt (f t) (fx t s) s) (t s : ℝ) :
    HasDerivAt (partialTime f t) (partialTime fx t s) s := by
  have hfxC1 : ContDiff ℝ (1 : ℕ) (uncurry fx) :=
    contDiff_partialArc_of_hasDerivAt (n := 1) (by exact_mod_cast hf) hfx
  have hfxdiff : Differentiable ℝ (uncurry fx) := hfxC1.differentiable (by norm_num)
  have hptC1 : ContDiff ℝ (1 : ℕ) (uncurry (partialTime f)) :=
    contDiff_partialTime_self (n := 1) (by exact_mod_cast hf)
  have hptdiff : Differentiable ℝ (uncurry (partialTime f)) := hptC1.differentiable (by norm_num)
  have hd : HasDerivAt (partialTime f t) (partialArc (partialTime f) t s) s :=
    hasDerivAt_partialArc hptdiff t s
  have hkey : partialArc (partialTime f) t s = partialTime fx t s := by
    have h1 : partialArc (partialTime f) t s = deriv (fun s' => partialTime f t s') s :=
      hd.deriv.symm
    have h2 : (fun s' => partialTime f t s') = fun s' => deriv (fun r => f r s') t := by
      funext s'
      exact ((hasDerivAt_partialTime (hf.differentiable (by norm_num)) t s').deriv).symm
    have h3 := MixedPartials.deriv_partial_comm hf t s
    have h4 : (fun a' => deriv (fun x' => f a' x') s) = fun a' => fx a' s := by
      funext a'; exact (hfx a' s).deriv
    have h5 : deriv (fun a' => fx a' s) t = partialTime fx t s :=
      (hasDerivAt_partialTime hfxdiff t s).deriv
    rw [h1, h2, ← h3, h4, h5]
  rwa [hkey] at hd

/-- **The `C²` comparison of the two marked selected inverses, with the
parameter derivatives of the rear frame data produced from the regularity of the
family.**

The hypotheses are those of
`SelInvFrontStripC2.dist_selInv_le_of_front_strip_C2`, with the parameter
derivative of the rear tangent angle, that of the rear curvature, their
continuity and the relation between them all removed. -/
theorem dist_selInv_le_of_front_motion_C2 {p q : Data} (Γ : NormalPath p q)
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
    {Ydot : ℝ → ℝ → ℂ} {etaF : ℝ → ℝ → ℝ} {Rb : ℝ → ℝ}
    {Pv0 khat rr : ℝ}
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
    (hRbd : ∀ t x,
      |frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x| ≤ Rb t)
    (hRbm : ∀ t, Rb t ≤ rr * Γ.m t) (hr : 0 ≤ rr)
    -- the parameter derivative of the normal speed of the path
    {etaU : ℝ → ℝ → ℝ} (hetaU : ∀ t u, HasDerivAt (Γ.eta t) (etaU t u) u)
    (hetaUbd : ∀ t u, |etaU t u| ≤ Γ.m t)
    (hnumA : 2 + 2 * khat * rr ≤ 1 / Pv0)
    (hnumK : (jacobiSourceConst kh P0 + 2) + khat ^ 2 + 2 * rr * stripCurvConst kh
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
  have hsfspace : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x :=
    fun t x => SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hδcont hstrip0 hstrip1
      hsfinv t x
  -- the arclength derivative of the tangent angle of the fronts is the curvature
  have hcurvcont : ∀ t, Continuous (curvOfPath V A P t) := by
    intro t
    have heq : curvOfPath V A P t = fun s => Kn t (s / P t) := by
      funext s; exact hKeq t s
    rw [heq]
    exact (hKnC3.continuous.comp (continuous_const.prodMk
      (continuous_id.div_const (P t)))).congr fun s => rfl
  have hΘ : ∀ t s, HasDerivAt (angleOfPath V A P t) (curvOfPath V A P t s) s :=
    fun t s => hasDerivAt_angleOfPath (hcurvcont t) s
  -- the arclength derivative of the rear tangent angle is the rear curvature
  have hangSpace : ∀ t x, HasDerivAt (rearOwnAngle (angleOfPath V A P) δ sf t)
      (Real.tan (δ t (sf t x))) x :=
    fun t x => hasDerivAt_rearOwnAngle_space (K := curvOfPath V A P) hΘ hsteer hsfspace t x
  have hang2 : ContDiff ℝ 2 (uncurry (rearOwnAngle (angleOfPath V A P) δ sf)) :=
    hangC.of_le (by norm_num)
  have halphaT : ∀ t x, HasDerivAt
      (fun r => rearOwnAngle (angleOfPath V A P) δ sf r x)
      (partialTime (rearOwnAngle (angleOfPath V A P) δ sf) t x) t :=
    hasDerivAt_partialTime (hangC.differentiable (by norm_num))
  have hkT : ∀ t x, HasDerivAt (fun r => Real.tan (δ r (sf r x)))
      (partialTime (fun t' x' => Real.tan (δ t' (sf t' x'))) t x) t :=
    hasDerivAt_partialTime (hkC1.differentiable (by norm_num))
  have halphaTc : Continuous
      (uncurry (partialTime (rearOwnAngle (angleOfPath V A P) δ sf))) :=
    (contDiff_partialTime_self (n := 2) (by exact_mod_cast hangC)).continuous
  have hkTc : Continuous
      (uncurry (partialTime fun t' x' => Real.tan (δ t' (sf t' x')))) :=
    (contDiff_partialTime_self (n := 0) (by exact_mod_cast hkC1)).continuous
  have halphaTS : ∀ t s, HasDerivAt
      (partialTime (rearOwnAngle (angleOfPath V A P) δ sf) t)
      (partialTime (fun t' x' => Real.tan (δ t' (sf t' x'))) t s) s :=
    fun t s => hasDerivAt_partialTime_arc hang2 hangSpace t s
  exact dist_selInv_le_of_front_strip_C2
    (alphaT := partialTime (rearOwnAngle (angleOfPath V A P) δ sf))
    (kT := partialTime fun t' x' => Real.tan (δ t' (sf t' x')))
    Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont
    hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
    hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
    hFc4 hΘc4 hsfinv hmark hevd hΘb hkbd hklip hYt hδC hsfC hYdotC hangC hkC1 hper hjac
    hlink hkappa1 halphaT hkT halphaTc hkTc halphaTS hmixed
    hRbd hRbm hr hetaU hetaUbd hnumA hnumK hsmall

end SelInvFrontMotionC2
