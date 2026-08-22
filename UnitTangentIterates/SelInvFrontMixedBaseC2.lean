import Mathlib
import UnitTangentIterates.SelInvFrontMotionBaseC2
import UnitTangentIterates.SelInvFrontMixedFundamentalDriftC2

/-!
# The `C²` estimate with the mixed-partial hypothesis discharged

`SelInvFrontMotionBaseC2.dist_selInv_le_of_front_motion_base_C2` still asks the caller
for the symmetry of the mixed partial derivatives of the family of selected
rears: a common value `W` for the parameter derivative of the unit tangent
`e^{iΨ}` and for the arclength derivative of the velocity written in the moving
frame.

That is Clairaut's theorem for the family `Y` of rear tracks, and its `C²`
regularity is not an extra assumption either: the two partial derivatives of `Y`
are the velocity `Ẏ`, jointly `C³` by hypothesis, and the unit tangent `e^{iΨ}`,
jointly `C³` because the rear tangent angle is, so `Y` is jointly `C²`
(`RearOwnTangential.contDiff_succ_of_partials`).  The arclength derivative of
`Y` is the unit tangent because each slice is carried in its own arclength
(`RearOwnArclength.hasDerivAt_rearOwn_space`), the fronts being unit-speed in
the arclength of the path (`FrontFromPath.exp_angleOfPath`), and the velocity is
`(ξ + iη)e^{iΨ}` (`RearFamilyFrame.frame_reconstruct`).

This is the base-point form: besides the drift bound, the vanishing of the
tangential drift of the selected rears at the marked point is discharged too,
from the marked point of the path being at rest, `∀ t, Γ.eta t 0 = 0`.

Main result: `dist_selInv_le_of_front_mixed_base_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvFrontMixedBaseC2

open SelInvFrontMixedFundamentalDriftC2

open SelInvFrontMixedFundamentalC2

open SelInvFrontMixedC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed GaugeFlowVariableSpeedPath GaugeFlowDerivCost
  GaugeMarkedDataOfRearFamily GaugeFlowUniqueness FlowDerivative
  GaugeFlowTimeDerivative GaugeFlowSupJacobi SelInvFrontCostC2 RearJacobiSourceCost
  SelInvFrontSourceC2 SelInvFrontStripC2 SelInvFrontMotionC2 RearOwnTangential

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, with the symmetry
of the mixed partial derivatives of the family of selected rears proved rather
than assumed.** -/
theorem dist_selInv_le_of_front_mixed_base_C2 {p q : Data} (Γ : NormalPath p q)
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
    {Ydot : ℝ → ℝ → ℂ} {etaF : ℝ → ℝ → ℝ}
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
  have hsfspace : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x :=
    fun t x => SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hδcont hstrip0 hstrip1
      hsfinv t x
  have hcospos : ∀ t s, 0 < Real.cos (δ t s) := by
    intro t s
    obtain ⟨-, hcge, hgpos, -⟩ := strip_bounds hkh0 hkh1 (hstrip0 t s) (hstrip1 t s)
    exact lt_of_lt_of_le hgpos hcge
  have hcosne : ∀ t s, Real.cos (δ t s) ≠ 0 := fun t s => ne_of_gt (hcospos t s)
  -- the tangent angle of the fronts
  have hcurvcont : ∀ t, Continuous (curvOfPath V A P t) := by
    intro t
    have heq : curvOfPath V A P t = fun s => Kn t (s / P t) := by
      funext s; exact hKeq t s
    rw [heq]
    exact (hKnC3.continuous.comp (continuous_const.prodMk
      (continuous_id.div_const (P t)))).congr fun s => rfl
  have hΘ : ∀ t s, HasDerivAt (angleOfPath V A P t) (curvOfPath V A P t s) s :=
    fun t s => hasDerivAt_angleOfPath (hcurvcont t) s
  have hVdiff : ∀ t, Differentiable ℝ (V t) := fun t u => (hA t u).differentiableAt
  have hVcont : ∀ t, Continuous (V t) := fun t => (hVdiff t).continuous
  have hFtangent : ∀ t s, HasDerivAt (frontOfPath Γ.X P t)
      (Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ))) s := by
    intro t s
    rw [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s]
    exact hasDerivAt_frontOfPath_tangent (hV t) (hPpos t) s
  -- each slice of the family of rears is carried in its own arclength
  have hYspace : ∀ t x, HasDerivAt
      (rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf t)
      (rearOwnTangent (angleOfPath V A P) δ sf t x) x :=
    fun t x => hasDerivAt_rearOwn_space (K := curvOfPath V A P) hFtangent hΘ hsteer
      hsfspace hcosne t x
  -- so the family is jointly `C²`
  have hTC1 : ContDiff ℝ (1 : ℕ) (uncurry (rearOwnTangent (angleOfPath V A P) δ sf)) := by
    have heq : uncurry (rearOwnTangent (angleOfPath V A P) δ sf)
        = fun p : ℝ × ℝ => Complex.exp (Complex.I *
          ((uncurry (rearOwnAngle (angleOfPath V A P) δ sf) p : ℝ) : ℂ)) := rfl
    rw [heq]
    exact contDiff_expI (n := 1) (hangC.of_le (by norm_num))
  have hYdotC1 : ContDiff ℝ (1 : ℕ) (uncurry Ydot) := hYdotC.of_le (by norm_num)
  have hY2 : ContDiff ℝ 2
      (uncurry (rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf)) := by
    have h := contDiff_succ_of_partials (n := 1) hYt hYspace hYdotC1 hTC1
    exact_mod_cast h
  have hYdotdiff : Differentiable ℝ (uncurry Ydot) := hYdotC1.differentiable (by norm_num)
  have hTdiff : Differentiable ℝ (uncurry (rearOwnTangent (angleOfPath V A P) δ sf)) :=
    hTC1.differentiable (by norm_num)
  -- Clairaut
  have hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I *
          (rearOwnAngle (angleOfPath V A P) δ sf r s : ℂ))) W t ∧
      HasDerivAt (fun x =>
          (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x : ℂ)
            * Complex.exp (Complex.I *
              (rearOwnAngle (angleOfPath V A P) δ sf t x : ℂ))
          + (frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x : ℂ)
            * (Complex.I * Complex.exp (Complex.I *
              (rearOwnAngle (angleOfPath V A P) δ sf t x : ℂ)))) W s := by
    intro t s
    refine ⟨deriv (Ydot t) s, ?_, ?_⟩
    · -- the parameter derivative of the unit tangent
      have hd : HasDerivAt (fun r => rearOwnTangent (angleOfPath V A P) δ sf r s)
          (partialTime (rearOwnTangent (angleOfPath V A P) δ sf) t s) t :=
        hasDerivAt_partialTime hTdiff t s
      have hcl := MixedPartials.deriv_partial_comm hY2 t s
      have hL : (fun a' => deriv (fun x' =>
          rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf a' x') s)
          = fun a' => rearOwnTangent (angleOfPath V A P) δ sf a' s := by
        funext a'; exact (hYspace a' s).deriv
      have hR : (fun x' => deriv (fun a' =>
          rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf a' x') t)
          = fun x' => Ydot t x' := by
        funext x'; exact (hYt t x').deriv
      rw [hL, hR] at hcl
      have hval : partialTime (rearOwnTangent (angleOfPath V A P) δ sf) t s
          = deriv (Ydot t) s := by
        rw [← hd.deriv]; exact hcl
      rw [hval] at hd
      exact hd
    · -- the arclength derivative of the velocity in the moving frame
      have hfun : (fun x =>
          (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x : ℂ)
            * Complex.exp (Complex.I *
              (rearOwnAngle (angleOfPath V A P) δ sf t x : ℂ))
          + (frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x : ℂ)
            * (Complex.I * Complex.exp (Complex.I *
              (rearOwnAngle (angleOfPath V A P) δ sf t x : ℂ)))) = Ydot t := by
        funext x
        have h := frame_reconstruct (Ydot t x)
          (rearOwnAngle (angleOfPath V A P) δ sf t x)
        rw [← h]
        simp only [frameTangential, frameNormal]
        ring
      rw [hfun]
      exact ((hasDerivAt_partialArc hYdotdiff t s).differentiableAt).hasDerivAt
  exact SelInvFrontMotionBaseC2.dist_selInv_le_of_front_motion_base_C2
    Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont
    hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
    hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
    hFc4 hΘc4 hsfinv hmark hevd hΘb hkbd hklip hYt hδC hsfC hYdotC hangC hkC1 hper hjac
    hlink hkappa1 hmixed hetaU hetaUbd hnumA hnumK hsmall

end SelInvFrontMixedBaseC2
