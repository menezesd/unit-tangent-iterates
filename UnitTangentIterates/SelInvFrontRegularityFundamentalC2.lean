import Mathlib
import UnitTangentIterates.SelInvFrontVelocityFundamentalC2
import UnitTangentIterates.SelInvFrontRegularityC2

/-!
# The `C²` estimate with the regularity of the rear data discharged

`SelInvFrontVelocityFundamentalC2.dist_selInv_le_of_front_velocity_fundamental_C2` still asks
separately for the regularity of four objects attached to the family of
selected rears: the change of variable `sf`, the velocity of the rears, the
rear tangent angle and the rear curvature `tan δ`.  All four are as smooth as
the front data and the steering angle, by the regularity theory of
`RearOwnHigherRegularity.lean`:

* `contDiff_sf` — the change of variable inherits the regularity of `δ`, the
  rear arclength having derivative `cos δ ≥ √(1−κ̂²) > 0`;
* `contDiff_rearOwnAngle` — the rear tangent angle is `Θ ∘ sf − δ ∘ sf`;
* `contDiff_rearOwnVelocity` — the velocity of the rears is the `trackVelocity`
  of the front data plus the tangential sliding of the change of variable
  (`rearOwnVelocity_eq_trackVelocity`);
* and `tan δ = sin δ / cos δ` is smooth on the selected strip.

So the four hypotheses collapse into one: the steering angle is jointly `C⁴`,
as the front data already is.

Main results: `rearOwnVelocity_eq_trackVelocity`,
`dist_selInv_le_of_front_regularity_fundamental_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvFrontRegularityFundamentalC2

open SelInvFrontRegularityC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed GaugeFlowVariableSpeedPath GaugeFlowDerivCost
  GaugeMarkedDataOfRearFamily GaugeFlowUniqueness FlowDerivative
  GaugeFlowTimeDerivative GaugeFlowSupJacobi SelInvFrontCostC2 RearJacobiSourceCost
  SelInvFrontSourceC2 SelInvFrontStripC2 SelInvFrontMotionC2 SelInvFrontMixedC2
  SelInvFrontJacobiC2 SelInvFrontVelocityC2 RearOwnTangential

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, with the
regularity of the rear data deduced from that of the front data.**  The
hypotheses are those of
`SelInvFrontVelocityFundamentalC2.dist_selInv_le_of_front_velocity_fundamental_C2` with the four
regularity hypotheses on the change of variable, on the velocity of the rears,
on the rear tangent angle and on the rear curvature replaced by the single
requirement that the steering angle be jointly `C⁴`. -/
theorem dist_selInv_le_of_front_regularity_fundamental_C2 {p q : Data} (Γ : NormalPath p q)
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
    {Rb : ℝ → ℝ}
    {Pv0 khat rr : ℝ}
    (hδC4 : ContDiff ℝ (4 : ℕ) (uncurry δ))
    (hper : ∀ t, Function.Periodic
      (frameNormal (rearOwnVelocity Γ.X V A P δ sf) (rearOwnAngle (angleOfPath V A P) δ sf) t)
      (rearArclength (δ t) (P t)))
    (hkappa1 : rearKappa1 kh ≤ khat)
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (rearArclength (δ t) (P t)),
      |frameTangential (rearOwnVelocity Γ.X V A P δ sf) (rearOwnAngle (angleOfPath V A P) δ sf) t x| ≤ Rb t)
    (hRbm : ∀ t, Rb t ≤ rr * Γ.m t) (hr : 0 ≤ rr)
    (hxi0 : ∀ t, frameTangential (rearOwnVelocity Γ.X V A P δ sf) (rearOwnAngle (angleOfPath V A P) δ sf) t 0 = 0)
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
          (-frameTangential (rearOwnVelocity Γ.X V A P δ sf) (rearOwnAngle (angleOfPath V A P) δ sf) t (Phi t u)) t) ∧
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
  have hcospos : ∀ t s, 0 < Real.cos (δ t s) := by
    intro t s
    obtain ⟨-, hcge, hgpos, -⟩ := strip_bounds hkh0 hkh1 (hstrip0 t s) (hstrip1 t s)
    exact lt_of_lt_of_le hgpos hcge
  have hδC2 : ContDiff ℝ (2 : ℕ) (uncurry δ) := hδC4.of_le (by norm_num)
  have hδC1 : ContDiff ℝ (1 : ℕ) (uncurry δ) := hδC4.of_le (by norm_num)
  have hFc1 : ContDiff ℝ (1 : ℕ) (uncurry (frontOfPath Γ.X P)) := hFc4.of_le (by norm_num)
  have hΘc1 : ContDiff ℝ (1 : ℕ) (uncurry (angleOfPath V A P)) := hΘc4.of_le (by norm_num)
  ------------------------------------------------------------------
  -- the change of variable is as smooth as the steering angle
  ------------------------------------------------------------------
  have hsfC4 : ContDiff ℝ (4 : ℕ) (uncurry sf) := by
    have h := contDiff_sf (n := 3) (kh := kh) hkh0 hkh1 (by exact_mod_cast hδC4)
      hstrip0 hstrip1 hsfinv
    exact_mod_cast h
  have hsfC3 : ContDiff ℝ (3 : ℕ) (uncurry sf) := hsfC4.of_le (by norm_num)
  have hsfC : ContDiff ℝ (1 : ℕ) (uncurry sf) := hsfC4.of_le (by norm_num)
  ------------------------------------------------------------------
  -- the rear tangent angle and the rear curvature
  ------------------------------------------------------------------
  have hangC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle (angleOfPath V A P) δ sf)) :=
    contDiff_rearOwnAngle (hΘc4.of_le (by norm_num)) (hδC4.of_le (by norm_num)) hsfC3
  have hkC1 : ContDiff ℝ 1 (uncurry fun t x => Real.tan (δ t (sf t x))) := by
    have hcomp : ContDiff ℝ (1 : ℕ) (fun p : ℝ × ℝ => (p.1, uncurry sf p)) :=
      contDiff_fst.prodMk hsfC
    have hg : ContDiff ℝ (1 : ℕ) (fun p : ℝ × ℝ => uncurry δ (p.1, uncurry sf p)) :=
      hδC1.comp hcomp
    have hfun : (uncurry fun t x => Real.tan (δ t (sf t x)))
        = fun p : ℝ × ℝ => Real.sin (uncurry δ (p.1, uncurry sf p))
          / Real.cos (uncurry δ (p.1, uncurry sf p)) := by
      funext p
      simp [uncurry, Real.tan_eq_sin_div_cos]
    rw [hfun]
    exact (Real.contDiff_sin.comp hg).div (Real.contDiff_cos.comp hg)
      fun p => ne_of_gt (hcospos p.1 (sf p.1 p.2))
  ------------------------------------------------------------------
  -- the velocity of the family of selected rears
  ------------------------------------------------------------------
  have hVdiff : ∀ t, Differentiable ℝ (V t) := fun t u => (hA t u).differentiableAt
  have hVcont : ∀ t, Continuous (V t) := fun t => (hVdiff t).continuous
  have hFtangent : ∀ t s, HasDerivAt (frontOfPath Γ.X P t)
      (Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ))) s := by
    intro t s
    rw [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s]
    exact hasDerivAt_frontOfPath_tangent (hV t) (hPpos t) s
  have hcurvcont : ∀ t, Continuous (curvOfPath V A P t) := by
    intro t
    have heq : curvOfPath V A P t = fun s => Kn t (s / P t) := by
      funext s; exact hKeq t s
    rw [heq]
    exact (hKnC3.continuous.comp (continuous_const.prodMk
      (continuous_id.div_const (P t)))).congr fun s => rfl
  have hΘd : ∀ t s, HasDerivAt (angleOfPath V A P t) (curvOfPath V A P t s) s :=
    fun t s => hasDerivAt_angleOfPath (hcurvcont t) s
  have hVelC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnVelocity Γ.X V A P δ sf)) := by
    refine contDiff_rearOwnVelocity (n := 3) (hΘc4.of_le (by norm_num))
      (hδC4.of_le (by norm_num)) hsfC3
      (contDiff_partialTime_self (n := 3) (by exact_mod_cast hFc4))
      (contDiff_partialTime_self (n := 3) (by exact_mod_cast hΘc4))
      (contDiff_partialTime_self (n := 3) (by exact_mod_cast hδC4))
      (contDiff_partialTime_self (n := 3) (by exact_mod_cast hsfC4)) ?_
    intro t x
    exact rearOwnVelocity_eq_trackVelocity hFc1 hΘc1 hδC1 hsfC hFtangent hΘd hsteer t x
  exact SelInvFrontVelocityFundamentalC2.dist_selInv_le_of_front_velocity_fundamental_C2
    Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont
    hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
    hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
    hFc4 hΘc4 hsfinv hmark hevd hΘb hkbd hklip hδC2 hsfC hVelC hangC hkC1 hper
    hkappa1 hRbd hRbm hr hxi0 hetaU hetaUbd hnumA hnumK hsmall

end SelInvFrontRegularityFundamentalC2
