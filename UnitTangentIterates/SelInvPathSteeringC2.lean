import Mathlib
import UnitTangentIterates.SelInvPathAngleC2
import UnitTangentIterates.SteeringNormalizedPeriod

/-!
# The `C²` estimate with the regularity of the steering angle produced

`SelInvPathAngleC2.dist_selInv_le_of_path_angle_C2` still asks the selected
steering angle `δ` of the path of fronts to be jointly `C⁴`.  That is not an
independent hypothesis either.  The normalized steering angle `dn` of the
statement solves the steering equation

```
  ∂_σ dn = P(t) · (Kn(t,σ) − sin dn(t,σ)) ,
```

with `dn(t,·)`, `Kn(t,·)` and `Kdn(t,·)` all `1`-periodic, and the statement
already carries every quantitative datum the smooth-dependence theory of
`SteeringNormalizedPeriod.lean` consumes: the two-sided bounds for the period,
the sup, Lipschitz and Taylor bounds for the curvature and the period, and the
joint `C³` regularity of `Kn`, `Kdn`, `P` and `Pd`.  So `dn` is jointly `C⁴`
(`SteeringNormalizedPeriod.contDiff_four_uncurry_delta`), and hence so is
`δ(t,s) = dn(t, s / P t)`, the steering angle read in the arclength of the
slice.

Main results: `contDiff_four_delta_of_normalized`,
`dist_selInv_le_of_path_steering_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathSteeringC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed GaugeFlowVariableSpeedPath GaugeFlowDerivCost
  GaugeMarkedDataOfRearFamily GaugeFlowUniqueness FlowDerivative
  GaugeFlowTimeDerivative GaugeFlowSupJacobi SelInvFrontCostC2 RearJacobiSourceCost
  SelInvFrontSourceC2 SelInvFrontStripC2 SelInvFrontMotionC2 SelInvFrontMixedC2
  SelInvFrontJacobiC2 SelInvFrontVelocityC2 SelInvFrontRegularityC2
  SelInvFrontChangeVarC2 SelInvFrontClosingC2 SelInvFrontNormalSpeedC2
  SelInvPathRegularityC2 SelInvPathAngleC2 FrontDataRegularity RearOwnTangential

variable {δ dn Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ} {P0 P1 kh Klip Plip : ℝ}

/-- **The steering angle in the arclength of the slices is jointly `C⁴`.**  The
normalized steering angle is jointly `C⁴` by the smooth-dependence theory in the
normalized parameter, and the change of parameter `s ↦ s / P t` is jointly `C⁴`
as well. -/
theorem contDiff_four_delta_of_normalized {Md MP CK CP : ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hdelta : ∀ t s, δ t s = dn t (s / P t))
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
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn)) :
    ContDiff ℝ (4 : ℕ) (uncurry δ) := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hPC3 : ContDiff ℝ (3 : ℕ) P :=
    hPC4.of_le (by exact_mod_cast (by norm_num : (3 : ℕ) ≤ 4))
  have hdnC4 : ContDiff ℝ (4 : ℕ) (uncurry dn) :=
    SteeringNormalizedPeriod.contDiff_four_uncurry_delta hP0 hkh0 hkh1 hPl hPu hsol hstrip
      hdnper hKnper hKdnper hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP
      hPC3 hPdC3 hKnC3 hKdnC3
  have hcomp : ContDiff ℝ (4 : ℕ) (uncurry fun t s => dn t (s / P t)) :=
    SteeringNormalizedPeriod.contDiff_arclength_of_normalized (n := 4) hdnC4 hPC4 hPpos
  have hfun : uncurry δ = uncurry fun t s => dn t (s / P t) := by
    funext z; exact hdelta z.1 z.2
  rw [hfun]
  exact hcomp

/-- **The `C²` comparison of the two marked selected inverses, with the
regularity of the selected steering angle produced rather than assumed.**  The
hypotheses are those of `SelInvPathAngleC2.dist_selInv_le_of_path_angle_C2` with
the joint `C⁴` regularity of the steering angle removed: it follows from the
data already present, by the smooth dependence of the selected steering angle on
the front in the normalized parameter. -/
theorem dist_selInv_le_of_path_steering_C2 {p q : Data} (Γ : NormalPath p q)
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
    (hXC6 : ContDiff ℝ (6 : ℕ) (uncurry Γ.X))
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hspeed : ∀ t u, ‖(pathVel Γ.X) t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) ((pathVel Γ.X) t u) * (pathAcc Γ.X) t u).im / P t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / (P t : ℂ)))
    (hdelta : ∀ t s, δ t s = dn t (s / P t))
    (hKeq : ∀ t s, curvOfPath (pathVel Γ.X) (pathAcc Γ.X) P t s = Kn t (s / P t))
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
    (hslit : ∀ t, pathVel Γ.X t 0 ∈ Complex.slitPlane)
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
    (hkappa1 : rearKappa1 kh ≤ khat)
    (hRbd : ∀ t x,
      |frameTangential (rearOwnVelocity Γ.X (pathVel Γ.X) (pathAcc Γ.X) P δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath (pathVel Γ.X) (pathAcc Γ.X) P) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t x| ≤ Rb t)
    (hRbm : ∀ t, Rb t ≤ rr * Γ.m t) (hr : 0 ≤ rr)
    -- the parameter derivative of the normal speed of the path
    (hetaC1 : ∀ t, ContDiff ℝ (1 : ℕ) (Γ.eta t))
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
          (-frameTangential (rearOwnVelocity Γ.X (pathVel Γ.X) (pathAcc Γ.X) P δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath (pathVel Γ.X) (pathAcc Γ.X) P) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t (Phi t u)) t) ∧
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
                    (jacobiSourceConst kh P0) * cost Γ)     := by
  have hδC4 : ContDiff ℝ (4 : ℕ) (uncurry δ) :=
    contDiff_four_delta_of_normalized hP0 hkh0 hkh1 hPl hPu hdelta hsol hstrip hdnper
      hKnper hKdnper hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP
      hPC4 hPdC3 hKnC3 hKdnC3
  exact dist_selInv_le_of_path_angle_C2
    Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hXC6 hPl hPu
    hspeed hXper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
    hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
    hslit hmark hevd hΘb hkbd hklip hδC4
    hkappa1 hRbd hRbm hr hetaC1 hnumA hnumK hsmall

end SelInvPathSteeringC2
