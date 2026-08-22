import Mathlib
import UnitTangentIterates.SelInvRearFamilySupFundamentalC2
import UnitTangentIterates.SelInvFrontCostC2
import UnitTangentIterates.SelInvC2Modulus
import UnitTangentIterates.RearCostDensity

/-!
# The `C²` estimate in terms of the cost of the path of fronts alone

`SelInvRearFamilySupC2.dist_selInv_le_of_rear_family_sup_C2` bounds the marked
distance of the two selected inverses of the ends of a normal path of fronts by
a function of two costs: the cost `c = cost Γ` of the path of fronts and the
total cost `M = ∫₀^T m` of the family of selected rears, `m` being an auxiliary
cost density the caller has to provide, subject to three conditions.

`RearCostDensity.lean` chooses that density: `m = C · m_F` with
`C = rearCostConst κ̂ κ̂' κ₂ ℓ d`, so that all three conditions hold as soon as
the total cost `C · c` is at most one.  This file feeds that choice into the
estimate.  The two remaining quantitative data of the rear side — the bound `Rb`
on the tangential drift and the bound `Dd` on the source of the inverse Jacobi
ODE — are correspondingly asked to be dominated by the cost density of the
*fronts*, which is how the estimates of `RearOwnTangentialCost.lean` produce
them; the only new hypothesis is the smallness condition `C · cost Γ ≤ 1`.

The conclusion is then a bound depending on the path only through `cost Γ`, and
`selInvFrontModulus` names it: it is continuous in the cost and vanishes with
it, so the two marked selected inverses come together as the cost of the path
of fronts tends to zero.

This is the fundamental-domain form: the bound on the tangential drift is asked
on one rear period only.  The modulus itself is unchanged, and is the one of
`SelInvFrontCostC2`.

Main result: `dist_selInv_le_of_front_cost_fundamental_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvFrontCostFundamentalC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed GaugeFlowVariableSpeedPath GaugeFlowDerivCost
  GaugeMarkedDataOfRearFamily GaugeFlowUniqueness FlowDerivative
  GaugeFlowTimeDerivative GaugeFlowSupJacobi

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, in terms of the
cost of the path of fronts alone.**

The hypotheses are those of
`SelInvRearFamilySupC2.dist_selInv_le_of_rear_family_sup_C2`, except that the
cost density of the family of selected rears is no longer a datum: it is chosen
here, proportional to the cost density of the path of fronts, the constant of
proportionality being `RearCostDensity.rearCostConst`.  The two bounds `Rb` and
`Dd` on the tangential drift and on the source of the inverse Jacobi ODE are
correspondingly asked to be dominated by the cost density of the *fronts*, and
the only extra hypothesis is that the resulting total cost of the family of
rears be at most one — a smallness condition on the cost of the path.  The
bound is then a function of `cost Γ` alone. -/
theorem dist_selInv_le_of_front_cost_fundamental_C2 {p q : Data} (Γ : NormalPath p q)
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
    {Ydot : ℝ → ℝ → ℂ} {etaF alphaT kT gS : ℝ → ℝ → ℝ} {Kx Rb Dd : ℝ → ℝ}
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
    (hRbm : ∀ t, Rb t ≤ rr * Γ.m t) (hr : 0 ≤ rr)
    (hxi0 : ∀ t,
      frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t 0 = 0)
    (hgSd : ∀ t x, HasDerivAt (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x')))
      (gS t x) x)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t) (hDm : ∀ t, Dd t ≤ dd * Γ.m t)
    (hnumA : 2 + 2 * khat * rr ≤ 1 / Pv0)
    (hnumK : (dd + 2) + khat ^ 2 + 2 * rr * kx ≤ 1 / Pv0 ^ 2 + khat ^ 2)
    (hdd : 0 ≤ dd)
    -- the total cost of the family of selected rears, with the density chosen
    -- proportional to that of the fronts, is at most one
    (hsmall : RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
      (rearArclength (δ 0) (P 0)) dd * cost Γ ≤ 1) :
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
                      (rearArclength (δ 0) (P 0)) dd * cost Γ)) khat
                  (costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
                    (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                    (rearArclength (δ 0) (P 0)) dd * cost Γ))
                  (khat * costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
                      (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                    (rearArclength (δ 0) (P 0)) dd * cost Γ)
                    + rearKappa2 kh * costP1 (rearArclength (δ 0) (P 0)) khat
                      (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                    (rearArclength (δ 0) (P 0)) dd * cost Γ) ^ 2)
                * (RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
                    (rearArclength (δ 0) (P 0)) dd * cost Γ) := by
  classical
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  obtain ⟨-, hdode0, hdmem0⟩ :=
    SelectedInverseRearOwnTerminal.delta_slice_of_normalized (t := 0) (hPpos 0) hdelta
      hKeq hsol hstrip hdnper
  have hdc0 : Continuous (δ 0) :=
    Differentiable.continuous fun s => (hdode0 s).differentiableAt
  have hellpos : 0 < rearArclength (δ 0) (P 0) :=
    SelectedInverseUnique.rearArclength_pos (hPpos 0) hkh0 hkh1 hdc0 hdmem0
  set C : ℝ := RearCostDensity.rearCostConst kh khat (rearKappa2 kh)
    (rearArclength (δ 0) (P 0)) dd with hCdef
  have hkhat0 : 0 ≤ khat :=
    le_trans (rearKappa1_nonneg hkh0 hkh1) hkappa1
  have hk20 : 0 ≤ rearKappa2 kh := rearKappa2_nonneg hkh0 hkh1
  have hC1 : 1 ≤ C := RearCostDensity.rearCostConst_ge_one hkh0 hkh1
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hcost0 : 0 ≤ cost Γ :=
    intervalIntegral.integral_nonneg Γ.T_pos.le fun t _ => Γ.m_nonneg t
  have hM0 : 0 ≤ C * cost Γ := mul_nonneg hCpos.le hcost0
  have hint : (∫ t in (0:ℝ)..Γ.T, C * Γ.m t) = C * cost Γ := by
    rw [intervalIntegral.integral_const_mul]
    rfl
  ------------------------------------------------------------------
  -- the chosen cost density of the family of rears
  ------------------------------------------------------------------
  have hmc' : Continuous fun t => C * Γ.m t := continuous_const.mul Γ.cont_m
  have hm0' : ∀ t, 0 ≤ C * Γ.m t := fun t => mul_nonneg hCpos.le (Γ.m_nonneg t)
  have hmstop' : ∀ t ∉ Ioo (0 : ℝ) Γ.T, C * Γ.m t = 0 := by
    intro t ht
    rw [Γ.m_stop t ht, mul_zero]
  have hmge' : ∀ t, Γ.m t / Real.sqrt (1 - kh ^ 2) ≤ C * Γ.m t := fun t =>
    RearCostDensity.mge_of_rearCostConst (khat := khat) (kappa2 := rearKappa2 kh)
      (ell := rearArclength (δ 0) (P 0)) (dd := dd) (Γ.m_nonneg t)
  have hDd0 : ∀ t, 0 ≤ Dd t := fun t => le_trans (abs_nonneg _) (hgSbd t 0)
  have hDm' : ∀ t, Dd t ≤ dd / C * (C * Γ.m t) := by
    intro t
    have hrw : dd / C * (C * Γ.m t) = dd * Γ.m t := by
      field_simp
    rw [hrw]
    exact hDm t
  have hRbm' : ∀ t, Rb t ≤ rr / C * (C * Γ.m t) := by
    intro t
    have hrw : rr / C * (C * Γ.m t) = rr * Γ.m t := by
      field_simp
    rw [hrw]
    exact hRbm t
  have hr' : 0 ≤ rr / C := div_nonneg hr hCpos.le
  have hrle : rr / C ≤ rr := div_le_self hr hC1
  have hddle : dd / C ≤ dd := div_le_self hdd hC1
  have hkx0 : 0 ≤ kx := le_trans (hKxnn 0) (hKxm 0)
  have hnumA' : 2 + 2 * khat * (rr / C) ≤ 1 / Pv0 := by nlinarith
  have hnumK' : (dd / C + 2) + khat ^ 2 + 2 * (rr / C) * kx ≤ 1 / Pv0 ^ 2 + khat ^ 2 := by
    nlinarith
  have hsupA' : ∀ t, 2 * (Γ.m t / Real.sqrt (1 - kh ^ 2))
      * costP1 (rearArclength (δ 0) (P 0)) khat (∫ s in (0 : ℝ)..Γ.T, C * Γ.m s)
        ≤ C * Γ.m t := by
    intro t
    rw [hint]
    exact RearCostDensity.supA_of_rearCostConst (kappa2 := rearKappa2 kh) (dd := dd)
      (Γ.m_nonneg t) hellpos.le hkhat0 hsmall
  have hsupB' : ∀ t, (Dd t + 2 * (Γ.m t / Real.sqrt (1 - kh ^ 2)))
        * costP1 (rearArclength (δ 0) (P 0)) khat (∫ s in (0 : ℝ)..Γ.T, C * Γ.m s) ^ 2
      + 2 * (Γ.m t / Real.sqrt (1 - kh ^ 2))
        * costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
          (∫ s in (0 : ℝ)..Γ.T, C * Γ.m s) ≤ C * Γ.m t := by
    intro t
    rw [hint]
    exact RearCostDensity.supB_of_rearCostConst (Γ.m_nonneg t) hellpos.le hkhat0 hk20
      (hDm t) (hDd0 t) hM0 hsmall
  ------------------------------------------------------------------
  -- the estimate with that density
  ------------------------------------------------------------------
  have key :=
    SelInvRearFamilySupFundamentalC2.dist_selInv_le_of_rear_family_sup_fundamental_C2
    (m := fun t => C * Γ.m t) (rr := rr / C) (dd := dd / C)
    Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont
    hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
    hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
    hFc4 hΘc4 hsfinv hmark hevd hΘb hkbd hklip hYt hδC hsfC hYdotC hangC hkC1 hper hjac
    hlink hkappa1 halphaT hkT halphaTc hkTc halphaTS hmixed hKxbd hKxnn hKxm hkXc
    hRbd hRbm' hr' hxi0 hgSd hgSbd hDm' hmc' hm0' hmstop' hmge' hnumA' hnumK' hsupA'
    hsupB'
  simpa only [hint] using key

end SelInvFrontCostFundamentalC2
