import Mathlib
import UnitTangentIterates.SelInvFrontNormalSpeedC2

/-!
# The `C²` estimate with the velocity and the acceleration of the path produced

`SelInvFrontNormalSpeedC2.dist_selInv_le_of_front_normalSpeed_C2` still carries
the velocity and the acceleration of the moving curve in its parameter as data,
assumed to be its first two parameter derivatives, continuous and periodic, and
asks separately that the front — the arclength reparametrization of the moving
curve — be jointly `C⁴`.  For a jointly `C⁴` moving curve none of that need be
assumed: `pathVel` and `pathAcc` are the two derivatives, they are periodic
because the moving curve is (`periodic_partialArc`), and the front is the
composition of the moving curve with the smooth rescaling `s ↦ s / P t`.

Main results: `pathVel`, `pathAcc`, `periodic_partialArc`,
`contDiff_frontOfPath`, `dist_selInv_le_of_path_regularity_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvPathRegularityC2

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
  RearOwnTangential

variable {δ dn Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ} {P0 P1 kh Klip Plip : ℝ}

/-- The velocity of a moving curve in its parameter. -/
def pathVel (X : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ := partialArc X

/-- The acceleration of a moving curve in its parameter. -/
def pathAcc (X : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ := partialArc (partialArc X)

/-- **The parameter derivative of a periodic family is periodic.** -/
theorem periodic_partialArc {X : ℝ → ℝ → ℂ} {c : ℝ}
    (hX : Differentiable ℝ (uncurry X))
    (hper : ∀ t, Function.Periodic (X t) c) (t : ℝ) :
    Function.Periodic (partialArc X t) c := by
  intro u
  have h1 : HasDerivAt (X t) (partialArc X t (u + c)) (u + c) :=
    hasDerivAt_partialArc hX t (u + c)
  have hshift : HasDerivAt (fun y => X t (y + c)) (partialArc X t (u + c)) u :=
    h1.comp_add_const u c
  have hfun : (fun y => X t (y + c)) = X t := funext fun y => hper t y
  rw [hfun] at hshift
  exact hshift.unique (hasDerivAt_partialArc hX t u)

/-- **The front of a jointly `C⁴` path is jointly `C⁴`**, being the moving curve
composed with the rescaling `s ↦ s / P t`. -/
theorem contDiff_frontOfPath {X : ℝ → ℝ → ℂ} (hPpos : ∀ t, 0 < P t)
    (hX : ContDiff ℝ (4 : ℕ) (uncurry X)) (hPC : ContDiff ℝ (4 : ℕ) P) :
    ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath X P)) := by
  have hinner : ContDiff ℝ (4 : ℕ) (fun z : ℝ × ℝ => (z.1, z.2 / P z.1)) :=
    contDiff_fst.prodMk (contDiff_snd.div (hPC.comp contDiff_fst)
      (fun z => ne_of_gt (hPpos z.1)))
  exact hX.comp hinner

/-- **The `C²` comparison of the two marked selected inverses, with the velocity
and the acceleration of the moving curve produced rather than assumed.**  The
hypotheses are those of
`SelInvFrontNormalSpeedC2.dist_selInv_le_of_front_normalSpeed_C2` with the
velocity, the acceleration, their continuity and periodicity and the joint
regularity of the front all replaced by the joint `C⁴` regularity of the moving
curve. -/
theorem dist_selInv_le_of_path_regularity_C2 {p q : Data} (Γ : NormalPath p q)
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
    (hXC4 : ContDiff ℝ (4 : ℕ) (uncurry Γ.X))
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
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath (pathVel Γ.X) (pathAcc Γ.X) P)))
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
  classical
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hXdiff : Differentiable ℝ (uncurry Γ.X) := hXC4.differentiable (by norm_num)
  have hV : ∀ t u, HasDerivAt (Γ.X t) (pathVel Γ.X t u) u := hasDerivAt_partialArc hXdiff
  have hVC3 : ContDiff ℝ (3 : ℕ) (uncurry (pathVel Γ.X)) :=
    contDiff_partialArc_self (n := 3) (by exact_mod_cast hXC4)
  have hVdiff : Differentiable ℝ (uncurry (pathVel Γ.X)) := hVC3.differentiable (by norm_num)
  have hA : ∀ t u, HasDerivAt (pathVel Γ.X t) (pathAcc Γ.X t u) u :=
    hasDerivAt_partialArc hVdiff
  have hAC2 : ContDiff ℝ (2 : ℕ) (uncurry (pathAcc Γ.X)) :=
    contDiff_partialArc_self (n := 2) (by exact_mod_cast hVC3)
  have hAcont : ∀ t, Continuous (pathAcc Γ.X t) := fun t =>
    hAC2.continuous.comp (continuous_const.prodMk continuous_id)
  have hVper : ∀ t, Function.Periodic (pathVel Γ.X t) 1 := periodic_partialArc hXdiff hXper
  have hAper : ∀ t, Function.Periodic (pathAcc Γ.X t) 1 := periodic_partialArc hVdiff hVper
  have hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)) :=
    contDiff_frontOfPath hPpos hXC4 hPC4
  exact dist_selInv_le_of_front_normalSpeed_C2
    Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont
    hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
    hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
    hFc4 hΘc4 hmark hevd hΘb hkbd hklip hδC4
    hkappa1 hRbd hRbm hr hetaC1 hnumA hnumK hsmall

end SelInvPathRegularityC2
