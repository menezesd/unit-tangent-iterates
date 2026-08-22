import Mathlib
import UnitTangentIterates.SelInvFrontMixedFundamentalC2
import UnitTangentIterates.SelInvFrontJacobiC2

/-!
# The `C²` estimate with the inverse Jacobi ODE discharged

`SelInvFrontMixedFundamentalC2.dist_selInv_le_of_front_mixed_fundamental_C2` still assumes the inverse
Jacobi ODE

`∂ₓη = sec δ · η_F ∘ sf − η`

for the normal velocity of the family of selected rears, together with the
identification of the normal velocity `η_F` of the fronts with the normal speed
of the path.  Both are consequences of the data of the path, once the selected
steering angle is jointly `C²` — the only strengthening this file makes to the
hypotheses, in exchange for the removal of the ODE, of the front normal velocity
and of its link with the path.

The argument is the paper's *Smooth dependence of the selected rear* as
formalized in `RearOwnMotion.hasDerivAt_rearOwn_normal_jacobi_of_smoothDependence`:
the front, its tangent angle and the steering angle are differentiable in the
path parameter (all three are jointly `Cⁿ`), the family of rear tracks moves
with the corresponding `trackVelocity` plus the tangential sliding of the change
of variable, and the tangential sliding does not change the normal component.
The front normal velocity produced by that lemma is identified with the normal
speed of the path: writing `X t u = F(t, P t · u)` and differentiating in the
time, the parameter derivative of the front is `η ν` minus a multiple of the
unit tangent, and the tangential term drops out of the normal component.

Main results:

* `hasDerivAt_comp_partials` — the chain rule for `t ↦ f(t, g t)` in terms of
  the two partial derivatives of `f`;
* `dist_selInv_le_of_front_jacobi_fundamental_C2` — the estimate with the inverse Jacobi
  ODE, the front normal velocity and its link with the path all removed.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvFrontJacobiFundamentalC2

open SelInvFrontJacobiC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed GaugeFlowVariableSpeedPath GaugeFlowDerivCost
  GaugeMarkedDataOfRearFamily GaugeFlowUniqueness FlowDerivative
  GaugeFlowTimeDerivative GaugeFlowSupJacobi SelInvFrontCostC2 RearJacobiSourceCost
  SelInvFrontSourceC2 SelInvFrontStripC2 SelInvFrontMotionC2 SelInvFrontMixedC2
  RearOwnTangential

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

theorem dist_selInv_le_of_front_jacobi_fundamental_C2 {p q : Data} (Γ : NormalPath p q)
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
    {Ydot : ℝ → ℝ → ℂ} {Rb : ℝ → ℝ}
    {Pv0 khat rr : ℝ}
    (hYt : ∀ t x, HasDerivAt
      (fun r => rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf r x) (Ydot t x) t)
    (hδC2 : ContDiff ℝ (2 : ℕ) (uncurry δ)) (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hYdotC : ContDiff ℝ (3 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (3 : ℕ)
      (uncurry (rearOwnAngle (angleOfPath V A P) δ sf)))
    (hkC1 : ContDiff ℝ 1 (uncurry fun t x => Real.tan (δ t (sf t x))))
    (hper : ∀ t, Function.Periodic
      (frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t)
      (rearArclength (δ t) (P t)))
    (hkappa1 : rearKappa1 kh ≤ khat)
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (rearArclength (δ t) (P t)),
      |frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x| ≤ Rb t)
    (hRbm : ∀ t, Rb t ≤ rr * Γ.m t) (hr : 0 ≤ rr)
    (hxi0 : ∀ t, frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t 0 = 0)
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
  have hδC : ContDiff ℝ 1 (uncurry δ) := hδC2.of_le (by norm_num)
  have hδcont : Continuous (uncurry δ) := hδC.continuous
  have hsfspace : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x :=
    fun t x => SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hδcont hstrip0 hstrip1
      hsfinv t x
  have hcospos : ∀ t s, 0 < Real.cos (δ t s) := by
    intro t s
    obtain ⟨-, hcge, hgpos, -⟩ := strip_bounds hkh0 hkh1 (hstrip0 t s) (hstrip1 t s)
    exact lt_of_lt_of_le hgpos hcge
  have hcosne : ∀ t s, Real.cos (δ t s) ≠ 0 := fun t s => ne_of_gt (hcospos t s)
  have hcurvcont : ∀ t, Continuous (curvOfPath V A P t) := by
    intro t
    have heq : curvOfPath V A P t = fun s => Kn t (s / P t) := by
      funext s; exact hKeq t s
    rw [heq]
    exact (hKnC3.continuous.comp (continuous_const.prodMk
      (continuous_id.div_const (P t)))).congr fun s => rfl
  have hΘd : ∀ t s, HasDerivAt (angleOfPath V A P t) (curvOfPath V A P t s) s :=
    fun t s => hasDerivAt_angleOfPath (hcurvcont t) s
  have hVdiff : ∀ t, Differentiable ℝ (V t) := fun t u => (hA t u).differentiableAt
  have hVcont : ∀ t, Continuous (V t) := fun t => (hVdiff t).continuous
  have hFtangent : ∀ t s, HasDerivAt (frontOfPath Γ.X P t)
      (Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ))) s := by
    intro t s
    rw [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s]
    exact hasDerivAt_frontOfPath_tangent (hV t) (hPpos t) s
  ------------------------------------------------------------------
  -- the front data is differentiable in the pair
  ------------------------------------------------------------------
  have hFdiff : Differentiable ℝ (uncurry (frontOfPath Γ.X P)) :=
    hFc4.differentiable (by norm_num)
  have hΘdiff : Differentiable ℝ (uncurry (angleOfPath V A P)) :=
    hΘc4.differentiable (by norm_num)
  have hδdiff : Differentiable ℝ (uncurry δ) := hδC.differentiable (by norm_num)
  have hsfdiff : Differentiable ℝ (uncurry sf) := hsfC.differentiable (by norm_num)
  have hFarc : ∀ t s, partialArc (frontOfPath Γ.X P) t s
      = Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ)) :=
    fun t s => (hasDerivAt_partialArc hFdiff t s).unique (hFtangent t s)
  ------------------------------------------------------------------
  -- the parameter derivative of the fronts, from the normal gauge
  ------------------------------------------------------------------
  have hPdiff : ∀ t, HasDerivAt P (deriv P t) t :=
    fun t => (hPC4.differentiable (by norm_num) t).hasDerivAt
  have hXfront : ∀ t u, frontOfPath Γ.X P t (P t * u) = Γ.X t u := by
    intro t u
    simp [frontOfPath, mul_div_cancel_left₀ _ (ne_of_gt (hPpos t))]
  have hVexp : ∀ t s, V t (s / P t)
      = (P t : ℂ) * Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ)) := by
    intro t s
    rw [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s, tangentOfPath]
    have hPne : ((P t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hPpos t))
    field_simp
  have hFdotval : ∀ t u, partialTime (frontOfPath Γ.X P) t (P t * u)
      = (Γ.eta t u : ℂ) * Γ.nu t u
        - ((deriv P t * u : ℝ) : ℂ)
          * Complex.exp (Complex.I * (angleOfPath V A P t (P t * u) : ℂ)) := by
    intro t u
    have hg : HasDerivAt (fun r => P r * u) (deriv P t * u) t := (hPdiff t).mul_const u
    have h := hasDerivAt_comp_partials hFdiff hg
    have hfun : (fun r => frontOfPath Γ.X P r (P r * u)) = fun r => Γ.X r u :=
      funext fun r => hXfront r u
    rw [hfun, hFarc t (P t * u)] at h
    have huniq := h.unique (Γ.hasDerivAt_time t u)
    rw [Complex.real_smul] at huniq
    rw [← huniq]
    ring
  have hnormalvel : ∀ t s,
      frontNormalVelocityAt (partialTime (frontOfPath Γ.X P)) (angleOfPath V A P) δ t s
        = Γ.eta t (s / P t) := by
    intro t s
    have hs : P t * (s / P t) = s := mul_div_cancel₀ s (ne_of_gt (hPpos t))
    have hF := hFdotval t (s / P t)
    rw [hs] at hF
    have hnuval : Γ.nu t (s / P t)
        = Complex.I * Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ)) := by
      rw [hnu t (s / P t), hVexp t s]
      have hPne : ((P t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hPpos t))
      field_simp
    have hang : rearAngle (angleOfPath V A P t) (δ t) s + δ t s = angleOfPath V A P t s := by
      simp [rearAngle]
    simp only [frontNormalVelocityAt, frontNormalVelocity, hang, hF, hnuval]
    set E := Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ)) with hE
    have hEE : E * (starRingEnd ℂ) E = 1 := RearSmoothDependence.exp_mul_conj _
    have hval : ((Γ.eta t (s / P t) : ℂ) * (Complex.I * E)
          - ((deriv P t * (s / P t) : ℝ) : ℂ) * E) * (starRingEnd ℂ) (Complex.I * E)
        = ((Γ.eta t (s / P t) : ℝ) : ℂ)
          + ((deriv P t * (s / P t) : ℝ) : ℂ) * Complex.I := by
      rw [map_mul, Complex.conj_I]
      linear_combination (-((Γ.eta t (s / P t) : ℝ) : ℂ) * Complex.I ^ 2
          + ((deriv P t * (s / P t) : ℝ) : ℂ) * Complex.I) * hEE
        + (-((Γ.eta t (s / P t) : ℝ) : ℂ)) * Complex.I_sq
    rw [hval]
    simp
  ------------------------------------------------------------------
  -- the smooth dependence data of the front
  ------------------------------------------------------------------
  have hFa : ∀ t s, HasDerivAt (fun r => frontOfPath Γ.X P r s)
      (partialTime (frontOfPath Γ.X P) t s) t := hasDerivAt_partialTime hFdiff
  have hΘa : ∀ t s, HasDerivAt (fun r => angleOfPath V A P r s)
      (partialTime (angleOfPath V A P) t s) t := hasDerivAt_partialTime hΘdiff
  have hδa : ∀ t s, HasDerivAt (fun r => δ r s) (partialTime δ t s) t :=
    hasDerivAt_partialTime hδdiff
  have hFdotC : ContDiff ℝ (3 : ℕ) (uncurry (partialTime (frontOfPath Γ.X P))) :=
    contDiff_partialTime_self (n := 3) (by exact_mod_cast hFc4)
  have hΘdotC : ContDiff ℝ (3 : ℕ) (uncurry (partialTime (angleOfPath V A P))) :=
    contDiff_partialTime_self (n := 3) (by exact_mod_cast hΘc4)
  have hwC : ContDiff ℝ (1 : ℕ) (uncurry (partialTime δ)) :=
    contDiff_partialTime_self (n := 1) (by exact_mod_cast hδC2)
  have hFdots : ∀ t s, HasDerivAt (partialTime (frontOfPath Γ.X P) t)
      (partialArc (partialTime (frontOfPath Γ.X P)) t s) s :=
    hasDerivAt_partialArc (hFdotC.differentiable (by norm_num))
  have hΘdots : ∀ t s, HasDerivAt (partialTime (angleOfPath V A P) t)
      (partialArc (partialTime (angleOfPath V A P)) t s) s :=
    hasDerivAt_partialArc (hΘdotC.differentiable (by norm_num))
  have hws : ∀ t s, HasDerivAt (partialTime δ t) (partialArc (partialTime δ) t s) s :=
    hasDerivAt_partialArc (hwC.differentiable (by norm_num))
  have hFc2 : ContDiff ℝ (2 : ℕ) (uncurry (frontOfPath Γ.X P)) := hFc4.of_le (by norm_num)
  have hΘc2 : ContDiff ℝ (2 : ℕ) (uncurry (angleOfPath V A P)) := hΘc4.of_le (by norm_num)
  ------------------------------------------------------------------
  -- the velocity of the family of rear tracks
  ------------------------------------------------------------------
  have hGC1 : ContDiff ℝ (1 : ℕ)
      (uncurry (frontParamTrack (frontOfPath Γ.X P) (angleOfPath V A P) δ)) := by
    have h1 : ContDiff ℝ (1 : ℕ) (uncurry (frontOfPath Γ.X P)) := hFc4.of_le (by norm_num)
    have h2 : ContDiff ℝ (1 : ℕ) (uncurry fun t s => angleOfPath V A P t s - δ t s) := by
      simpa [Function.uncurry] using (hΘc4.of_le (by norm_num : ((1 : ℕ) : WithTop ℕ∞)
        ≤ ((4 : ℕ) : WithTop ℕ∞))).sub hδC
    have h3 := contDiff_expI (n := 1) h2
    have heq : uncurry (frontParamTrack (frontOfPath Γ.X P) (angleOfPath V A P) δ)
        = fun p : ℝ × ℝ => uncurry (frontOfPath Γ.X P) p
          - Complex.exp (Complex.I *
            ((uncurry (fun t s => angleOfPath V A P t s - δ t s) p : ℝ) : ℂ)) := rfl
    rw [heq]
    exact h1.sub h3
  have hGdiff : Differentiable ℝ
      (uncurry (frontParamTrack (frontOfPath Γ.X P) (angleOfPath V A P) δ)) :=
    hGC1.differentiable (by norm_num)
  have hGtime : ∀ t s,
      partialTime (frontParamTrack (frontOfPath Γ.X P) (angleOfPath V A P) δ) t s
        = trackVelocity (partialTime (frontOfPath Γ.X P))
            (partialTime (angleOfPath V A P)) (partialTime δ) (angleOfPath V A P) δ t s :=
    fun t s => (hasDerivAt_partialTime hGdiff t s).unique
      (hasDerivAt_frontParamTrack_time hFa hΘa hδa t s)
  have hGarc : ∀ t s,
      partialArc (frontParamTrack (frontOfPath Γ.X P) (angleOfPath V A P) δ) t s
        = (Real.cos (δ t s) : ℂ)
          * Complex.exp (Complex.I * (rearAngle (angleOfPath V A P t) (δ t) s : ℂ)) :=
    fun t s => (hasDerivAt_partialArc hGdiff t s).unique
      (hasDerivAt_rearTrack (K := curvOfPath V A P t) (hFtangent t s) (hΘd t s) (hsteer t s))
  have hlinkY : ∀ t x, Ydot t x
      = trackVelocity (partialTime (frontOfPath Γ.X P))
          (partialTime (angleOfPath V A P)) (partialTime δ) (angleOfPath V A P) δ t (sf t x)
        + (partialTime sf t x) • ((Real.cos (δ t (sf t x)) : ℂ)
          * Complex.exp (Complex.I *
            (rearAngle (angleOfPath V A P t) (δ t) (sf t x) : ℂ))) := by
    intro t x
    have hg : HasDerivAt (fun r => sf r x) (partialTime sf t x) t :=
      hasDerivAt_partialTime hsfdiff t x
    have h := hasDerivAt_comp_partials hGdiff hg
    rw [hGtime, hGarc] at h
    exact (hYt t x).unique h
  ------------------------------------------------------------------
  -- the inverse Jacobi ODE for the normal velocity of the rears
  ------------------------------------------------------------------
  have hjac : ∀ t x, HasDerivAt
      (fun x' => frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x')
      ((fun t' s => Γ.eta t' (s / P t')) t (sf t x) / Real.cos (δ t (sf t x))
        - frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t x) x := by
    intro t x
    have h := RearOwnMotion.hasDerivAt_rearOwn_normal_jacobi_of_smoothDependence
      (F := frontOfPath Γ.X P) (Θ := angleOfPath V A P) (δ := δ) (sf := sf)
      (K := curvOfPath V A P) (Fdot := partialTime (frontOfPath Γ.X P))
      (Θdot := partialTime (angleOfPath V A P)) (w := partialTime δ)
      (Fdots := partialArc (partialTime (frontOfPath Γ.X P)))
      (Θdots := partialArc (partialTime (angleOfPath V A P)))
      (ws := partialArc (partialTime δ))
      (sft := partialTime sf) (Ydot := Ydot)
      hFtangent hΘd hsteer hsfspace hcosne hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδC2
      hlinkY t x
    rwa [hnormalvel t (sf t x)] at h
  have hlink : ∀ t u, Γ.eta t u = (fun t' s => Γ.eta t' (s / P t')) t (P t * u) := by
    intro t u
    simp [mul_div_cancel_left₀ _ (ne_of_gt (hPpos t))]
  exact SelInvFrontMixedFundamentalC2.dist_selInv_le_of_front_mixed_fundamental_C2 (etaF := fun t' s => Γ.eta t' (s / P t'))
    Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont
    hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
    hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
    hFc4 hΘc4 hsfinv hmark hevd hΘb hkbd hklip hYt hδC hsfC hYdotC hangC hkC1 hper hjac
    hlink hkappa1 hRbd hRbm hr hxi0 hetaU hetaUbd hnumA hnumK hsmall

end SelInvFrontJacobiFundamentalC2
