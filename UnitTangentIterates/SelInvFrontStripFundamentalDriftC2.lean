import Mathlib
import UnitTangentIterates.SelInvFrontDriftFundamentalC2
import UnitTangentIterates.SelInvFrontStripFundamentalC2

/-!
# The `C²` estimate with the strip data of the selected rears discharged

`SelInvFrontSourceFundamentalDriftC2.dist_selInv_le_of_front_source_fundamental_drift_C2`
still asks the caller for three pieces of data attached to the family of
selected rears which are in fact determined by the front:

* the arclength derivative `gS` of the source `η_F(sf x)/cos δ(sf x)` of the
  inverse Jacobi ODE — it exists, since `η_F`, `δ` and the change of variable
  `sf` are all differentiable and `cos δ` does not vanish on the selected
  strip;
* a bound `Kx` for the quantity `(K − sin δ)/cos³δ` and a uniform bound `kx`
  for it along the path — the bounds of the selected strip give the explicit
  constant

  `stripCurvConst κ̂ = 2κ̂/(1−κ̂²)^{3/2}` ;

* the joint continuity of that quantity — a consequence of the joint
  regularity already assumed for the curvature of the fronts, for the steering
  angle and for the change of variable, since `cos δ ≥ √(1−κ̂²) > 0`.

This file discharges all three, so that nothing about the strip curvature or
about the source of the inverse Jacobi ODE is left to the caller: the only
numerical condition that mentions them is `hnumK`, now written with the
explicit constants `jacobiSourceConst κ̂ P₀` and `stripCurvConst κ̂`.

This is the fundamental-domain form, with the drift bound discharged: the
tangential drift of the family of selected rears is controlled over one rear
period by `P₁·κ̂/(1−κ̂²)` times the normal speed of the path, so no bound on it
is left to the caller.

Main result: `dist_selInv_le_of_front_strip_fundamental_drift_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvFrontStripFundamentalDriftC2

open SelInvFrontStripFundamentalC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed GaugeFlowVariableSpeedPath GaugeFlowDerivCost
  GaugeMarkedDataOfRearFamily GaugeFlowUniqueness FlowDerivative
  GaugeFlowTimeDerivative GaugeFlowSupJacobi SelInvFrontCostC2 RearJacobiSourceCost
  SelInvFrontSourceC2 RearOwnTangential SelInvFrontStripC2

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, with the strip
data of the family of selected rears produced from the front data.**

The hypotheses are those of
`SelInvFrontDriftFundamentalDriftC2.dist_selInv_le_of_front_drift_fundamental_drift_C2`, with the derivative of
the source of the inverse Jacobi ODE, the bound on `(K − sin δ)/cos³δ` and its
continuity all removed; the constant of the estimate is the same, with
`stripCurvConst κ̂` in place of the bound the caller used to supply. -/
theorem dist_selInv_le_of_front_strip_fundamental_drift_C2 {p q : Data} (Γ : NormalPath p q)
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
    (hxi0 : ∀ t,
      frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t 0 = 0)
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
  have hK : ∀ t s, |curvOfPath V A P t s| ≤ kh := by
    intro t s
    rw [hKeq t s]
    exact hKnbd t _
  have hδcont : Continuous (uncurry δ) := hδC.continuous
  have hsfcont : Continuous (uncurry sf) := hsfC.continuous
  have hsfspace : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x :=
    fun t x => SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hδcont hstrip0 hstrip1
      hsfinv t x
  have hcospos : ∀ t s, 0 < Real.cos (δ t s) := by
    intro t s
    obtain ⟨-, hcge, hgpos, -⟩ := strip_bounds hkh0 hkh1 (hstrip0 t s) (hstrip1 t s)
    exact lt_of_lt_of_le hgpos hcge
  ------------------------------------------------------------------
  -- the front normal velocity in the arclength of the front
  ------------------------------------------------------------------
  have hetaFeq : ∀ t, etaF t = fun s => Γ.eta t (s / P t) := by
    intro t
    funext s
    rw [hlink t (s / P t), mul_div_cancel₀ s (ne_of_gt (hPpos t))]
  have hetaFD : ∀ t s, HasDerivAt (etaF t) (etaU t (s / P t) / P t) s := by
    intro t s
    rw [hetaFeq t]
    have hinner : HasDerivAt (fun x : ℝ => x / P t) (1 / P t) s := by
      simpa using (hasDerivAt_id s).div_const (P t)
    simpa [div_eq_mul_inv, mul_comm] using (hetaU t (s / P t)).comp s hinner
  ------------------------------------------------------------------
  -- the derivative of the source of the inverse Jacobi ODE exists
  ------------------------------------------------------------------
  have hgSex : ∀ t x, HasDerivAt
      (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x')))
      (deriv (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x'))) x) x := by
    intro t x
    have h1 : HasDerivAt (fun x' => etaF t (sf t x'))
        (etaU t (sf t x / P t) / P t * (1 / Real.cos (δ t (sf t x)))) x :=
      (hetaFD t (sf t x)).comp x (hsfspace t x)
    have h2 : HasDerivAt (fun x' => δ t (sf t x'))
        ((curvOfPath V A P t (sf t x) - Real.sin (δ t (sf t x)))
          * (1 / Real.cos (δ t (sf t x)))) x := (hsteer t (sf t x)).comp x (hsfspace t x)
    exact (h1.div h2.cos (ne_of_gt (hcospos t (sf t x)))).differentiableAt.hasDerivAt
  ------------------------------------------------------------------
  -- the strip bound for the arclength derivative of the rear curvature
  ------------------------------------------------------------------
  have hKxbd : ∀ t x, |(curvOfPath V A P t (sf t x) - Real.sin (δ t (sf t x)))
      / Real.cos (δ t (sf t x)) ^ 3| ≤ stripCurvConst kh := fun t x =>
    abs_curvDeriv_le_strip hkh0 hkh1 (hstrip0 t (sf t x)) (hstrip1 t (sf t x))
      (hK t (sf t x))
  ------------------------------------------------------------------
  -- and its joint continuity
  ------------------------------------------------------------------
  have hkXc : Continuous (uncurry fun t x =>
      (curvOfPath V A P t (sf t x) - Real.sin (δ t (sf t x)))
        / Real.cos (δ t (sf t x)) ^ 3) := by
    have hrw : (uncurry fun t x =>
        (curvOfPath V A P t (sf t x) - Real.sin (δ t (sf t x)))
          / Real.cos (δ t (sf t x)) ^ 3)
        = fun z : ℝ × ℝ =>
          (Kn z.1 (sf z.1 z.2 / P z.1) - Real.sin (δ z.1 (sf z.1 z.2)))
            / Real.cos (δ z.1 (sf z.1 z.2)) ^ 3 := by
      funext z
      simp [uncurry, hKeq]
    rw [hrw]
    have hPc : Continuous P := hPC4.continuous
    have hsfz : Continuous fun z : ℝ × ℝ => sf z.1 z.2 := hsfcont
    have hδz : Continuous fun z : ℝ × ℝ => δ z.1 (sf z.1 z.2) :=
      hδcont.comp (continuous_fst.prodMk hsfz)
    have hKz : Continuous fun z : ℝ × ℝ => Kn z.1 (sf z.1 z.2 / P z.1) :=
      hKnC3.continuous.comp
        (continuous_fst.prodMk (hsfz.div (hPc.comp continuous_fst)
          fun z => ne_of_gt (hPpos z.1)))
    exact (hKz.sub (Real.continuous_sin.comp hδz)).div
      ((Real.continuous_cos.comp hδz).pow 3)
      fun z => pow_ne_zero 3 (ne_of_gt (hcospos z.1 (sf z.1 z.2)))
  exact SelInvFrontDriftFundamentalC2.dist_selInv_le_of_front_drift_fundamental_C2
    (Kx := fun _ => stripCurvConst kh) (kx := stripCurvConst kh)
    (gS := fun t x => deriv (fun x' => etaF t (sf t x') / Real.cos (δ t (sf t x'))) x)
    Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont
    hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
    hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
    hFc4 hΘc4 hsfinv hmark hevd hΘb hkbd hklip hYt hδC hsfC hYdotC hangC hkC1 hper hjac
    hlink hkappa1 halphaT hkT halphaTc hkTc halphaTS hmixed hKxbd
    (fun _ => stripCurvConst_nonneg hkh0) (fun _ => le_rfl) hkXc
    hxi0 hgSex hetaU hetaUbd hnumA hnumK hsmall

end SelInvFrontStripFundamentalDriftC2
