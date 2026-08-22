import Mathlib
import UnitTangentIterates.SelInvFrontChangeVarBaseC2
import UnitTangentIterates.SelInvFrontClosingFundamentalDriftC2

/-!
# The `C²` estimate with the closing relation of the selected rears proved

`SelInvFrontChangeVarBaseC2.dist_selInv_le_of_front_changevar_base_C2` still asks that
the normal component of the velocity of the family of selected rears be
periodic in the rear arclength.  It is: each slice of the family closes up with
the rear period `Q t = ∫₀^{P t} cos δ(t, ·)`, because the front closes up with
period `P t` and its tangent angle increases by `2π` there, and differentiating
that closing relation in the time — the closing relations of the gauge — shows
that the normal component of the velocity takes the same value at the two ends
of a period, while the tangential component drops by `Q'(t)`.

This is the base-point form: besides the drift bound, the vanishing of the
tangential drift of the selected rears at the marked point is discharged too,
from the marked point of the path being at rest, `∀ t, Γ.eta t 0 = 0`.

Main result: `dist_selInv_le_of_front_closing_base_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvFrontClosingBaseC2

open SelInvFrontClosingFundamentalDriftC2

open SelInvFrontClosingFundamentalC2

open SelInvFrontClosingC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed GaugeFlowVariableSpeedPath GaugeFlowDerivCost
  GaugeMarkedDataOfRearFamily GaugeFlowUniqueness FlowDerivative
  GaugeFlowTimeDerivative GaugeFlowSupJacobi SelInvFrontCostC2 RearJacobiSourceCost
  SelInvFrontSourceC2 SelInvFrontStripC2 SelInvFrontMotionC2 SelInvFrontMixedC2
  SelInvFrontJacobiC2 SelInvFrontVelocityC2 SelInvFrontRegularityC2
  SelInvFrontChangeVarC2 RearOwnTangential

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The `C²` comparison of the two marked selected inverses, with the closing
relation of the family of selected rears proved rather than assumed.**  The
hypotheses are those of
`SelInvFrontChangeVarBaseC2.dist_selInv_le_of_front_changevar_base_C2` with the
periodicity of the normal velocity of the rears removed. -/
theorem dist_selInv_le_of_front_closing_base_C2 {p q : Data} (Γ : NormalPath p q)
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
    (hmark : ∀ t, Γ.eta t 0 = 0)
    -- the tangent-angle lift of the terminal marked selected inverse
    {kb kL : ℝ} {Θb kb' : ℝ → ℝ}
    (hevd : ∀ s, HasDerivAt (ev (SelectedInverseMap.selInv kh q))
      (Complex.exp (Complex.I * (Θb s : ℂ))) s)
    (hΘb : ∀ s, HasDerivAt Θb (kb' s) s) (hkbd : ∀ s, |kb' s| ≤ kb)
    (hklip : ∀ s t, |kb' s - kb' t| ≤ kL * |s - t|)
    -- the motion of the family of selected rears, in its own arclength
    {Pv0 khat : ℝ}
    (hδC4 : ContDiff ℝ (4 : ℕ) (uncurry δ))
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
          (-frameTangential (rearOwnVelocity Γ.X V A P δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) (rearOwnAngle (angleOfPath V A P) δ (SelInvFrontChangeVarC2.rearArclengthInv δ)) t (Phi t u)) t) ∧
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
                    (jacobiSourceConst kh P0) * cost Γ)   := by
  classical
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hslice : ∀ t, Function.Periodic (δ t) (P t) ∧
      (∀ s, HasDerivAt (δ t) (curvOfPath V A P t s - Real.sin (δ t s)) s) ∧
      (∀ s, δ t s ∈ Icc (0 : ℝ) (Real.arcsin kh)) := fun t =>
    SelectedInverseRearOwnTerminal.delta_slice_of_normalized (t := t) (hPpos t) hdelta
      hKeq hsol hstrip hdnper
  have hdper : ∀ t, Function.Periodic (δ t) (P t) := fun t => (hslice t).1
  have hsteer : ∀ t s, HasDerivAt (δ t) (curvOfPath V A P t s - Real.sin (δ t s)) s :=
    fun t => (hslice t).2.1
  have hstrip0 : ∀ t s, 0 ≤ δ t s := fun t s => ((hslice t).2.2 s).1
  have hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh := fun t s => ((hslice t).2.2 s).2
  have hcospos : ∀ t s, 0 < Real.cos (δ t s) := by
    intro t s
    obtain ⟨-, hcge, hgpos, -⟩ := strip_bounds hkh0 hkh1 (hstrip0 t s) (hstrip1 t s)
    exact lt_of_lt_of_le hgpos hcge
  have hdC1 : ContDiff ℝ (1 : ℕ) (uncurry δ) := hδC4.of_le (by norm_num)
  have hdcU : Continuous (uncurry δ) := hdC1.continuous
  have hdc : ∀ t, Continuous (δ t) := fun t =>
    hdcU.comp (continuous_const.prodMk continuous_id)
  have hFc1 : ContDiff ℝ (1 : ℕ) (uncurry (frontOfPath Γ.X P)) := hFc4.of_le (by norm_num)
  have hThc1 : ContDiff ℝ (1 : ℕ) (uncurry (angleOfPath V A P)) := hΘc4.of_le (by norm_num)
  set sfI : ℝ → ℝ → ℝ := rearArclengthInv δ with hsfIdef
  have hsfinv : ∀ t x, rearArclength (δ t) (sfI t x) = x :=
    rearArclength_rearArclengthInv hkh0 hkh1 hdc hstrip0 hstrip1
  have hsfC4 : ContDiff ℝ (4 : ℕ) (uncurry sfI) := by
    have h := contDiff_sf (n := 3) (kh := kh) hkh0 hkh1 (by exact_mod_cast hδC4)
      hstrip0 hstrip1 hsfinv
    exact_mod_cast h
  have hsfC : ContDiff ℝ (1 : ℕ) (uncurry sfI) := hsfC4.of_le (by norm_num)
  ------------------------------------------------------------------
  -- the space derivative of the family is its unit tangent
  ------------------------------------------------------------------
  have hVdiff : ∀ t, Differentiable ℝ (V t) := fun t u => (hA t u).differentiableAt
  have hVcont : ∀ t, Continuous (V t) := fun t => (hVdiff t).continuous
  have hFtangent : ∀ t s, HasDerivAt (frontOfPath Γ.X P t)
      (Complex.exp (Complex.I * (angleOfPath V A P t s : ℂ))) s := by
    intro t s
    rw [exp_angleOfPath (hA t) (hAcont t) (hVcont t) (hspeed t) (hPpos t) s]
    exact hasDerivAt_frontOfPath_tangent (hV t) (hPpos t) s
  have hcurvcont : ∀ t, Continuous (curvOfPath V A P t) := fun t =>
    continuous_curvOfPath (hVcont t) (hAcont t)
  have hThd : ∀ t s, HasDerivAt (angleOfPath V A P t) (curvOfPath V A P t s) s :=
    fun t s => hasDerivAt_angleOfPath (hcurvcont t) s
  have hsfx : ∀ t x, HasDerivAt (sfI t) (1 / Real.cos (δ t (sfI t x))) x :=
    SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hdcU hstrip0 hstrip1 hsfinv
  have hYx : ∀ t x, HasDerivAt
      (rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sfI t)
      (rearOwnTangent (angleOfPath V A P) δ sfI t x) x :=
    hasDerivAt_rearOwn_space hFtangent hThd hsteer hsfx
      (fun t s => ne_of_gt (hcospos t s))
  ------------------------------------------------------------------
  -- the parameter derivative of the family, in the moving frame
  ------------------------------------------------------------------
  have hYC : ContDiff ℝ (1 : ℕ)
      (uncurry (rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sfI)) :=
    contDiff_rearOwn_one hFc1 hThc1 hdC1 hsfC
  have hYt : ∀ t x, HasDerivAt
      (fun r => rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sfI r x)
      (rearOwnVelocity Γ.X V A P δ sfI t x) t :=
    hasDerivAt_rearOwnVelocity hFc1 hThc1 hdC1 hsfC
  have hYtframe : ∀ t x, HasDerivAt
      (fun r => rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sfI r x)
      ((frameTangential (rearOwnVelocity Γ.X V A P δ sfI)
            (rearOwnAngle (angleOfPath V A P) δ sfI) t x : ℂ)
          * rearOwnTangent (angleOfPath V A P) δ sfI t x
        + (frameNormal (rearOwnVelocity Γ.X V A P δ sfI)
            (rearOwnAngle (angleOfPath V A P) δ sfI) t x : ℂ)
          * (Complex.I * rearOwnTangent (angleOfPath V A P) δ sfI t x)) t := by
    intro t x
    have hrec := frame_reconstruct (rearOwnVelocity Γ.X V A P δ sfI t x)
      (rearOwnAngle (angleOfPath V A P) δ sfI t x)
    have heq : (frameTangential (rearOwnVelocity Γ.X V A P δ sfI)
            (rearOwnAngle (angleOfPath V A P) δ sfI) t x : ℂ)
          * rearOwnTangent (angleOfPath V A P) δ sfI t x
        + (frameNormal (rearOwnVelocity Γ.X V A P δ sfI)
            (rearOwnAngle (angleOfPath V A P) δ sfI) t x : ℂ)
          * (Complex.I * rearOwnTangent (angleOfPath V A P) δ sfI t x)
        = rearOwnVelocity Γ.X V A P δ sfI t x := by
      rw [← hrec]
      simp only [rearOwnTangent, frameTangential, frameNormal]
      ring
    rw [heq]
    exact hYt t x
  have htau0 : ∀ t x, rearOwnTangent (angleOfPath V A P) δ sfI t x ≠ 0 := by
    intro t x h
    have hn := norm_rearOwn_tangent (Θ := angleOfPath V A P) (δ := δ) (sf := sfI) t x
    rw [h] at hn
    simp at hn
  ------------------------------------------------------------------
  -- the closing relation of the family, and its derivative
  ------------------------------------------------------------------
  have hThper : ∀ t s,
      angleOfPath V A P t (s + P t) = angleOfPath V A P t s + 2 * Real.pi :=
    fun t s => angleOfPath_add_period (hVper t) (hAper t) (hVcont t) (hAcont t)
      (hPpos t) (hturn t) s
  have hangshift : ∀ t x,
      rearOwnAngle (angleOfPath V A P) δ sfI t (x + rearArclength (δ t) (P t))
        = rearOwnAngle (angleOfPath V A P) δ sfI t x + 2 * Real.pi := fun t x =>
    RearOwnPathDistFrame.rearOwnAngle_shift (kh := kh) (P := P) hkh0 hkh1 hdc hstrip0
      hstrip1 hdper hsfinv hThper t x
  have htauper : ∀ t, Function.Periodic (rearOwnTangent (angleOfPath V A P) δ sfI t)
      (rearArclength (δ t) (P t)) := by
    intro t x
    have h2pi : Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I by
        push_cast; ring]
      exact Complex.exp_two_pi_mul_I
    simp only [rearOwnTangent, hangshift t x]
    push_cast
    rw [show Complex.I * ((rearOwnAngle (angleOfPath V A P) δ sfI t x : ℂ)
          + 2 * (Real.pi : ℂ))
        = Complex.I * (rearOwnAngle (angleOfPath V A P) δ sfI t x : ℂ)
          + Complex.I * ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.exp_add, h2pi, mul_one]
  have hFper : ∀ t s, frontOfPath Γ.X P t (s + P t) = frontOfPath Γ.X P t s :=
    fun t s => periodic_frontOfPath (hXper t) (hPpos t) s
  have hclose : ∀ t x,
      rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sfI t
          (x + rearArclength (δ t) (P t))
        = rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sfI t x :=
    rearOwn_closing hkh0 hkh1 hdc hstrip0 hstrip1 hdper hsfinv hFper hThper
  have hAfam : ContDiff ℝ (4 : ℕ) (uncurry fun t s => rearArclength (δ t) s) :=
    contDiff_rearArclengthFamily hδC4
  have hAfamd : Differentiable ℝ (uncurry fun t s => rearArclength (δ t) s) :=
    hAfam.differentiable (by norm_num)
  have hPdiff : Differentiable ℝ P := hPC4.differentiable (by norm_num)
  obtain ⟨Qf, hQd⟩ : ∃ Q' : ℝ → ℝ,
      ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Q' t) t :=
    ⟨fun t => partialTime (fun t s => rearArclength (δ t) s) t (P t)
        + deriv P t • partialArc (fun t s => rearArclength (δ t) s) t (P t),
      fun t => SelInvFrontJacobiC2.hasDerivAt_comp_partials hAfamd ((hPdiff t).hasDerivAt)⟩
  have hper : ∀ t, Function.Periodic
      (frameNormal (rearOwnVelocity Γ.X V A P δ sfI)
        (rearOwnAngle (angleOfPath V A P) δ sfI) t)
      (rearArclength (δ t) (P t)) := by
    intro t x
    exact (GaugeClosingRelations.closing_relations hYC hYx hYtframe htau0 htauper hclose
      hQd t x).2
  exact SelInvFrontChangeVarBaseC2.dist_selInv_le_of_front_changevar_base_C2
    Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont
    hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
    hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
    hFc4 hΘc4 hmark hevd hΘb hkbd hklip hδC4 hper
    hkappa1 hetaU hetaUbd hnumA hnumK hsmall

end SelInvFrontClosingBaseC2
