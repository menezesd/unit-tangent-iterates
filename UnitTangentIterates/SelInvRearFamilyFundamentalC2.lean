import Mathlib
import UnitTangentIterates.SelInvMarkingDefectClosedC2
import UnitTangentIterates.GaugeRearFamilyFundamental
import UnitTangentIterates.GaugeFlowUniqueness
import UnitTangentIterates.SelInvDriftRigidity

/-!
# The last link, with the tangential drift bounded on one period only

`SelInvMarkingDefectClosedC2.dist_selInv_le_of_marking_defect_cost_C2` bounds the
marked (`C²`) distance of the two marked selected inverses of the ends of a
normal path of fronts by

```
  markingC2Bound … + c2ConstVar … · cost Γ' ,
```

for *any* normal path `Γ'` of variable-speed slices joining `selInv κ̂ p` to the
curve `q'` that reads `selInv κ̂ q` in the gauge marking `Φ` of the path.

`GaugeRearFamilyFundamental.exists_variableSpeed_normalPath_of_rearFamily_fundamental`
produces exactly such a path from the motion of the family of selected rears
carried in its own arclength — but with *its own* marking, the flow of minus the
tangential component of that motion.  It asks for the bound on that tangential
component on one rear period only, so this file too asks for it there only; the
closing of the slices, the turning of their tangent angle over one period and
the differentiability of the rear period, which it needs in exchange, are all
read off the front data of the path, with no constraint on the motion of the
rear length.

This file identifies the two markings and so removes the hypothesis.  The
identification is an ODE uniqueness statement: the marking of the first
construction is now known to solve the same flow equation
`∂_tΦ = −ξ(t, Φ)` (this is the conjunct threaded through the `…DefectC2` chain),
it starts at the same affine marking `u ↦ rearArclength (δ 0) (P 0) · u`, and the
field is globally Lipschitz in the arclength, so the two markings coincide
(`GaugeFlowUniqueness.flow_unique_of_deriv_bound`).  The two ends of the second
construction are then the two ends the first one asks for: at time `0` the
marked selected inverse `selInv κ̂ p` itself, and at time `T` the curve `q'`
that reads `selInv κ̂ q` in the marking.

The conclusion is therefore the `C²` comparison of the two marked selected
inverses with **both** terms produced from the data of the path and of the
family of rears:

```
  dist (selInv κ̂ q) (selInv κ̂ p)
      ≤ markingC2Bound … + c2ConstVar … · ∫₀^T m .
```

Main result: `dist_selInv_le_of_rear_family_fundamental_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvRearFamilyFundamentalC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed GaugeFlowVariableSpeedPath GaugeFlowDerivCost
  GaugeMarkedDataOfRearFamily GaugeFlowUniqueness

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The `C²` comparison of the two marked selected inverses of the ends of a
normal path of fronts, with the comparison path produced from the family of
selected rears and with the two markings identified.**

The first summand is the defect of the gauge marking, the second the cost of the
comparison path, which is the time integral of the cost density `m` of the
family of rears; both vanish with the cost of the path of fronts. -/
theorem dist_selInv_le_of_rear_family_fundamental_C2 {p q : Data} (Γ : NormalPath p q)
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
    (hnumK : (dd + 2) + khat ^ 2 + 2 * rr * kx ≤ 1 / Pv0 ^ 2 + khat ^ 2) :
    perim (SelectedInverseMap.selInv kh p) = rearArclength (δ 0) (P 0) ∧
      perim (SelectedInverseMap.selInv kh q) = rearArclength (δ Γ.T) (P Γ.T) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
        (∀ t, Phi t 0 = 0) ∧
        (∀ u t, HasDerivAt (fun r => Phi r u)
          (-frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t (Phi t u)) t) ∧
        ∀ q' : Data,
          (∀ u, q'.1 u = (SelectedInverseMap.selInv kh q).1
              (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
          (∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u) →
          (∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) →
          (∀ t, ∀ j ≤ 2, MarkedTopology.supNorm (iteratedDeriv j
            (fun u => frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t
              (Phi t u))) ≤ m t) →
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
  -- the steering equation on the selected strip, slice by slice
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
  -- the regularity of the front data in the pair
  have hle14 : ((1 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (1 : ℕ) ≤ 4)
  have hFC : ContDiff ℝ 1 (uncurry (frontOfPath Γ.X P)) := by simpa using hFc4.of_le hle14
  have hΘC : ContDiff ℝ 1 (uncurry (angleOfPath V A P)) := by simpa using hΘc4.of_le hle14
  have hYC : ContDiff ℝ (1 : ℕ)
      (uncurry (rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf)) :=
    contDiff_one_rearOwn hFC hΘC hδC hsfC
  -- the canonical time derivative of the family of rears is `Ydot`
  have hpt : partialTime (rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf) = Ydot := by
    funext t x
    exact (hasDerivAt_partialTime (hYC.differentiable (by norm_num)) t x).unique (hYt t x)
  ------------------------------------------------------------------
  -- the first half: the bound with the comparison path still free
  ------------------------------------------------------------------
  obtain ⟨hperimp, hperimq, Phi, hPhi0, hbase, hflow, hmain⟩ :=
    SelInvMarkingDefectClosedC2.dist_selInv_le_of_marking_defect_cost_C2
      Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont
      hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
      hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
      hFc4 hΘc4 hsfinv hmark hevd hΘb hkbd hklip
  have hPhiflow : ∀ u t, HasDerivAt (fun r => Phi r u)
      (-frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t (Phi t u)) t := by
    intro u t
    have h := hflow u t
    rwa [hpt] at h
  refine ⟨hperimp, hperimq, Phi, hPhi0, hbase, hPhiflow, ?_⟩
  intro q' hq' hd1 hd2 hsup
  ------------------------------------------------------------------
  -- the second half: the comparison path of the family of rears
  ------------------------------------------------------------------
  -- the closing of the slices, and the differentiability of the rear period
  have hδper : ∀ t, Function.Periodic (δ t) (P t) := fun t => (hslice t).1
  have hδt : ∀ t, Continuous (δ t) := fun t =>
    hδcont.comp (continuous_const.prodMk continuous_id)
  have hΘper : ∀ t s,
      angleOfPath V A P t (s + P t) = angleOfPath V A P t s + 2 * Real.pi :=
    fun t s => angleOfPath_add_period (hVper t) (hAper t) (hVcont t) (hAcont t)
      (hPpos t) (hturn t) s
  have hFper : ∀ t s, frontOfPath Γ.X P t (s + P t) = frontOfPath Γ.X P t s :=
    fun t s => periodic_frontOfPath (hXper t) (hPpos t) s
  have hclose : ∀ t x,
      rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf t
          (x + rearArclength (δ t) (P t))
        = rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf t x :=
    rearOwn_closing hkh0 hkh1 hδt hstrip0 hstrip1 hδper hsfinv hFper hΘper
  have hangper : ∀ t x,
      rearOwnAngle (angleOfPath V A P) δ sf t (x + rearArclength (δ t) (P t))
        = rearOwnAngle (angleOfPath V A P) δ sf t x + 2 * Real.pi := fun t x =>
    RearOwnPathDistFrame.rearOwnAngle_shift (kh := kh) (P := P) hkh0 hkh1 hδt hstrip0
      hstrip1 hδper hsfinv hΘper t x
  have hPd : ∀ t, HasDerivAt P (deriv P t) t := fun t =>
    (hPC4.differentiable (by norm_num) t).hasDerivAt.deriv ▸
      (hPC4.differentiable (by norm_num) t).hasDerivAt
  have hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r))
      ((∫ u in (0 : ℝ)..P t,
          SelectedChangeOfVariable.cosTimeDeriv δ (partialTime δ) t u)
        + deriv P t * Real.cos (δ t (P t))) t := fun t =>
    SelInvDriftRigidity.hasDerivAt_rearPeriod hδC hPd t
  obtain ⟨Psi, hPsi0, hPsibase, hPsiflow, hrmain⟩ :=
    GaugeRearFamilyFundamental.exists_variableSpeed_normalPath_of_rearFamily_fundamental
      (F := frontOfPath Γ.X P)
      (Θ := angleOfPath V A P) (δ := δ) (sf := sf) (K := curvOfPath V A P) (Ydot := Ydot)
      (etaF := etaF) (P := P) (Q := fun t => rearArclength (δ t) (P t))
      (Q' := fun t => (∫ u in (0 : ℝ)..P t,
          SelectedChangeOfVariable.cosTimeDeriv δ (partialTime δ) t u)
        + deriv P t * Real.cos (δ t (P t)))
      (khat := khat) (alphaT := alphaT) (kT := kT)
      (Kx := Kx) (kx := kx) (Rb := Rb) (r := rr) (gS := gS) (Dd := Dd) (d := dd)
      (m := m) (P0 := Pv0)
      Γ hkh0 hkh1 hstrip0 hstrip1 hK hF hΘ hsteer hsfspace hcos hYt hFC hΘC
      hδC hsfC (hYdotC.of_le (by norm_num)) (hangC.of_le (by norm_num))
      hkC1 hQpos hQd hclose hangper hxi0 hjac hPpos hlink hkappa1
      halphaT hkT halphaTc hkTc halphaTS hmixed hKxbd hKxnn hKxm hkXc hRbd hRbm hr
      hgSd hgSbd hDm hmc hm0 hmstop hmge hnumA hnumK
  ------------------------------------------------------------------
  -- the two markings are the flow of the same field from the same start
  ------------------------------------------------------------------
  -- the cost density is bounded, so the field of the flow is globally Lipschitz
  obtain ⟨Mm, hMm⟩ : ∃ M : ℝ, ∀ t, m t ≤ M := by
    obtain ⟨t0, ht0mem, ht0max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Γ.T)).exists_isMaxOn
      (Set.nonempty_Icc.2 Γ.T_pos.le) hmc.continuousOn
    refine ⟨max (m t0) 0, fun t => ?_⟩
    by_cases ht : t ∈ Ioo (0 : ℝ) Γ.T
    · exact le_trans (ht0max (Ioo_subset_Icc_self ht)) (le_max_left _ _)
    · rw [hmstop t ht]; exact le_max_right _ _
  have hxiC1 : ContDiff ℝ 1
      (uncurry (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf))) :=
    RearOwnFrameData.contDiff_frameTangential (hYdotC.of_le (by norm_num))
      (hangC.of_le (by norm_num))
  have hxid : ∀ t x, HasDerivAt
      (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t)
      (partialX (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf)) t x) x :=
    fun t x => hasDerivAt_partialX hxiC1 t x
  have hxibd : ∀ t x,
      |partialX (frameTangential Ydot (rearOwnAngle (angleOfPath V A P) δ sf)) t x|
        ≤ rearKappa1 kh * Mm := by
    intro t x
    refine le_trans (abs_partialX_frameTangential_le_rearKappa1
      (K := curvOfPath V A P) (Q := fun t => rearArclength (δ t) (P t)) (etaF := etaF)
      (P := P) Γ hkh0 hkh1 hstrip0 hstrip1 hF hΘ hsteer hsfspace hcos hYt
      (hYdotC.of_le (by norm_num)) (hangC.of_le (by norm_num)) hQpos hper hjac hPpos
      hlink t x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (rearKappa1_nonneg hkh0 hkh1)
    have hroot : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.2 (by nlinarith)
    have hroot1 : Real.sqrt (1 - kh ^ 2) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
    have : Γ.m t ≤ m t := by
      refine le_trans ?_ (hmge t)
      rw [le_div_iff₀ hroot]
      nlinarith [Γ.m_nonneg t]
    exact this.trans (hMm t)
  have hMmnn : 0 ≤ rearKappa1 kh * Mm :=
    le_trans (abs_nonneg _) (hxibd 0 0)
  have hstart0 : ∀ u, Phi 0 u = Psi 0 u := by
    intro u
    rw [hPhi0 u, hPsi0 u, hperimp]
  have hPP : ∀ t u, Phi t u = Psi t u := fun t u =>
    flow_unique_of_deriv_bound (K := rearKappa1 kh * Mm) hMmnn hxid hxibd hPhiflow hPsiflow
      hstart0 t u
  ------------------------------------------------------------------
  -- the two ends of the second construction
  ------------------------------------------------------------------
  -- the marked selected inverse of the initial slice traces the initial rear
  obtain ⟨-, -, -, hevp⟩ :=
    ev_selInv_eq_rearOwn (X := Γ.X) (V := V) (A := A) (P := P) (δ := δ) (sf := sf)
      hc hkmin hkh1 hp hub hinjR (hPpos 0) (hV 0) (hA 0) (hAcont 0) (hspeed 0)
      (funext Γ.start) (hslice 0).1 (hslice 0).2.1 (hslice 0).2.2 (hsfinv 0)
  obtain ⟨-, -, -, hevq⟩ :=
    ev_selInv_eq_rearOwn (X := Γ.X) (V := V) (A := A) (P := P) (δ := δ) (sf := sf)
      hcq hkminq hkh1 hq hubq hinjRq (hPpos Γ.T) (hV Γ.T) (hA Γ.T) (hAcont Γ.T)
      (hspeed Γ.T) (funext Γ.finish) (hslice Γ.T).1 (hslice Γ.T).2.1 (hslice Γ.T).2.2
      (hsfinv Γ.T)
  have hperimp0 : 0 < perim (SelectedInverseMap.selInv kh p) := by
    rw [hperimp]; exact hQpos 0
  have hstartEnd : ∀ u, rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf 0 (Psi 0 u)
      = (SelectedInverseMap.selInv kh p).1 u := by
    intro u
    rw [← hevp (Psi 0 u), ev, hPsi0 u, ← hperimp]
    congr 1
    field_simp
  have hfinishEnd : ∀ u,
      rearOwn (frontOfPath Γ.X P) (angleOfPath V A P) δ sf Γ.T (Psi Γ.T u) = q'.1 u := by
    intro u
    rw [hq' u, ← hPP Γ.T u, ← hevq (Phi Γ.T u), ev]
  have hsup' : ∀ t, ∀ j ≤ 2, MarkedTopology.supNorm (iteratedDeriv j
      (fun u => frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t (Psi t u)))
        ≤ m t := by
    intro t j hj
    have hfun : (fun u => frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t
        (Psi t u))
        = fun u => frameNormal Ydot (rearOwnAngle (angleOfPath V A P) δ sf) t (Phi t u) :=
      funext fun u => by rw [hPP t u]
    rw [hfun]
    exact hsup t j hj
  obtain ⟨Γ', -, -, -, hcostΓ', hvar⟩ :=
    hrmain (SelectedInverseMap.selInv kh p) q' hstartEnd hfinishEnd hsup'
  ------------------------------------------------------------------
  -- the two halves combined
  ------------------------------------------------------------------
  have h := hmain q' hq' hd1 hd2 Pv0
    (costP1 (rearArclength (δ 0) (P 0)) khat (∫ t in (0 : ℝ)..Γ.T, m t)) khat
    (costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh) (∫ t in (0 : ℝ)..Γ.T, m t))
    (khat * costG1 (rearArclength (δ 0) (P 0)) khat (rearKappa2 kh)
        (∫ t in (0 : ℝ)..Γ.T, m t)
      + rearKappa2 kh * costP1 (rearArclength (δ 0) (P 0)) khat
        (∫ t in (0 : ℝ)..Γ.T, m t) ^ 2) Γ' hvar
  rwa [hcostΓ'] at h

end SelInvRearFamilyFundamentalC2
