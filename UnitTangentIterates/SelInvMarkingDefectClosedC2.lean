import Mathlib
import UnitTangentIterates.SelectedInverseRearOwnTerminalDefectC2
import UnitTangentIterates.MarkedComparisonC2

/-!
# The two marked selected inverses are close in the `C²` metric of the space of
marked curves

`SelInvMarkingDefectClosed.sup_selInv_le_of_marking_defect_cost` closes the
uniform (`C⁰`) comparison of the two marked selected inverses of the ends of a
normal path.  This file is its `C²` counterpart, in the metric of the space of
marked curves itself.

`SelectedInverseRearOwnTerminalDefectC2.exists_marked_rearOwn_pathDist_and_distC2_terminal`
supplies the first half: the curve `q'` that reads the terminal marked selected
inverse `selInv κ̂ q` in the gauge marking of the path is within
`markingC2Bound …` of `selInv κ̂ q`, a quantity that vanishes with `cost Γ`.
`NormalPathC2IncrementVariableSpeed.dist_le_cost_variableSpeed` supplies the
second half: any normal path `Γ'` of slices of variable speed joining
`selInv κ̂ p` to `q'` bounds their marked distance by
`c2ConstVar … · cost Γ'`.  The triangle inequality of the marked metric gives

```
  dist (selInv κ̂ q) (selInv κ̂ p) ≤ markingC2Bound … + c2ConstVar … · cost Γ' ,
```

both terms vanishing with the costs of the two paths.

The path `Γ'` is a hypothesis here: producing it from the gauge flow is the
remaining step of the non-expansiveness argument.

Main result: `dist_selInv_le_of_marking_defect_cost_C2`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelInvMarkingDefectClosedC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  FrontFromPath SelectedInverseRearOwn SelectedInverseRearOwnTerminal
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnTangentialCostC2
  NormalPathC2IncrementVariableSpeed

variable {V A : ℝ → ℝ → ℂ} {δ dn Kn Kdn sf : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The two marked selected inverses of the ends of a normal path are close in
the `C²` metric of the space of marked curves.**

For a normal path that does not move at its marked point, and for any normal
path `Γ'` of slices of variable speed from `selInv κ̂ p` to the curve `q'` that
reads `selInv κ̂ q` in the gauge marking, the two marked selected inverses are
at marked distance at most `markingC2Bound … + c2ConstVar … · cost Γ'`, both
terms vanishing with the costs of the two paths. -/
theorem dist_selInv_le_of_marking_defect_cost_C2 {p q : Data} (Γ : NormalPath p q)
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
    (hklip : ∀ s t, |kb' s - kb' t| ≤ kL * |s - t|) :
    perim (SelectedInverseMap.selInv kh p) = rearArclength (δ 0) (P 0) ∧
      perim (SelectedInverseMap.selInv kh q) = rearArclength (δ Γ.T) (P Γ.T) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
        (∀ t, Phi t 0 = 0) ∧
        (∀ u t, HasDerivAt (fun r => Phi r u)
          (-frameTangential (partialTime (rearOwn (frontOfPath Γ.X P)
              (angleOfPath V A P) δ sf))
            (rearOwnAngle (angleOfPath V A P) δ sf) t (Phi t u)) t) ∧
        ∀ q' : Data,
          (∀ u, q'.1 u = (SelectedInverseMap.selInv kh q).1
              (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
          (∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u) →
          (∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) →
          ∀ (Pv0 Pv1 khat G1 Cg : ℝ) (Γ' : NormalPath (SelectedInverseMap.selInv kh p) q'),
            IsVariableSpeedNormalPath Pv0 Pv1 khat G1 Cg Γ' →
            dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
              ≤ markingC2Bound (2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ)
                  (flowDefectC1Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ))
                  (flowDefectC2Int (rearArclength (δ 0) (P 0)) (kh / (1 - kh ^ 2) * cost Γ)
                    (gaugeGrowth2 kh * cost Γ))
                  (rearArclength (δ Γ.T) (P Γ.T)) kb kL
                + c2ConstVar Pv0 Pv1 khat G1 Cg * cost Γ' := by
  obtain ⟨hperimp, hperimq, EF, hEF0, hEFbd, Phi, hPhi0, hbase, hflow, hdefect, hdistC2,
      hPhi⟩ :=
    SelectedInverseRearOwnTerminalDefectC2.exists_marked_rearOwn_pathDist_and_distC2_terminal
      Γ hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA hAcont
      hspeed hXper hVper hAper hturn hnu hdelta hKeq hsol hstrip hdnper hKnper hKdnper
      hKnbd hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
      hFc4 hΘc4 hsfinv hmark hevd hΘb hkbd hklip
  obtain ⟨dR, -, hmemP, -, -, -⟩ :=
    SelectedInverseMap.selInv_spec hc hkmin hkh1 hp hub hinjR
  refine ⟨hperimp, hperimq, Phi, hPhi0, hbase, hflow, ?_⟩
  intro q' hq' hd1 hd2 Pv0 Pv1 khat G1 Cg Γ' hΓ'
  have h1 := hdistC2 q' hq' hd1 hd2
  have h2 : dist (SelectedInverseMap.selInv kh p) q'
      ≤ c2ConstVar Pv0 Pv1 khat G1 Cg * cost Γ' :=
    dist_le_cost_variableSpeed Γ' hmemP.hasDerivAt_curve hd1 hmemP.hasDerivAt_vel hd2 hΓ'
  calc dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p)
      ≤ dist (SelectedInverseMap.selInv kh q) q'
          + dist q' (SelectedInverseMap.selInv kh p) := dist_triangle _ _ _
    _ = dist q' (SelectedInverseMap.selInv kh q)
          + dist (SelectedInverseMap.selInv kh p) q' := by
        rw [dist_comm (SelectedInverseMap.selInv kh q) q',
          dist_comm q' (SelectedInverseMap.selInv kh p)]
    _ ≤ _ := add_le_add h1 h2

end SelInvMarkingDefectClosedC2
