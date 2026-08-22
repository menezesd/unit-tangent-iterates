import Mathlib
import UnitTangentIterates.GaugePathRearFamilyDefect
import UnitTangentIterates.GaugeMarkingDefectFrameC2

/-!
# The path-distance bound and the `C²` defect of its gauge marking, together

`GaugePathRearFamilyDefect.pathDist_and_defect_le_of_rear_family` exposes the
gauge marking `Φ` of the family of rear tracks together with the *position*
defect `|Φ_T(u) − Q(T)·u| ≤ 2 L_max κ · cost Γ`.  That is a `C⁰` statement, and
the metric of the space of marked curves is a `C²` one: comparing the terminal
curve of the path-distance bound with the marked selected inverse itself needs
the deviation of `Φ_T` from the affine marking in position, in the first and in
the second derivative.

This file states the two together, for the same `Φ`.  Besides the hypotheses of
the `C⁰` form it asks only for a bound `C₂ t ≤ κ₂ · m t` for the second
arclength derivative of the tangential component — the second space derivative
of the field of the gauge flow, the first being already bounded by `C t ≤ κ·m t`
there — and for the terminal curve to be a member of the tube tracing
`Y(T, ·)` in its arclength.  The conclusion adds to the `C⁰` one that the curve
read in the marking is at marked distance

```
  markingC2Bound (2 L_max κ · cost Γ) (flowDefectC1Int (Q 0) (κ · cost Γ))
    (flowDefectC2Int (Q 0) (κ · cost Γ) (κ₂ · cost Γ)) (Q T) k_b k_L
```

from that curve, a quantity depending on the path only through its cost and
vanishing with it.

Main result: `pathDist_and_distC2_le_of_rear_family`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearTrack ArclengthInverse

namespace GaugePathRearFamilyDefectC2

open UniformFrameBounds GaugeNormalPath JacobiArclengthUniform PathMetricJacobi
  GaugeGeometryPathVariable GaugePathDistVariable GaugeGeometryPathFront GaugePathRearFamily
  MarkingDeviationC2 MarkingFlowDefectC2

/-- **The path pseudodistance of the selected rears, together with the `C²`
defect of the gauge marking in which it is read.**

Under the hypotheses of
`GaugePathRearFamilyDefect.pathDist_and_defect_le_of_rear_family`, with the
second arclength derivative of the tangential component bounded by
`C₂ t ≤ κ₂ · m t` and with a member `b` of the tube tracing the terminal slice
in its arclength, the gauge marking `Φ` fixes the base point, reads exactly one
period, deviates from the affine marking of the terminal period by at most
`2 L_max κ · cost Γ` in position, reads `b` as a marked curve at distance at
most `markingC2Bound …` from `b` itself, and the path pseudodistance from the
initial slice to the terminal slice read in `Φ` is at most
`gaugeJacobiConst … · cost Γ`. -/
theorem pathDist_and_distC2_le_of_rear_family {p q : Data} (Γ : NormalPath p q) (p' b : Data)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {delta K etaF etaFs etaR sf : ℝ → ℝ → ℝ}
    {Y tauY : ℝ → ℝ → ℂ}
    (D : GaugeFrameData) {Qf Qf' : ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    -- the steering equation on the selected strip
    (hsteer : ∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    -- the front normal velocity
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    -- the change of variable and the inverse Jacobi ODE
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hetaR : ∀ t x, HasDerivAt (etaR t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x)
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, etaR t = fun _ => 0)
    -- the rear period
    (hQdef : ∀ t, Qf t = rearArclength (delta t) (P t))
    (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    -- the family of rear tracks, in its own arclength
    (hv1 : ∀ t x, D.v t x = 1)
    (hY : ContDiff ℝ (1 : ℕ) (uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((D.xi t x : ℂ) * tauY t x + (etaR t x : ℂ) * (Complex.I * tauY t x)) t)
    (htaunorm : ∀ t x, ‖tauY t x‖ = 1)
    (hclose : ∀ t x, Y t (x + Qf t) = Y t x)
    (hstart : ∀ u, p'.1 u = Y 0 (Qf 0 * u))
    -- the gauge normalization and the growth of the tangential component
    (hxi0 : ∀ t, D.xi t 0 = 0) {C C2 : ℝ → ℝ} {Lmax kappa kappa2 : ℝ}
    (hxi1bd : ∀ t x, |D.xi1 t x| ≤ C t) (hCcont : Continuous C)
    (hxi2bd : ∀ t x, |D.xi2 t x| ≤ C2 t) (hC2cont : Continuous C2)
    (hQmax : ∀ t, Qf t ≤ Lmax) (hcost : ∀ t, C t ≤ kappa * Γ.m t)
    (hcost2 : ∀ t, C2 t ≤ kappa2 * Γ.m t)
    -- the terminal curve, a member of the tube tracing the terminal slice
    {cq kminq dltq kb kL : ℝ} {Θ k : ℝ → ℝ}
    (hcq : 0 < cq) (hb : IsTubeMember cq kminq dltq b) (hperimb : perim b = Qf Γ.T)
    (hevb : ∀ x, ev b x = Y Γ.T x)
    (hev : ∀ s, HasDerivAt (ev b) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s) (hkb : ∀ s, |k s| ≤ kb)
    (hklip : ∀ s t, |k s - k t| ≤ kL * |s - t|) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Qf 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ t, Phi t 1 = Qf t) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u) (-D.xi t (Phi t u)) t) ∧
      (∀ u, |Phi Γ.T u - Qf Γ.T * u| ≤ 2 * Lmax * kappa * cost Γ) ∧
      (∀ q' : Data, (∀ u, q'.1 u = Y Γ.T (Phi Γ.T u)) →
        (∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u) → (∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) →
        dist q' b ≤ markingC2Bound (2 * Lmax * kappa * cost Γ)
          (flowDefectC1Int (Qf 0) (kappa * cost Γ))
          (flowDefectC2Int (Qf 0) (kappa * cost Γ) (kappa2 * cost Γ)) (Qf Γ.T) kb kL) ∧
      ∀ q' : Data, (∀ u, q'.1 u = Y Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤
          gaugeJacobiConst P0 P1 kh D.rateLip D.rateBound2 Γ.T (Qf 0) * cost Γ := by
  -- the speed of the bundle is constant, so its derivatives vanish
  have hv1zero : ∀ t x, D.v1 t x = 0 := by
    intro t x
    have h1 : HasDerivAt (D.v t) (D.v1 t x) x := D.hv t x
    have h2 : HasDerivAt (D.v t) 0 x := by
      have : D.v t = fun _ => (1 : ℝ) := funext fun y => hv1 t y
      rw [this]
      exact hasDerivAt_const x 1
    exact h1.unique h2
  have hv2zero : ∀ t x, D.v2 t x = 0 := by
    intro t x
    have h1 : HasDerivAt (D.v1 t) (D.v2 t x) x := D.hv1 t x
    have h2 : HasDerivAt (D.v1 t) 0 x := by
      have : D.v1 t = fun _ => (0 : ℝ) := funext fun y => hv1zero t y
      rw [this]
      exact hasDerivAt_const x 0
    exact h1.unique h2
  -- hence the two space derivatives of the field are those of the tangential component
  have hrate1 : ∀ t x, GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1 t x = -D.xi1 t x := by
    intro t x
    rw [GaugeRate.gaugeRate1, hv1 t x, hv1zero t x]
    ring
  have hrate2 : ∀ t x,
      GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2 t x = -D.xi2 t x := by
    intro t x
    rw [GaugeRate.gaugeRate2, hv1 t x, hv1zero t x, hv2zero t x]
    ring
  have hC1 : ∀ t x, |GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1 t x| ≤ C t := by
    intro t x
    rw [hrate1 t x, abs_neg]
    exact hxi1bd t x
  have hC2 : ∀ t x, |GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2 t x| ≤ C2 t := by
    intro t x
    rw [hrate2 t x, abs_neg]
    exact hxi2bd t x
  -- the tangent never vanishes
  have htau0 : ∀ t x, tauY t x ≠ 0 := by
    intro t x h
    have hn := htaunorm t x
    rw [h] at hn
    simp at hn
  -- the tangent is periodic with the rear period, by differentiating the closing relation
  have htauper : ∀ t, Function.Periodic (tauY t) (Qf t) := by
    intro t x
    have hshift : HasDerivAt (fun y => Y t (y + Qf t)) (tauY t (x + Qf t)) x :=
      HasDerivAt.comp_add_const x (Qf t) (hYx t (x + Qf t))
    have hfun : (fun y => Y t (y + Qf t)) = Y t := funext fun y => hclose t y
    rw [hfun] at hshift
    exact hshift.unique (hYx t x)
  -- the normal velocity is periodic with the rear period, by the closing relations
  have hetaRper : ∀ t, Function.Periodic (etaR t) (Qf t) := fun t x =>
    (GaugeClosingRelations.closing_relations hY hYx hYt htau0 htauper hclose hQd t x).2
  -- the rear period at time zero is positive
  have hQ0 : 0 < Qf 0 := by
    rw [hQdef 0]
    exact SelectedPathData.rearPeriod_pos (lt_of_lt_of_le hP0 (hPl 0)) hkh0 hkh1
      (SelectedPathData.continuous_of_steering (hsteer 0)) (hstrip0 0) (hstrip1 0)
  -- the gauge flow
  obtain ⟨Phi, hPhi0, hPhid⟩ := exists_gaugeFlow_of_frameData D hQ0
  have hPhic : ∀ u, Continuous fun t => Phi t u := by
    intro u
    have hd : Differentiable ℝ fun t => Phi t u := fun t => (hPhid u t).differentiableAt
    exact hd.continuous
  -- the moving marked curve and its unit normal
  set XR : ℝ → ℝ → ℂ := fun t u => Y t (Phi t u) with hXRdef
  set nuR : ℝ → ℝ → ℂ := fun t u => Complex.I * tauY t (Phi t u) with hnuRdef
  have hnu : ∀ t u, ‖nuR t u‖ = 1 := by
    intro t u
    rw [hnuRdef]
    simp [htaunorm]
  -- the velocity of the moving marked curve is normal
  have hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t (Phi t u) : ℂ) * nuR t u) t := by
    intro t u
    have h := hasDerivAt_along_curve (Y := Y) (tauY := tauY)
      (Yt := fun t x => (D.xi t x : ℂ) * tauY t x + (etaR t x : ℂ) * (Complex.I * tauY t x))
      hY hYx hYt (hPhid u t)
    refine h.congr_deriv ?_
    rw [hnuRdef, GaugeRate.gaugeRate, hv1]
    simp only [div_one, Complex.real_smul, Complex.ofReal_neg]
    ring
  -- and it depends continuously on the time
  have hetaRc : Continuous (uncurry etaR) :=
    continuous_normal_component hY hYx hYt htau0
  have htauc : Continuous (uncurry tauY) := continuous_partial_space hY hYx
  have hcont : ∀ u, Continuous fun t => (etaR t (Phi t u) : ℂ) * nuR t u := by
    intro u
    have h1 : Continuous fun t => etaR t (Phi t u) :=
      hetaRc.comp (continuous_id.prodMk (hPhic u))
    have h2 : Continuous fun t => tauY t (Phi t u) :=
      htauc.comp (continuous_id.prodMk (hPhic u))
    rw [hnuRdef]
    exact (Complex.continuous_ofReal.comp h1).mul (continuous_const.mul h2)
  -- the base point is fixed
  have hbase : ∀ t, Phi t 0 = 0 :=
    GaugeBaseFlow.gaugeFlow_base_fixed D (fun r => hPhid 0 r) (by simp [hPhi0 0]) hxi0
  -- the tangential component is quasi-periodic, by the closing relation
  have hxiqp : ∀ t x, D.xi t (x + Qf t) = D.xi t x - Qf' t * D.v t x := by
    intro t x
    have h := (GaugeClosingRelations.closing_relations hY hYx hYt htau0 htauper hclose hQd
      t x).1
    rw [hv1 t x, mul_one]
    exact h
  have hvper : ∀ t, Function.Periodic (D.v t) (Qf t) := by
    intro t x
    rw [hv1 t (x + Qf t), hv1 t x]
  -- so the marking reads exactly one period, and its defect is bounded by the cost
  have hone : ∀ t, Phi t 1 = Qf t :=
    fun t => GaugeMarkingDefectFrame.flow_one_eq_period D hQd hvper hxiqp hPhid hPhi0 hbase t
  have hdefect : ∀ u, |Phi Γ.T u - Qf Γ.T * u| ≤ 2 * Lmax * kappa * cost Γ := fun u =>
    GaugeMarkingDefectFrame.gauge_marking_defect_le_cost Γ D hQd hvper hxiqp hPhid hPhi0 hQ0
      hxi0 hxi1bd hCcont one_pos (fun t x => by rw [hv1 t x]; norm_num) hQmax
      (fun t => by simpa using hcost t) u
  have hPhiflow : ∀ u t, HasDerivAt (fun r => Phi r u) (-D.xi t (Phi t u)) t := by
    intro u t
    refine (hPhid u t).congr_deriv ?_
    rw [GaugeRate.gaugeRate, hv1 t (Phi t u), div_one]
  refine ⟨Phi, fun u => hPhi0 u, hbase, hone, hPhiflow, hdefect, ?_, ?_⟩
  · -- the `C²` defect: the curve read in the marking is close to the curve itself
    intro q' hq' hq'd hq'v
    exact GaugeMarkingDefectFrameC2.dist_le_of_frameData_cost Γ D hQd hvper hxiqp hPhid
      hPhi0 hQ0 hxi0 hC1 hCcont hC2 hC2cont hQmax hcost hcost2 rfl hcq hb hperimb hev hΘ
      hkb hklip (fun u => by rw [hq' u, hevb (Phi Γ.T u)]) hq'd hq'v
  · intro q' hq'
    exact pathDist_le_of_gauge_geometry_front (etaY := etaR) (sf := sf) (etaFs := etaFs)
      (K := K) (XR := XR) (nuR := nuR) (Qf' := Qf') Γ D hP0 hkh0 hkh1 hPl hPu hsteer hstrip0
      hstrip1 hdper hK hKc hetaFd hetaFsc hetaFper hsfinv hetaR hQdef hQd hetaRper hlink hv1
      hY hYx hYt htau0 htauper hclose hPhid hPhi0
      (fun u => by simp only [hXRdef]; rw [hPhi0 u, hstart u])
      (fun u => by simp only [hXRdef]; rw [hq' u]) hderiv hcont hnu hrest

end GaugePathRearFamilyDefectC2
