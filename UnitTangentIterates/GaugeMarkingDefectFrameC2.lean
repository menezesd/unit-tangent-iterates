import Mathlib
import UnitTangentIterates.MarkingDefectCostC2
import UnitTangentIterates.GaugeMarkingDefectFrame

/-!
# The `C²` defect of the gauge marking of a bundle of frame data

`GaugeMarkingDefectFrame.gauge_marking_defect_le_cost` bounds the **position**
defect of the gauge marking of a bundle of frame data by `2 L_max κ · cost Γ`.
`MarkingDefectCostC2.dist_le_of_gauge_flow_cost` upgrades a position defect to a
bound in the metric of the space of marked curves, but asks for the flow
equation of the marking together with bounds for the first two space derivatives
of its field.

This file discharges that whole hypothesis block for the gauge flow of a bundle
of frame data — the flow of the tangential rate `−ξ/v` that the path-metric
assembly uses as its marking.  Everything comes from the bundle:

* the field is jointly continuous, globally Lipschitz and twice differentiable
  in the arclength, with jointly continuous derivatives (`GaugeRate.lean`);
* its second space derivative is bounded by `D.rateBound2`;
* it vanishes at the base point as soon as the tangential component does, so a
  bound `C t` for its first space derivative makes it grow linearly,
  `|R(t,x)| ≤ C t · |x|`;
* the flow translates by the current period and fixes the base point
  (`GaugeMarkingDefectFrame.lean`).

The conclusion is that a member `b` of the tube of perimeter `Q T`, read in the
gauge marking of the final time, is at marked distance

```
  markingC2Bound (2 L_max κ · cost Γ) (flowDefectC1Int (Q 0) (κ · cost Γ))
    (flowDefectC2Int (Q 0) (κ · cost Γ) (κ₂ · cost Γ)) L k_b k_L
```

from `b` itself — a bound depending on the path only through its cost, and
vanishing with it.

Main result: `dist_le_of_frameData_cost`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open scoped NNReal

namespace GaugeMarkingDefectFrameC2

open UniformFrameBounds GaugeFlowVariablePeriod MarkingDeviationC2 MarkingFlowDefectC2

/-- **The field of the gauge flow of a bundle vanishes at the base point** as
soon as the tangential component does. -/
theorem gaugeRate_base_eq_zero (D : GaugeFrameData) (hxi0 : ∀ t, D.xi t 0 = 0) (t : ℝ) :
    GaugeRate.gaugeRate D.xi D.v t 0 = 0 := by
  rw [GaugeRate.gaugeRate, hxi0 t, zero_div, neg_zero]

/-- **The field of the gauge flow of a bundle grows at most linearly**, from a
bound for its own space derivative (no bound for the tangential component is
needed). -/
theorem abs_gaugeRate_le_mul_of_rate (D : GaugeFrameData) {C : ℝ → ℝ}
    (hxi0 : ∀ t, D.xi t 0 = 0)
    (hC : ∀ t x, |GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1 t x| ≤ C t) (t x : ℝ) :
    |GaugeRate.gaugeRate D.xi D.v t x| ≤ C t * |x| :=
  MarkingDefectCost.abs_le_mul_abs_of_deriv_bound
    (fun y => GaugeRate.hasDerivAt_gaugeRate D.hxi D.hv D.hvne t y) (hC t)
    (gaugeRate_base_eq_zero D hxi0 t) x

/-- **The `C²` defect of the gauge marking of a bundle of frame data, bounded by
the cost of the path.**

The gauge flow `Φ` of a bundle whose tangential component vanishes at the base
point, whose slices have period `Q t ≤ L_max`, and the two space derivatives of
whose tangential rate are bounded by `C t ≤ κ·m t` and `C₂ t ≤ κ₂·m t` against
the cost density of the path, reads a member `b` of the tube of perimeter
`L = Q T` as a marked curve `q'` at distance at most

`markingC2Bound (2 L_max κ · cost Γ) (flowDefectC1Int (Q 0) (κ·cost Γ))
  (flowDefectC2Int (Q 0) (κ·cost Γ) (κ₂·cost Γ)) L k_b k_L`

from `b` in the metric of the space of marked curves. -/
theorem dist_le_of_frameData_cost {p q b q' : Data} (Γ : NormalPath p q) (D : GaugeFrameData)
    {Phi : ℝ → ℝ → ℝ} {Q Q' C C2 : ℝ → ℝ}
    {Lmax kappa kappa2 L kb kL cq kminq dltq : ℝ} {Θ k : ℝ → ℝ}
    -- the bundle and its flow
    (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hvper : ∀ t, Function.Periodic (D.v t) (Q t))
    (hxiqp : ∀ t x, D.xi t (x + Q t) = D.xi t x - Q' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u) (hQ0 : 0 < Q 0) (hxi0 : ∀ t, D.xi t 0 = 0)
    -- the quantitative bounds, against the cost density
    (hC : ∀ t x, |GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1 t x| ≤ C t) (hCcont : Continuous C)
    (hC2 : ∀ t x, |GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2 t x| ≤ C2 t)
    (hC2cont : Continuous C2)
    (hQmax : ∀ t, Q t ≤ Lmax)
    (hcost : ∀ t, C t ≤ kappa * Γ.m t) (hcost2 : ∀ t, C2 t ≤ kappa2 * Γ.m t)
    -- the curve that is read in the marking
    (hQT : Q Γ.T = L)
    (hcq : 0 < cq) (hb : IsTubeMember cq kminq dltq b) (hLb : perim b = L)
    (hev : ∀ s, HasDerivAt (ev b) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s) (hkb : ∀ s, |k s| ≤ kb)
    (hklip : ∀ s t, |k s - k t| ≤ kL * |s - t|)
    (hq'1 : ∀ u, q'.1 u = ev b (Phi Γ.T u))
    (hq'd : ∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u)
    (hq'v : ∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) :
    dist q' b ≤ markingC2Bound (2 * Lmax * kappa * cost Γ)
      (flowDefectC1Int (Q 0) (kappa * cost Γ))
      (flowDefectC2Int (Q 0) (kappa * cost Γ) (kappa2 * cost Γ)) L kb kL := by
  -- the base point is fixed and the marking reads exactly one period
  have hbase : ∀ t, Phi t 0 = 0 :=
    GaugeBaseFlow.gaugeFlow_base_fixed D (fun t => hPhid 0 t) (by simp [hPhi0 0]) hxi0
  have hone : ∀ t, Phi t 1 = Q t :=
    fun t => GaugeMarkingDefectFrame.flow_one_eq_period D hQd hvper hxiqp hPhid hPhi0 hbase t
  have hper : ∀ t x, Phi t (x + 1) = Phi t x + Phi t 1 := by
    intro t x
    rw [hone t]
    exact flow_translation_var (K := Real.toNNReal D.rateLip) D.lipschitzWith_gaugeRate hQd
      (quasiPeriodic_gaugeRate D.hvne hvper hxiqp) hPhid hPhi0 x t
  -- the flow line is continuous, hence so is the field along it
  have hPhic : ∀ x, Continuous fun t => Phi t x := by
    intro x
    have hdiff : Differentiable ℝ fun t => Phi t x := fun t => (hPhid x t).differentiableAt
    exact hdiff.continuous
  have hdc : ∀ x, Continuous fun t => GaugeRate.gaugeRate D.xi D.v t (Phi t x) := by
    intro x
    have h1 : Continuous fun t => D.xi t (Phi t x) :=
      D.hxic.comp (continuous_id.prodMk (hPhic x))
    have h2 : Continuous fun t => D.v t (Phi t x) :=
      D.hvc.comp (continuous_id.prodMk (hPhic x))
    exact (h1.div h2 fun t => D.hvne t (Phi t x)).neg
  -- the linear growth of the field
  have hgrow : ∀ t x, |GaugeRate.gaugeRate D.xi D.v t x| ≤ C t * |x| :=
    abs_gaugeRate_le_mul_of_rate D hxi0 hC
  have hCnn : ∀ t, 0 ≤ C t := fun t => le_trans (abs_nonneg _) (hC t 0)
  exact MarkingDefectCostC2.dist_le_of_gauge_flow_cost
    (R := GaugeRate.gaugeRate D.xi D.v)
    (Rx := GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
    (Rxx := GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2)
    (Klip := Real.toNNReal D.rateLip) (K2 := D.rateBound2) (L0 := Q 0) Γ
    D.lipschitzWith_gaugeRate
    (GaugeRate.continuous_gaugeRate D.hxic D.hvc D.hvne) hPhid hdc
    (GaugeRate.hasDerivAt_gaugeRate D.hxi D.hv D.hvne)
    (GaugeRate.continuous_gaugeRate1 D.hxic D.hxi1c D.hvc D.hv1c D.hvne)
    (GaugeRate.hasDerivAt_gaugeRate1 D.hxi D.hxi1 D.hv D.hv1 D.hvne)
    (GaugeRate.continuous_gaugeRate2 D.hxic D.hxi1c D.hxi2c D.hvc D.hv1c D.hv2c D.hvne)
    D.hrate2 hCcont hgrow hCnn hC hC2cont hC2 hcost hcost2 hPhi0 hQ0 hbase hper
    (fun t => by rw [hone t]; exact hQmax t) (by rw [hone Γ.T, hQT])
    hcq hb hLb hev hΘ hkb hklip hq'1 hq'd hq'v

/-- **Non-vacuity of the `C²` defect bound of a bundle.**  For the bundle at rest
of `GaugeMarkingDefectFrame.restFrameData` the gauge flow is the affine marking
of the constant period, the two rate bounds hold with `C = C₂ = 0`, and the
conclusion is the bound with all three defects equal to zero — that is, the
curve read in the marking is the curve itself. -/
theorem dist_le_of_frameData_cost_rest {p q b q' : Data} (Γ : NormalPath p q)
    {L kb kL cq kminq dltq : ℝ} {Θ k : ℝ → ℝ}
    (hL : 0 < L)
    (hcq : 0 < cq) (hb : IsTubeMember cq kminq dltq b) (hLb : perim b = L)
    (hev : ∀ s, HasDerivAt (ev b) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s) (hkb : ∀ s, |k s| ≤ kb)
    (hklip : ∀ s t, |k s - k t| ≤ kL * |s - t|)
    (hq'1 : ∀ u, q'.1 u = ev b (L * u))
    (hq'd : ∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u)
    (hq'v : ∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) :
    dist q' b ≤ markingC2Bound (2 * L * 0 * cost Γ) (flowDefectC1Int L (0 * cost Γ))
      (flowDefectC2Int L (0 * cost Γ) (0 * cost Γ)) L kb kL := by
  have hzero : ∀ t x : ℝ,
      GaugeRate.gaugeRate GaugeMarkingDefectFrame.restFrameData.xi
        GaugeMarkingDefectFrame.restFrameData.v t x = 0 := by
    intro t x
    simp [GaugeRate.gaugeRate, GaugeMarkingDefectFrame.restFrameData]
  refine dist_le_of_frameData_cost (Phi := fun _ x => L * x) (Q := fun _ => L)
    (Q' := fun _ => 0) (C := fun _ => 0) (C2 := fun _ => 0) (Lmax := L) (kappa := 0)
    (kappa2 := 0) Γ GaugeMarkingDefectFrame.restFrameData
    (fun t => hasDerivAt_const t L) (fun _ _ => rfl)
    (fun _ _ => by norm_num [GaugeMarkingDefectFrame.restFrameData])
    (fun x t => ?_) (fun x => rfl) hL
    (fun _ => rfl) (fun t x => by
      simp [GaugeRate.gaugeRate1, GaugeMarkingDefectFrame.restFrameData])
    continuous_const
    (fun t x => by simp [GaugeRate.gaugeRate2, GaugeMarkingDefectFrame.restFrameData])
    continuous_const (fun _ => le_rfl) (fun t => by simp) (fun t => by simp) rfl
    hcq hb hLb hev hΘ hkb hklip hq'1 hq'd hq'v
  · rw [hzero t (L * x)]
    exact hasDerivAt_const t (L * x)

end GaugeMarkingDefectFrameC2
