import Mathlib
import UnitTangentIterates.MarkingDefectCost
import UnitTangentIterates.GaugeFlowVariablePeriod
import UnitTangentIterates.GaugeBaseFlow

/-!
# The defect of the gauge flow of a bundle of frame data

`MarkingDefectCost.lean` bounds the defect of a gauge marking from the linear
growth of the field of its flow.  This file discharges the whole hypothesis
block of that bound for the **gauge flow of a bundle of frame data** — the flow
`Φ` of the tangential rate `−ξ/v` that the path-metric assembly uses as its
marking (`GaugePathRearFamily.exists_gaugeFlow_of_frameData`).

Each hypothesis comes from a fact already established elsewhere in the project:

* the field is globally Lipschitz in the arclength, with constant `D.rateLip`
  (`UniformFrameBounds.GaugeFrameData.lipschitzWith_gaugeRate`);
* it is quasi-periodic, so the flow started from the rescaled arclength
  translates by the current period, `Φ_t(u+1) = Φ_t(u) + Q t`
  (`GaugeFlowVariablePeriod.flow_translation_var`); in particular
  `Φ_t(1) = Q t` once the base point is fixed;
* the base point is fixed as soon as the tangential component vanishes there
  (`GaugeBaseFlow.gaugeFlow_base_fixed`);
* and then the tangential component grows at most linearly in the arclength, so
  the field of the flow does too.

The conclusion is that the marking at the final time deviates from the affine
marking of the terminal period `Q T` by at most `2 L_max κ · cost Γ`, where
`L_max` bounds the period and `κ` bounds the ratio of the growth coefficient of
the tangential rate to the cost density of the path.

Main results:

* `abs_gaugeRate_le_mul_of_frameData` — the linear growth of the field;
* `flow_one_eq_period` — `Φ_t(1) = Q t`;
* `gauge_marking_defect_le_cost` — the defect bound;
* `restFrameData` and `gauge_marking_defect_le_cost_rest` — the bundle of a
  family at rest, on which the whole hypothesis block is checked to be
  satisfiable.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open scoped NNReal

namespace GaugeMarkingDefectFrame

open UniformFrameBounds GaugeFlowVariablePeriod

/-! ### The linear growth of the field of the gauge flow -/

/-- **The field of the gauge flow of a bundle grows at most linearly.**  If the
tangential component of the bundle vanishes at the base point and its arclength
derivative is bounded by `C t`, and the speed is at least `v₀ > 0`, then
`|−ξ/v (t, x)| ≤ (C t / v₀)|x|`. -/
theorem abs_gaugeRate_le_mul_of_frameData (D : GaugeFrameData) {C : ℝ → ℝ} {v0 : ℝ}
    (hxi0 : ∀ t, D.xi t 0 = 0) (hxi1 : ∀ t x, |D.xi1 t x| ≤ C t)
    (hv0 : 0 < v0) (hv : ∀ t x, v0 ≤ |D.v t x|) (t x : ℝ) :
    |GaugeRate.gaugeRate D.xi D.v t x| ≤ (C t / v0) * |x| :=
  MarkingDefectCost.abs_gaugeRate_le_mul_abs D.hxi hxi0 hxi1 hv0 hv t x

/-! ### The marking reads exactly one period -/

/-- **The gauge marking reads exactly one period.**  Started from the rescaled
arclength and fixing the base point, the flow of the quasi-periodic tangential
rate satisfies `Φ_t(1) = Q t`. -/
theorem flow_one_eq_period (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Q Q' : ℝ → ℝ}
    (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hvper : ∀ t, Function.Periodic (D.v t) (Q t))
    (hxiqp : ∀ t x, D.xi t (x + Q t) = D.xi t x - Q' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u) (hbase : ∀ t, Phi t 0 = 0) (t : ℝ) :
    Phi t 1 = Q t := by
  have h := flow_translation_var (K := Real.toNNReal D.rateLip) D.lipschitzWith_gaugeRate hQd
    (quasiPeriodic_gaugeRate D.hvne hvper hxiqp) hPhid hPhi0 0 t
  rw [zero_add, hbase t, zero_add] at h
  exact h

/-! ### The defect of the gauge marking of the bundle -/

/-- **The defect of the gauge marking of a bundle of frame data, bounded by the
cost of the path.**  The gauge flow of a bundle whose tangential component
vanishes at the base point, whose arclength derivative is bounded by `C t` with
`C t / v₀ ≤ κ · m t`, and whose slices have period at most `L_max`, deviates at
the final time from the affine marking of the terminal period by at most
`2 L_max κ · cost Γ`. -/
theorem gauge_marking_defect_le_cost {p q : Data} (Γ : NormalPath p q) (D : GaugeFrameData)
    {Phi : ℝ → ℝ → ℝ} {Q Q' C : ℝ → ℝ} {v0 Lmax kappa : ℝ}
    (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hvper : ∀ t, Function.Periodic (D.v t) (Q t))
    (hxiqp : ∀ t x, D.xi t (x + Q t) = D.xi t x - Q' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u) (hQ0 : 0 < Q 0)
    (hxi0 : ∀ t, D.xi t 0 = 0) (hxi1 : ∀ t x, |D.xi1 t x| ≤ C t) (hCcont : Continuous C)
    (hv0 : 0 < v0) (hv : ∀ t x, v0 ≤ |D.v t x|)
    (hQmax : ∀ t, Q t ≤ Lmax) (hcost : ∀ t, C t / v0 ≤ kappa * Γ.m t) (u : ℝ) :
    |Phi Γ.T u - Q Γ.T * u| ≤ 2 * Lmax * kappa * cost Γ := by
  -- the base point is fixed
  have hbase : ∀ t, Phi t 0 = 0 :=
    GaugeBaseFlow.gaugeFlow_base_fixed D (fun t => hPhid 0 t) (by simp [hPhi0 0]) hxi0
  -- the marking reads exactly one period
  have hone : ∀ t, Phi t 1 = Q t :=
    fun t => flow_one_eq_period D hQd hvper hxiqp hPhid hPhi0 hbase t
  -- and is therefore quasi-periodic with that period
  have hper : ∀ t x, Phi t (x + 1) = Phi t x + Phi t 1 := by
    intro t x
    rw [hone t]
    exact flow_translation_var (K := Real.toNNReal D.rateLip) D.lipschitzWith_gaugeRate hQd
      (quasiPeriodic_gaugeRate D.hvne hvper hxiqp) hPhid hPhi0 x t
  -- the field of the flow is continuous along each line and grows linearly
  have hPhic : ∀ x, Continuous fun t => Phi t x := by
    intro x
    have hdiff : Differentiable ℝ fun t => Phi t x := fun t => (hPhid x t).differentiableAt
    exact hdiff.continuous
  have hcline : ∀ x, Continuous fun t => GaugeRate.gaugeRate D.xi D.v t (Phi t x) := by
    intro x
    have h1 : Continuous fun t => D.xi t (Phi t x) :=
      D.hxic.comp (continuous_id.prodMk (hPhic x))
    have h2 : Continuous fun t => D.v t (Phi t x) :=
      D.hvc.comp (continuous_id.prodMk (hPhic x))
    exact (h1.div h2 fun t => D.hvne t (Phi t x)).neg
  have hgrow : ∀ t x, |GaugeRate.gaugeRate D.xi D.v t x| ≤ (C t / v0) * |x| :=
    abs_gaugeRate_le_mul_of_frameData D hxi0 hxi1 hv0 hv
  have hCnn : ∀ t, 0 ≤ C t / v0 := fun t =>
    div_nonneg (le_trans (abs_nonneg _) (hxi1 t 0)) hv0.le
  have hLmax0 : 0 ≤ Lmax := le_trans hQ0.le (hQmax 0)
  have hmain := MarkingDefectCost.abs_marking_defect_le_cost (K := Real.toNNReal D.rateLip)
    (C := fun t => C t / v0) (Lmax := Lmax) (kappa := kappa) Γ D.lipschitzWith_gaugeRate
    hPhid hcline (hCcont.div_const v0)
    (fun t x hx => le_trans (hgrow t x) (mul_le_mul_of_nonneg_left hx (hCnn t)))
    hPhi0 hQ0 (fun t _ => by rw [hbase t]; simpa using hLmax0) hper
    (fun t _ => by rw [hone t]; exact hQmax t) hcost u
  rwa [hone Γ.T] at hmain

/-! ### The drifting base point -/

/-- **The gauge marking reads one period up to the drift of its base point.**
Without any hypothesis on the motion of the base point, the flow of the
quasi-periodic tangential rate satisfies `Φ_t(1) = Φ_t(0) + Q t`. -/
theorem flow_one_eq_period_drift (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Q Q' : ℝ → ℝ}
    (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hvper : ∀ t, Function.Periodic (D.v t) (Q t))
    (hxiqp : ∀ t x, D.xi t (x + Q t) = D.xi t x - Q' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u) (t : ℝ) :
    Phi t 1 = Phi t 0 + Q t := by
  have h := flow_translation_var (K := Real.toNNReal D.rateLip) D.lipschitzWith_gaugeRate hQd
    (quasiPeriodic_gaugeRate D.hvne hvper hxiqp) hPhid hPhi0 0 t
  rwa [zero_add] at h

/-- **The field of the gauge flow of a bundle, bounded on a window.**  If the
tangential component of the bundle is bounded by `C t` on `|x| ≤ L_max` and the
speed is at least `v₀ > 0`, then `|−ξ/v| ≤ (C t/(v₀ L_max))·L_max` there. -/
theorem abs_gaugeRate_le_window_of_frameData (D : GaugeFrameData) {C : ℝ → ℝ} {v0 Lmax : ℝ}
    (hxi : ∀ t x, |x| ≤ Lmax → |D.xi t x| ≤ C t)
    (hv0 : 0 < v0) (hv : ∀ t x, v0 ≤ |D.v t x|) (hLmax : 0 < Lmax)
    (t x : ℝ) (hx : |x| ≤ Lmax) :
    |GaugeRate.gaugeRate D.xi D.v t x| ≤ (C t / (v0 * Lmax)) * Lmax := by
  have hvpos : 0 < |D.v t x| := lt_of_lt_of_le hv0 (hv t x)
  have hCnn : 0 ≤ C t := le_trans (abs_nonneg _) (hxi t x hx)
  have heq : (C t / (v0 * Lmax)) * Lmax = C t / v0 := by
    field_simp
  rw [GaugeRate.gaugeRate, abs_neg, abs_div, heq, div_le_div_iff₀ hvpos hv0]
  nlinarith [hxi t x hx, hv t x, abs_nonneg (D.xi t x)]

/-- **The defect of the gauge marking of a bundle whose base point drifts.**  The
gauge flow of a bundle whose tangential component is bounded by `C t` on the
window `|x| ≤ L_max` with `C t/(v₀ L_max) ≤ κ·m t`, whose base point stays in
that window and has drifted by at most `dB` at the final time, deviates at the
final time from the affine marking of the terminal period by at most
`2 L_max κ · cost Γ + dB`. -/
theorem gauge_marking_defect_le_cost_drift {p q : Data} (Γ : NormalPath p q)
    (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Q Q' C : ℝ → ℝ} {v0 Lmax dB kappa : ℝ}
    (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hvper : ∀ t, Function.Periodic (D.v t) (Q t))
    (hxiqp : ∀ t x, D.xi t (x + Q t) = D.xi t x - Q' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q 0 * u) (hQ0 : 0 < Q 0)
    (hbase : ∀ t ∈ Icc (0:ℝ) Γ.T, |Phi t 0| ≤ Lmax) (hdrift : |Phi Γ.T 0| ≤ dB)
    (hxi : ∀ t x, |x| ≤ Lmax → |D.xi t x| ≤ C t) (hCcont : Continuous C)
    (hv0 : 0 < v0) (hv : ∀ t x, v0 ≤ |D.v t x|) (hLmax0 : 0 < Lmax)
    (hone : ∀ t ∈ Icc (0:ℝ) Γ.T, Phi t 1 ≤ Lmax)
    (hcost : ∀ t, C t / (v0 * Lmax) ≤ kappa * Γ.m t) (u : ℝ) :
    |Phi Γ.T u - Q Γ.T * u| ≤ 2 * Lmax * kappa * cost Γ + dB := by
  -- the marking is quasi-periodic with the current period
  have hper : ∀ x, Phi Γ.T (x + 1) = Phi Γ.T x + Q Γ.T := fun x =>
    flow_translation_var (K := Real.toNNReal D.rateLip) D.lipschitzWith_gaugeRate hQd
      (quasiPeriodic_gaugeRate D.hvne hvper hxiqp) hPhid hPhi0 x Γ.T
  -- and reads one period up to the drift of the base point
  have hLT : |Phi Γ.T 1 - Q Γ.T| ≤ dB := by
    rw [flow_one_eq_period_drift D hQd hvper hxiqp hPhid hPhi0 Γ.T]
    simpa using hdrift
  have hPhic : ∀ x, Continuous fun t => Phi t x := by
    intro x
    have hdiff : Differentiable ℝ fun t => Phi t x := fun t => (hPhid x t).differentiableAt
    exact hdiff.continuous
  have hcline : ∀ x, Continuous fun t => GaugeRate.gaugeRate D.xi D.v t (Phi t x) := by
    intro x
    have h1 : Continuous fun t => D.xi t (Phi t x) :=
      D.hxic.comp (continuous_id.prodMk (hPhic x))
    have h2 : Continuous fun t => D.v t (Phi t x) :=
      D.hvc.comp (continuous_id.prodMk (hPhic x))
    exact (h1.div h2 fun t => D.hvne t (Phi t x)).neg
  exact MarkingDefectCost.abs_marking_defect_le_cost_drift
    (K := Real.toNNReal D.rateLip) (C := fun t => C t / (v0 * Lmax)) (Lmax := Lmax)
    (LT := Q Γ.T) (dB := dB) (kappa := kappa) Γ D.lipschitzWith_gaugeRate hPhid hcline
    (hCcont.div_const (v0 * Lmax))
    (fun t x hx => abs_gaugeRate_le_window_of_frameData D hxi hv0 hv hLmax0 t x hx)
    hPhi0 hQ0 hbase hper hLT hone hcost u

/-- **A bundle of frame data at rest**: the tangential component vanishes and
the speed is constantly one, the situation of a family of closed curves that
does not move. -/
def restFrameData : GaugeFrameData where
  xi := fun _ _ => 0
  xi1 := fun _ _ => 0
  xi2 := fun _ _ => 0
  v := fun _ _ => 1
  v1 := fun _ _ => 0
  v2 := fun _ _ => 0
  rateLip := 0
  rateBound2 := 0
  hxi := fun _ x => hasDerivAt_const x 0
  hxi1 := fun _ x => hasDerivAt_const x 0
  hv := fun _ x => hasDerivAt_const x 1
  hv1 := fun _ x => hasDerivAt_const x 0
  hvne := fun _ _ => one_ne_zero
  hxic := continuous_const
  hxi1c := continuous_const
  hxi2c := continuous_const
  hvc := continuous_const
  hv1c := continuous_const
  hv2c := continuous_const
  hrate1 := fun _ _ => by simp [GaugeRate.gaugeRate1]
  hrate2 := fun _ _ => by simp [GaugeRate.gaugeRate2]

/-- **Non-vacuity of the defect bound.**  For the bundle at rest the gauge flow
is the affine marking of the constant period `Q`, every hypothesis of
`gauge_marking_defect_le_cost` holds with `C ≡ 0`, `v₀ = 1`, `L_max = Q` and
`κ = 0`, and the bound reads `0 ≤ 0`. -/
theorem gauge_marking_defect_le_cost_rest {p q : Data} (Γ : NormalPath p q)
    {Q : ℝ} (hQ : 0 < Q) (u : ℝ) :
    |Q * u - Q * u| ≤ 2 * Q * 0 * cost Γ := by
  refine gauge_marking_defect_le_cost (Phi := fun _ x => Q * x) (Q := fun _ => Q)
    (Q' := fun _ => 0) (C := fun _ => 0) (v0 := 1) (Lmax := Q) (kappa := 0) Γ restFrameData
    (fun t => hasDerivAt_const t Q) (fun _ _ => rfl) (fun _ _ => by norm_num [restFrameData])
    (fun x t => ?_) (fun x => rfl) hQ (fun _ => rfl) (fun _ _ => by simp [restFrameData])
    continuous_const one_pos (fun _ _ => by simp [restFrameData]) (fun _ => le_rfl)
    (fun t => by simp) u
  · have hzero : GaugeRate.gaugeRate restFrameData.xi restFrameData.v t (Q * x) = 0 := by
      simp [GaugeRate.gaugeRate, restFrameData]
    rw [hzero]
    exact hasDerivAt_const t (Q * x)

end GaugeMarkingDefectFrame
