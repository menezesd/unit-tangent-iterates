import Mathlib
import UnitTangentIterates.MarkingFlowDefectC2
import UnitTangentIterates.MarkingDefectCost

/-!
# The `C²` marking defect of a gauge flow along a normal path

`MarkingDefectCost.abs_marking_defect_le_cost` bounds the *position* defect of
the gauge marking of a normal path by `2·L_max·κ·cost Γ`, from the linear growth
`|R(t,x)| ≤ C t·|x|` of the field of the gauge flow with `C t ≤ κ·m t`, `m` the
cost density of the path.  `MarkingFlowDefectC2.lean` bounds the two derivative
defects of a flow marking by the time integrals of bounds for the first two
space derivatives of its field.

This file puts the two together.  If in addition the space derivatives of the
field obey `|∂ₓR(t,x)| ≤ C t ≤ κ·m t` and `|∂²ₓR(t,x)| ≤ C₂ t ≤ κ₂·m t`, then
the curve read in the gauge marking of the final time is at marked distance

```
  dist q' b ≤ markingC2Bound (2 L_max κ · cost Γ)
                (flowDefectC1Int L₀ (κ · cost Γ))
                (flowDefectC2Int L₀ (κ · cost Γ) (κ₂ · cost Γ)) L k_b k_L
```

from the curve `b` itself — a bound depending on the path only through its cost,
and vanishing with it (`MarkingFlowDefectC2.tendsto_flow_marking_bound_zero`).

Main result: `dist_le_of_gauge_flow_cost`.
-/

noncomputable section

open Set Function MeasureTheory
open scoped NNReal

namespace MarkingDefectCostC2

open MarkedSpace PathMetric PathMetric.NormalPath MarkingDeviationC2 MarkingFlowDefectC2

/-- The time integral of a bound for the field, bounded by the cost of the
path. -/
theorem integral_le_mul_cost {p q : Data} (Γ : NormalPath p q) {C : ℝ → ℝ} {kappa : ℝ}
    (hCcont : Continuous C) (hcost : ∀ t, C t ≤ kappa * Γ.m t) :
    (∫ t in (0 : ℝ)..Γ.T, C t) ≤ kappa * cost Γ := by
  have hT : (0 : ℝ) ≤ Γ.T := Γ.T_pos.le
  have hCint : IntervalIntegrable C volume 0 Γ.T := hCcont.intervalIntegrable 0 Γ.T
  have hmint : IntervalIntegrable (fun t => kappa * Γ.m t) volume 0 Γ.T :=
    (continuous_const.mul Γ.cont_m).intervalIntegrable 0 Γ.T
  have hle : (∫ t in (0 : ℝ)..Γ.T, C t) ≤ ∫ t in (0 : ℝ)..Γ.T, kappa * Γ.m t :=
    intervalIntegral.integral_mono_on hT hCint hmint fun t _ => hcost t
  have heq : (∫ t in (0 : ℝ)..Γ.T, kappa * Γ.m t) = kappa * cost Γ := by
    rw [intervalIntegral.integral_const_mul, cost]
  linarith [hle, heq.le, heq.ge]

/-- **The `C²` defect of the gauge marking of a normal path.**  For a gauge flow
whose field vanishes at the base point and whose first two space derivatives are
bounded by multiples of the cost density of the path, the curve read in the
marking of the final time is at marked distance from the curve itself at most an
explicit function of the cost of the path, vanishing with it. -/
theorem dist_le_of_gauge_flow_cost {p q b q' : Data} (Γ : NormalPath p q)
    {R Rx Rxx : ℝ → ℝ → ℝ} {C C2 : ℝ → ℝ} {Phi : ℝ → ℝ → ℝ} {Klip : ℝ≥0}
    {K2 L0 Lmax kappa kappa2 L kb kL cq kminq dltq : ℝ} {Θ k : ℝ → ℝ}
    -- the flow and its field
    (hlip : ∀ t, LipschitzWith Klip (R t)) (hRcont : Continuous (uncurry R))
    (hd : ∀ u t, HasDerivAt (fun s => Phi s u) (R t (Phi t u)) t)
    (hdc : ∀ u, Continuous fun t => R t (Phi t u))
    (hRx : ∀ s x, HasDerivAt (R s) (Rx s x) x) (hRxcont : Continuous (uncurry Rx))
    (hRxx : ∀ s x, HasDerivAt (Rx s) (Rxx s x) x) (hRxxcont : Continuous (uncurry Rxx))
    (hK2 : ∀ s x, |Rxx s x| ≤ K2)
    -- the quantitative bounds, in terms of the cost density
    (hCcont : Continuous C) (hgrow : ∀ t x, |R t x| ≤ C t * |x|) (hCnn : ∀ t, 0 ≤ C t)
    (hRxbd : ∀ s x, |Rx s x| ≤ C s)
    (hC2cont : Continuous C2) (hRxxbd : ∀ s x, |Rxx s x| ≤ C2 s)
    (hcost : ∀ t, C t ≤ kappa * Γ.m t) (hcost2 : ∀ t, C2 t ≤ kappa2 * Γ.m t)
    -- the marking
    (h0 : ∀ u, Phi 0 u = L0 * u) (hL0 : 0 < L0) (hbase : ∀ t, Phi t 0 = 0)
    (hper : ∀ t u, Phi t (u + 1) = Phi t u + Phi t 1) (hLmax : ∀ t, Phi t 1 ≤ Lmax)
    (hPhiT : Phi Γ.T 1 = L)
    -- the curve that is read in the marking
    (hcq : 0 < cq) (hb : IsTubeMember cq kminq dltq b) (hLb : perim b = L)
    (hev : ∀ s, HasDerivAt (ev b) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s) (hkb : ∀ s, |k s| ≤ kb)
    (hklip : ∀ s t, |k s - k t| ≤ kL * |s - t|)
    (hq'1 : ∀ u, q'.1 u = ev b (Phi Γ.T u))
    (hq'd : ∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u)
    (hq'v : ∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) :
    dist q' b ≤ markingC2Bound (2 * Lmax * kappa * cost Γ)
      (flowDefectC1Int L0 (kappa * cost Γ))
      (flowDefectC2Int L0 (kappa * cost Γ) (kappa2 * cost Γ)) L kb kL := by
  have hT : (0 : ℝ) ≤ Γ.T := Γ.T_pos.le
  have hC2nn : ∀ t, 0 ≤ C2 t := fun t => le_trans (abs_nonneg _) (hRxxbd t 0)
  have hLpos : 0 < L := hLb ▸ perim_pos hcq hb
  have hkb0 : 0 ≤ kb := le_trans (abs_nonneg _) (hkb 0)
  have hkL0 : 0 ≤ kL := by
    have h0' := hklip 1 0
    simp only [sub_zero, abs_one, mul_one] at h0'
    exact le_trans (abs_nonneg _) h0'
  -- the position defect, from the cost
  have hLmax0 : 0 ≤ Lmax := by
    refine le_trans ?_ (hLmax 0)
    rw [h0 1, mul_one]
    exact hL0.le
  have hdev : ∀ u, |Phi Γ.T u - L * u| ≤ 2 * Lmax * kappa * cost Γ := by
    intro u
    have h := MarkingDefectCost.abs_marking_defect_le_cost (K := Klip) (Lmax := Lmax)
      (L0 := L0) Γ hlip hd hdc hCcont
      (fun t x hx => le_trans (hgrow t x) (mul_le_mul_of_nonneg_left hx (hCnn t)))
      h0 hL0 (fun t _ => by rw [hbase t]; simpa using hLmax0) hper (fun t _ => hLmax t) hcost u
    rwa [hPhiT] at h
  -- the general `C²` bound, with the two time integrals
  have hmain := MarkingFlowDefectC2.dist_le_of_flow_marking_int (h := R) (hx := Rx) (hxx := Rxx)
    (K := Klip) (ell := L0) (Phi := Phi) (K2 := K2) (C := C) (C2 := C2) (Θ := Θ) (k := k)
    (kb := kb) (kL := kL) (e0 := 2 * Lmax * kappa * cost Γ) (q := b) (r := q')
    hlip hRcont hd hL0 h0 hRx hRxcont hRxx hRxxcont hK2 hRxbd hCcont hRxxbd hC2cont hT
    hcq hb hLb hev hΘ hkb hklip hq'1 hq'd hq'v hdev
    (by rw [hbase Γ.T, hPhiT, sub_zero])
  -- the two time integrals are bounded by the cost
  have hC : (∫ t in (0 : ℝ)..Γ.T, C t) ≤ kappa * cost Γ := integral_le_mul_cost Γ hCcont hcost
  have hC2 : (∫ t in (0 : ℝ)..Γ.T, C2 t) ≤ kappa2 * cost Γ :=
    integral_le_mul_cost Γ hC2cont hcost2
  have hCnn' : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..Γ.T, C t :=
    intervalIntegral.integral_nonneg hT fun t _ => hCnn t
  have hC2nn' : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..Γ.T, C2 t :=
    intervalIntegral.integral_nonneg hT fun t _ => hC2nn t
  refine le_trans hmain (markingC2Bound_mono hLpos.le hkb0 hkL0
    (flowDefectC1Int_nonneg hL0.le hCnn') le_rfl
    (flowDefectC1Int_mono hL0.le hC) (flowDefectC2Int_mono hC2nn' hC hC2))

end MarkingDefectCostC2
