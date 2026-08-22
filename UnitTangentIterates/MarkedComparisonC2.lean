import Mathlib
import UnitTangentIterates.MarkingDefectCostC2
import UnitTangentIterates.NormalPathC2IncrementVariableSpeed

/-!
# The `C²` comparison of a curve with the end of a path reaching its marking

This file puts together the two halves of the terminal comparison in the metric
of the space of marked curves.

* `MarkingDefectCostC2.dist_le_of_gauge_flow_cost` bounds the marked distance
  from the curve `b` to the curve `q'` that reads `b` in the gauge marking of
  the final time of a normal path `Γ`, by a function of `cost Γ` alone.
* `NormalPathC2IncrementVariableSpeed.dist_le_cost_variableSpeed` bounds the
  marked distance of the two ends of a normal path `Γ'` whose slices are closed
  curves of variable speed, by a constant times `cost Γ'`.  The point of the
  variable-speed version is exactly that `q'` — a curve read in a marking that
  is normalized but not affine — is *not* carried in a constant-speed parameter
  and so is not a member of the tube, which the constant-speed estimate
  requires of both ends.

The triangle inequality of the marked metric then compares `b` with the initial
curve `a` of `Γ'`:

```
  dist b a ≤ markingC2Bound (2 L_max κ · cost Γ)
                (flowDefectC1Int L₀ (κ·cost Γ))
                (flowDefectC2Int L₀ (κ·cost Γ) (κ₂·cost Γ)) L k_b k_L
             + c2ConstVar P₀ P₁ κ̂ G₁ C_g · cost Γ' .
```

Both terms are proportional to (indeed vanish with) the costs of the two paths,
so this is the `C²` form of the uniform comparison
`MarkingDeviation.norm_sub_le_pathDist_add_marking`, with the defect of the
marking measured rather than assumed away and with the terminal
reparametrization no longer required to be affine.

Main result: `dist_le_of_marking_and_variableSpeed`.
-/

noncomputable section

open Set Function MeasureTheory
open scoped NNReal

namespace MarkedComparisonC2

open MarkedSpace PathMetric PathMetric.NormalPath MarkingDeviationC2 MarkingFlowDefectC2
  MarkingDefectCostC2 NormalPathC2IncrementVariableSpeed

/-- **The `C²` comparison of a curve with the initial curve of a path reaching
the curve read in its gauge marking.**

`b` is a member of the tube, `q'` reads it in the gauge marking of the final
time of the normal path `Γ`, and `Γ'` is a normal path from `a` to `q'` whose
slices are closed curves of variable speed.  Then `b` and `a` are at marked
distance at most the marking defect produced by the cost of `Γ` plus the
constant of the variable-speed increment times the cost of `Γ'`. -/
theorem dist_le_of_marking_and_variableSpeed {p q a b q' : Data} (Γ : NormalPath p q)
    (Γ' : NormalPath a q')
    {R Rx Rxx : ℝ → ℝ → ℝ} {C C2 : ℝ → ℝ} {Phi : ℝ → ℝ → ℝ} {Klip : ℝ≥0}
    {K2 L0 Lmax kappa kappa2 L kb kL cq kminq dltq : ℝ} {Θ k : ℝ → ℝ}
    {P0 P1 khat G1 Cg : ℝ}
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
    (hq'v : ∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u)
    -- the path reaching the curve read in the marking
    (had : ∀ u, HasDerivAt (⇑a.1) (a.2.1 u) u) (hav : ∀ u, HasDerivAt (⇑a.2.1) (a.2.2 u) u)
    (hΓ' : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ') :
    dist b a ≤ markingC2Bound (2 * Lmax * kappa * cost Γ)
        (flowDefectC1Int L0 (kappa * cost Γ))
        (flowDefectC2Int L0 (kappa * cost Γ) (kappa2 * cost Γ)) L kb kL
      + c2ConstVar P0 P1 khat G1 Cg * cost Γ' := by
  have hmark : dist q' b ≤ markingC2Bound (2 * Lmax * kappa * cost Γ)
      (flowDefectC1Int L0 (kappa * cost Γ))
      (flowDefectC2Int L0 (kappa * cost Γ) (kappa2 * cost Γ)) L kb kL :=
    MarkingDefectCostC2.dist_le_of_gauge_flow_cost Γ hlip hRcont hd hdc hRx hRxcont hRxx
      hRxxcont hK2 hCcont hgrow hCnn hRxbd hC2cont hRxxbd hcost hcost2 h0 hL0 hbase hper
      hLmax hPhiT hcq hb hLb hev hΘ hkb hklip hq'1 hq'd hq'v
  have hpath : dist a q' ≤ c2ConstVar P0 P1 khat G1 Cg * cost Γ' :=
    dist_le_cost_variableSpeed Γ' had hq'd hav hq'v hΓ'
  calc dist b a ≤ dist b q' + dist q' a := dist_triangle b q' a
    _ = dist q' b + dist a q' := by rw [dist_comm b q', dist_comm q' a]
    _ ≤ _ := add_le_add hmark hpath

end MarkedComparisonC2
