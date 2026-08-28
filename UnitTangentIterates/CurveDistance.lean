import Mathlib
import UnitTangentIterates.ClosingArgument

/-!
# From a uniform bound on curves to a Hausdorff bound on their images

The shadowing theorem of *A Noncircular Oval with Convex Unit-Tangent Iterates*
produces the orbit `X_n` as a uniform limit of pullbacks inside shrinking
tubes, and records the conclusion as a bound on the **Hausdorff distance**
`d_H(X_n, Q_n)`, which is then fed into the closing width argument.  This file
supplies the passage between the two: a uniform bound on the distance of two
parametrized curves bounds the Hausdorff distance of their images, and the
image of a closed (periodic, continuous) curve is compact, hence bounded and
nonempty — the hypotheses of the closing argument.

Main results:

* `hausdorffDist_range_le` : `sup_t dist (f t) (g t) ≤ d` implies
  `d_H(range f, range g) ≤ d`;
* `isCompact_range_of_periodic` : the image of a closed curve is compact;
* `not_isCircleOfPerimeter_of_dist_le` : **the closing argument for curves** —
  a closed curve uniformly `d`-close to a model of width at most `C_W`, whose
  perimeter is at least `2H − d`, does not trace a circle, provided
  `C_W + 2d < (2H − d)/π`.
-/

noncomputable section

open Metric Set Function

namespace CurveDistance

/-- **A uniform bound on two parametrizations bounds the Hausdorff distance of
their images.** -/
theorem hausdorffDist_range_le {ι : Type*} [Nonempty ι] {E : Type*} [PseudoMetricSpace E]
    {f g : ι → E} {d : ℝ} (hd : 0 ≤ d) (h : ∀ t, dist (f t) (g t) ≤ d) :
    hausdorffDist (range f) (range g) ≤ d := by
  refine hausdorffDist_le_of_infDist hd ?_ ?_
  · rintro _ ⟨t, rfl⟩
    exact le_trans (infDist_le_dist_of_mem (mem_range_self t)) (h t)
  · rintro _ ⟨t, rfl⟩
    refine le_trans (infDist_le_dist_of_mem (mem_range_self t)) ?_
    rw [dist_comm]
    exact h t

/-- The image of a closed curve is compact. -/
theorem isCompact_range_of_periodic {E : Type*} [TopologicalSpace E] {γ : ℝ → E} {L : ℝ}
    (hγ : Continuous γ) (hper : Periodic γ L) (hL : 0 < L) : IsCompact (range γ) := by
  have himg : γ '' Icc 0 L = range γ := by
    refine Subset.antisymm (image_subset_range _ _) ?_
    rw [← hper.image_Ioc hL 0]
    refine image_mono ?_
    simpa using (Ioc_subset_Icc_self : Ioc (0:ℝ) (0 + L) ⊆ Icc 0 (0 + L))
  rw [← himg]
  exact isCompact_Icc.image hγ

/-- The image of a closed curve is bounded. -/
theorem isBounded_range_of_periodic {E : Type*} [PseudoMetricSpace E] {γ : ℝ → E} {L : ℝ}
    (hγ : Continuous γ) (hper : Periodic γ L) (hL : 0 < L) :
    Bornology.IsBounded (range γ) :=
  (isCompact_range_of_periodic hγ hper hL).isBounded

/-- **The closing argument, for curves, in the paper's Hausdorff form.**  This
is the shape in which Theorem `thm:shadow` delivers its conclusion:
`d_H(X, Q) ≤ d` together with the perimeter estimate.  No pointwise comparison
of the two parametrizations is required. -/
theorem not_isCircleOfPerimeter_of_hausdorffDist_range_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X Q : ℝ → E} {LX LQ : ℝ}
    (hX : Continuous X) (hXper : Periodic X LX) (hLX : 0 < LX)
    (hQ : Continuous Q) (hQper : Periodic Q LQ) (hLQ : 0 < LQ)
    {e : E} (he : ‖e‖ = 1) {d Cw H L : ℝ}
    (hdist : hausdorffDist (range X) (range Q) ≤ d)
    (hQw : Width.width (range Q) e ≤ Cw)
    (hL : 2 * H - d ≤ L)
    (hgap : Cw + 2 * d < (2 * H - d) / Real.pi) :
    ¬ ClosingArgument.IsCircleOfPerimeter (range X) L :=
  ClosingArgument.not_isCircleOfPerimeter_of_hausdorffDist_le
    (range_nonempty X) (range_nonempty Q)
    (isBounded_range_of_periodic hX hXper hLX)
    (isBounded_range_of_periodic hQ hQper hLQ) he hdist hQw hL hgap

/-- **The closing argument, for curves.**  If the closed curve `X` stays within
distance `d` of the closed model curve `Q`, the width of the model in a unit
direction is at most `C_W`, the perimeter `L` of `X` is at least `2H − d`, and
`C_W + 2d < (2H − d)/π`, then the image of `X` is not a circle of perimeter
`L`. -/
theorem not_isCircleOfPerimeter_of_dist_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {X Q : ℝ → E} {LX LQ : ℝ}
    (hX : Continuous X) (hXper : Periodic X LX) (hLX : 0 < LX)
    (hQ : Continuous Q) (hQper : Periodic Q LQ) (hLQ : 0 < LQ)
    {e : E} (he : ‖e‖ = 1) {d Cw H L : ℝ} (hd0 : 0 ≤ d)
    (hdist : ∀ t, dist (X t) (Q t) ≤ d)
    (hQw : Width.width (range Q) e ≤ Cw)
    (hL : 2 * H - d ≤ L)
    (hgap : Cw + 2 * d < (2 * H - d) / Real.pi) :
    ¬ ClosingArgument.IsCircleOfPerimeter (range X) L := by
  refine ClosingArgument.not_isCircleOfPerimeter_of_hausdorffDist_le
    (range_nonempty X) (range_nonempty Q)
    (isBounded_range_of_periodic hX hXper hLX)
    (isBounded_range_of_periodic hQ hQper hLQ) he
    (hausdorffDist_range_le hd0 hdist) hQw hL hgap

end CurveDistance
