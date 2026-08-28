import Mathlib
import UnitTangentIterates.HausdorffWidthStability
import UnitTangentIterates.Width
import UnitTangentIterates.ClosingArgument
import UnitTangentIterates.CurveDistance

/-! # Complex planar Hausdorff-width bridge -/

noncomputable section

open Metric Set

namespace ComplexHausdorffWidthBridge

/-- The real directional projection on the complex plane. -/
def directionProjection (e : ℂ) : ℂ → ℝ := fun z => inner ℝ z e

/-- Projection in a unit complex direction is `1`-Lipschitz. -/
theorem lipschitzWith_directionProjection {e : ℂ} (he : ‖e‖ = 1) :
    LipschitzWith 1 (directionProjection e) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, NNReal.coe_one, one_mul]
  show |(inner ℝ x e : ℝ) - (inner ℝ y e : ℝ)| ≤ dist x y
  rw [← inner_sub_left]
  exact (abs_real_inner_le_norm (x - y) e).trans_eq (by rw [he, mul_one, dist_eq_norm])

/-- Mathlib Hausdorff distance controls complex directional width by the sharp
factor two.  This is the direct planar specialization of the paper's width
stability statement. -/
theorem abs_width_sub_le_hausdorff_complex
    {X Q : Set ℂ} (hX : X.Nonempty) (hQ : Q.Nonempty)
    (hXb : Bornology.IsBounded X) (hQb : Bornology.IsBounded Q)
    {e : ℂ} (he : ‖e‖ = 1) {d : ℝ}
    (hd : hausdorffDist X Q ≤ d) :
    |Width.width X e - Width.width Q e| ≤ 2 * d :=
  Width.abs_width_sub_le hX hQ hXb hQb (le_of_eq he) hd

/-- Range form used for two closed planar parametrized curves. -/
theorem abs_width_range_sub_le_hausdorff
    {X Q : ℝ → ℂ}
    (hXne : (Set.range X).Nonempty) (hQne : (Set.range Q).Nonempty)
    (hXb : Bornology.IsBounded (Set.range X))
    (hQb : Bornology.IsBounded (Set.range Q))
    {e : ℂ} (he : ‖e‖ = 1) {d : ℝ}
    (hd : hausdorffDist (Set.range X) (Set.range Q) ≤ d) :
    |Width.width (Set.range X) e - Width.width (Set.range Q) e| ≤ 2 * d :=
  abs_width_sub_le_hausdorff_complex hXne hQne hXb hQb he hd

/-- The complex specialization feeds the existing closing API without any
additional geometric lemma. -/
theorem not_circle_of_complex_hausdorff_width
    {X Q : Set ℂ} (hX : X.Nonempty) (hQ : Q.Nonempty)
    (hXb : Bornology.IsBounded X) (hQb : Bornology.IsBounded Q)
    {e : ℂ} (he : ‖e‖ = 1) {d Cw H L : ℝ}
    (hd : hausdorffDist X Q ≤ d) (hQw : Width.width Q e ≤ Cw)
    (hL : 2 * H - d ≤ L)
    (hgap : Cw + 2 * d < (2 * H - d) / Real.pi) :
    ¬ ClosingArgument.IsCircleOfPerimeter X L :=
  ClosingArgument.not_isCircleOfPerimeter_of_hausdorffDist_le
    hX hQ hXb hQb he hd hQw hL hgap

/-- Pointwise-close parametrizations give the range-level closing conclusion
through the existing `CurveDistance` adapter. -/
theorem not_circle_of_pointwise_close_ranges
    {X Q : ℝ → ℂ}
    (hXc : Continuous X) (hXper : Function.Periodic X 1)
    (hQc : Continuous Q) (hQper : Function.Periodic Q 1)
    {e : ℂ} (he : ‖e‖ = 1) {d Cw H L : ℝ}
    (hd0 : 0 ≤ d) (hd : ∀ u, dist (X u) (Q u) ≤ d)
    (hQw : Width.width (Set.range Q) e ≤ Cw)
    (hL : 2 * H - d ≤ L)
    (hgap : Cw + 2 * d < (2 * H - d) / Real.pi) :
    ¬ ClosingArgument.IsCircleOfPerimeter (Set.range X) L :=
  CurveDistance.not_isCircleOfPerimeter_of_dist_le
    hXc hXper one_pos hQc hQper one_pos he hd0 hd hQw hL hgap

end ComplexHausdorffWidthBridge
