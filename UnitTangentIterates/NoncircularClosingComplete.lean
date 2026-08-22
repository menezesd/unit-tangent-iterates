import Mathlib
import UnitTangentIterates.ClosingArgument
import UnitTangentIterates.WidthUniformProduced

/-!
# Complete noncircularity closing argument

This file unifies the final closing step of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates* (Section 7):

1. **Uniform Transverse Width Bound** (`WidthUniformProduced.lean`):
   ```
     width(Q_H, e_y) ≤ C_W = C_0 + 1      uniformly for all H ≥ H_*
   ```

2. **Closing Contradiction by Width Gap** (`ClosingArgument.lean`):
   For any shadowing curve `X₀` within Hausdorff distance `d = C_sh r_0` of `Q_0`,
   its perimeter is at least `2 H_0 - d`.  Whenever
   ```
     C_W + 2d < (2 H_0 - d) / π
   ```
   `X₀` cannot be a metric circle of that perimeter.
-/

noncomputable section

open Metric Set Width ClosingArgument

namespace NoncircularClosingComplete

/-- **The noncircularity of thin shadowing curves.**  Given a set `X` within
Hausdorff distance `d` of a model curve `Q` whose transverse width is bounded by `Cw`,
and whose perimeter is `L ≥ 2H - d`, `X` is strictly noncircular whenever the
separation `H` satisfies the threshold inequality `H > (π(Cw + 2d) + d) / 2`. -/
theorem not_isCircleOfPerimeter_of_large_separation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X Q : Set E} (hX : X.Nonempty) (hQ : Q.Nonempty)
    (hXb : Bornology.IsBounded X) (hQb : Bornology.IsBounded Q)
    {e : E} (he : ‖e‖ = 1) {d Cw H L : ℝ}
    (hd : hausdorffDist X Q ≤ d) (hQw : width Q e ≤ Cw)
    (hL : 2 * H - d ≤ L)
    (hH_large : Real.pi * (Cw + 2 * d) + d < 2 * H) :
    ¬ IsCircleOfPerimeter X L := by
  have hgap : Cw + 2 * d < (2 * H - d) / Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]
    linarith
  exact not_isCircleOfPerimeter_of_hausdorffDist_le
    hX hQ hXb hQb he hd hQw hL hgap

end NoncircularClosingComplete
