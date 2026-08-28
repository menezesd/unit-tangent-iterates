import Mathlib
import UnitTangentIterates.MarkedSpace
import UnitTangentIterates.CurveDistance

/-!
# The marked metric dominates the Hausdorff distance of arclength images

Theorem `thm:shadow` of *A Noncircular Oval with Convex Unit-Tangent Iterates*
records the conclusion of the shadowing construction as a bound on the
**Hausdorff distance** of images,
`d_H(X_n, Q_n) + |Per(X_n) - 2L_n| ≤ C r_n`, and that is exactly the form the
closing width argument of Section~7 consumes.

The marked metric of `MarkedSpace` compares two curves in one *common periodic
parameter*, whereas `MarkedSpace.ev` reparametrizes each curve by *its own*
arclength.  Those two parametrizations differ when the perimeters differ, so a
marked-distance bound does **not** give a pointwise bound on the arclength
parametrizations.  It does give the Hausdorff bound, because reparametrizing a
curve does not move its image; that is the content of this file.
-/

open Metric Set

namespace MarkedSpace

/-- **The marked distance dominates the Hausdorff distance of the arclength
images.**  This is the paper's `d_H(X, Q) ≤ d`, obtained from a bound in the
marked metric without any comparison of the two perimeters. -/
theorem hausdorffDist_range_ev_le {p q : Data}
    (hp : perim p ≠ 0) (hq : perim q ≠ 0) {d : ℝ} (hd : 0 ≤ d)
    (hpq : dist p q ≤ d) :
    hausdorffDist (range (ev p)) (range (ev q)) ≤ d := by
  rw [range_ev_of_perim_ne_zero hp, range_ev_of_perim_ne_zero hq]
  refine CurveDistance.hausdorffDist_range_le hd fun u => ?_
  rw [dist_eq_norm]
  exact (dist_apply_le p q u).trans hpq

/-- Tube form of `hausdorffDist_range_ev_le`. -/
theorem hausdorffDist_range_ev_le_of_tube {c kmin delta : ℝ} (hc : 0 < c)
    {p q : Data} (hp : IsTubeMember c kmin delta p)
    (hq : IsTubeMember c kmin delta q) {d : ℝ} (hd : 0 ≤ d)
    (hpq : dist p q ≤ d) :
    hausdorffDist (range (ev p)) (range (ev q)) ≤ d :=
  hausdorffDist_range_ev_le (ne_of_gt (perim_pos hc hp))
    (ne_of_gt (perim_pos hc hq)) hd hpq

end MarkedSpace
