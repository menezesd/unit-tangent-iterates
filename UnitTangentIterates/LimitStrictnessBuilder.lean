import UnitTangentIterates.LimitStrictnessReduction

/-!
# Building `LimitStrictnessData` from the relative bound

§53 reduced the two substantive fields of `LimitStrictnessData` to facts the
development already tracks.  This file assembles the reduction into a
constructor.

`limitStrictnessData_of_relative` takes, for a marked curve `p`:

* the derivative witnesses for the curve, its tangent angle, and its curvature;
* periodicity of the curvature in the perimeter;
* `0 ≤ k` — the closed tube condition;
* `|k'| ≤ k` — the paper's `eq:relative-y-derivatives` at order one;
* `∫₀^{perim} k = π` — the turning identity;

and produces `LimitStrictnessData p`.  The next-track convexity comes from
`next_nonneg_of_relative`, the nonvanishing from `curvature_nonzero_of_total`.

So the `hstrict` hypothesis of the floor-free closing chain is no longer an
opaque geometric requirement: it asks exactly for the order-one relative bound
and the turning identity, both of which the model curves carry by construction.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real Function MarkedSpace

namespace UnconditionalAssembly

/-- **`LimitStrictnessData` from the order-one relative bound.**  Every field is
either a derivative witness or one of the two reductions of §53: the
next-track convexity from `|k'| ≤ k`, and the nonvanishing from the turning
identity.  Nothing geometric beyond those is needed. -/
def limitStrictnessData_of_relative {p : MarkedSpace.Data} {theta k k' : ℝ → ℝ}
    (hcurve : ∀ s, HasDerivAt (MarkedSpace.ev p)
      (Complex.exp (Complex.I * (theta s : ℂ))) s)
    (hangle : ∀ s, HasDerivAt theta (k s) s)
    (hcurv : ∀ s, HasDerivAt k (k' s) s)
    (hper : Periodic k (MarkedSpace.perim p))
    (hk0 : ∀ s, 0 ≤ k s)
    (hrel : ∀ s, |k' s| ≤ k s)
    (htotal : (∫ r in (0:ℝ)..(MarkedSpace.perim p), k r) = π) :
    LimitStrictnessData p where
  theta := theta
  k := k
  k' := k'
  curve_deriv := hcurve
  angle_deriv := hangle
  curvature_deriv := hcurv
  curvature_periodic := hper
  curvature_nonnegative := hk0
  next_nonnegative := fun s => next_nonneg_of_relative (hk0 s) (hrel s)
  curvature_nonzero := curvature_nonzero_of_total htotal

end UnconditionalAssembly
